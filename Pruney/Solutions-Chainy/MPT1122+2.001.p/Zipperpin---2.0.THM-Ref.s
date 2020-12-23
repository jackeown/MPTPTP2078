%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bBkXuNIdWd

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:20 EST 2020

% Result     : Theorem 33.73s
% Output     : Refutation 33.73s
% Verified   : 
% Statistics : Number of formulae       :  237 (12561 expanded)
%              Number of leaves         :   43 (3889 expanded)
%              Depth                    :   28
%              Number of atoms          : 2196 (138023 expanded)
%              Number of equality atoms :  164 (9295 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_11_type,type,(
    sk_B_11: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X65: $i,X67: $i] :
      ( ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X67 ) )
      | ~ ( r1_tarski @ X65 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k9_subset_1 @ X48 @ X46 @ X47 )
        = ( k3_xboole_0 @ X46 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k9_subset_1 @ X38 @ X37 @ X37 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','14'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ( ( k4_xboole_0 @ X13 @ X15 )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X154: $i,X155: $i] :
      ( ~ ( m1_subset_1 @ X154 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X155 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X155 ) @ X154 @ ( k3_subset_1 @ ( u1_struct_0 @ X155 ) @ X154 ) )
        = ( k2_struct_0 @ X155 ) )
      | ~ ( l1_struct_0 @ X155 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('37',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k3_subset_1 @ X41 @ ( k3_subset_1 @ X41 @ X40 ) )
        = X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t28_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k4_subset_1 @ X53 @ X54 @ ( k2_subset_1 @ X53 ) )
        = ( k2_subset_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t28_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('42',plain,(
    ! [X29: $i] :
      ( ( k2_subset_1 @ X29 )
      = X29 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('43',plain,(
    ! [X29: $i] :
      ( ( k2_subset_1 @ X29 )
      = X29 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k4_subset_1 @ X53 @ X54 @ X53 )
        = X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','39','45'])).

thf(t53_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
              & ( ( ( v2_pre_topc @ A )
                  & ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                    = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
               => ( v3_pre_topc @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_pre_topc])).

thf('47',plain,(
    m1_subset_1 @ sk_B_11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('49',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('52',plain,(
    ! [X137: $i] :
      ( ( l1_struct_0 @ X137 )
      | ~ ( l1_pre_topc @ X137 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('56',plain,(
    ! [X154: $i,X155: $i] :
      ( ~ ( m1_subset_1 @ X154 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X155 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X155 ) @ X154 @ ( k3_subset_1 @ ( u1_struct_0 @ X155 ) @ X154 ) )
        = ( k2_struct_0 @ X155 ) )
      | ~ ( l1_struct_0 @ X155 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('57',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k3_subset_1 @ X41 @ ( k3_subset_1 @ X41 @ X40 ) )
        = X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('61',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) )
    = sk_B_11 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k4_subset_1 @ X51 @ X52 @ ( k3_subset_1 @ X51 @ X52 ) )
        = ( k2_subset_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf('64',plain,(
    ! [X29: $i] :
      ( ( k2_subset_1 @ X29 )
      = X29 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('65',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k4_subset_1 @ X51 @ X52 @ ( k3_subset_1 @ X51 @ X52 ) )
        = X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) )
    = sk_B_11 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('68',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_B_11 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('70',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','69'])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('72',plain,(
    ! [X121: $i,X122: $i] :
      ( ~ ( m1_subset_1 @ X121 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X122 ) ) )
      | ~ ( v4_pre_topc @ X121 @ X122 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X122 ) @ ( k2_struct_0 @ X122 ) @ X121 ) @ X122 )
      | ~ ( l1_pre_topc @ X122 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('77',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k4_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75','78'])).

thf('80',plain,
    ( ~ ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','39','45'])).

thf('82',plain,(
    m1_subset_1 @ sk_B_11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('84',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('86',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('89',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','39','45'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( m1_subset_1 @ sk_B_11 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_11 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf(t22_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
            = B ) ) ) )).

thf('98',plain,(
    ! [X156: $i,X157: $i] :
      ( ~ ( m1_subset_1 @ X156 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X157 ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X157 ) @ ( k2_struct_0 @ X157 ) @ ( k7_subset_1 @ ( u1_struct_0 @ X157 ) @ ( k2_struct_0 @ X157 ) @ X156 ) )
        = X156 )
      | ~ ( l1_struct_0 @ X157 ) ) ),
    inference(cnf,[status(esa)],[t22_pre_topc])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('101',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('105',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103','104','105'])).

thf('107',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 )
    = sk_B_11 ),
    inference('sup-',[status(thm)],['96','106'])).

thf('108',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    = sk_B_11 ),
    inference(demod,[status(thm)],['89','90','91','107'])).

thf('109',plain,
    ( ~ ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A )
    | ( v3_pre_topc @ sk_B_11 @ sk_A ) ),
    inference(demod,[status(thm)],['80','108'])).

thf('110',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    | ~ ( v3_pre_topc @ sk_B_11 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ~ ( v3_pre_topc @ sk_B_11 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_11 @ sk_A ) ),
    inference(split,[status(esa)],['110'])).

thf('112',plain,
    ( ( v3_pre_topc @ sk_B_11 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','39','45'])).

thf('116',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('117',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('119',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('121',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('124',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('125',plain,
    ( ( v3_pre_topc @ sk_B_11 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(demod,[status(thm)],['112','113','114','121','122','123','124'])).

thf('126',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('127',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(split,[status(esa)],['110'])).

thf('128',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('130',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('132',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('134',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('135',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 )
       != ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      | ( v3_pre_topc @ sk_B_11 @ sk_A ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference('sup-',[status(thm)],['125','135'])).

thf('137',plain,
    ( ( v3_pre_topc @ sk_B_11 @ sk_A )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    = sk_B_11 ),
    inference(demod,[status(thm)],['89','90','91','107'])).

thf('139',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('140',plain,(
    ! [X121: $i,X122: $i] :
      ( ~ ( m1_subset_1 @ X121 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X122 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X122 ) @ ( k2_struct_0 @ X122 ) @ X121 ) @ X122 )
      | ( v4_pre_topc @ X121 @ X122 )
      | ~ ( l1_pre_topc @ X122 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ~ ( v3_pre_topc @ sk_B_11 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['138','145'])).

thf('147',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','69'])).

thf('148',plain,
    ( ~ ( v3_pre_topc @ sk_B_11 @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference('sup-',[status(thm)],['137','148'])).

thf('150',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

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

thf('151',plain,(
    ! [X165: $i,X166: $i] :
      ( ~ ( m1_subset_1 @ X165 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X166 ) ) )
      | ~ ( v4_pre_topc @ X165 @ X166 )
      | ( ( k2_pre_topc @ X166 @ X165 )
        = X165 )
      | ~ ( l1_pre_topc @ X166 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('152',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('156',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('157',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('158',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference('sup-',[status(thm)],['149','158'])).

thf('160',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('161',plain,
    ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference('simplify_reflect-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( v3_pre_topc @ sk_B_11 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(split,[status(esa)],['110'])).

thf('163',plain,(
    ~ ( v3_pre_topc @ sk_B_11 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v3_pre_topc @ sk_B_11 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['111','163'])).

thf('165',plain,(
    ~ ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A ) ),
    inference(clc,[status(thm)],['109','164'])).

thf('166',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','69'])).

thf('167',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    | ( v2_pre_topc @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['167'])).

thf('169',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('170',plain,(
    ! [X165: $i,X166: $i] :
      ( ~ ( m1_subset_1 @ X165 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X166 ) ) )
      | ~ ( v2_pre_topc @ X166 )
      | ( ( k2_pre_topc @ X166 @ X165 )
       != X165 )
      | ( v4_pre_topc @ X165 @ X166 )
      | ~ ( l1_pre_topc @ X166 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
       != X0 )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
       != X0 )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ! [X0: $i] :
        ( ( ( k2_pre_topc @ sk_A @ X0 )
         != X0 )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['168','173'])).

thf('175',plain,
    ( ( v2_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(split,[status(esa)],['167'])).

thf('176',plain,(
    v2_pre_topc @ sk_A ),
    inference('sat_resolution*',[status(thm)],['161','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
       != X0 )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['174','176'])).

thf('178',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
     != ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference('sup-',[status(thm)],['166','177'])).

thf('179',plain,
    ( ( v3_pre_topc @ sk_B_11 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(split,[status(esa)],['179'])).

thf('181',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('183',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('184',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','61','68'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('186',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('187',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(demod,[status(thm)],['180','181','182','183','184','185','186'])).

thf('188',plain,
    ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference('sat_resolution*',[status(thm)],['161'])).

thf('189',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ),
    inference(simpl_trail,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A )
    | ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 )
     != ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) ) ),
    inference(demod,[status(thm)],['178','189'])).

thf('191',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_11 ) @ sk_A ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    $false ),
    inference(demod,[status(thm)],['165','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bBkXuNIdWd
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:00:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 33.73/33.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 33.73/33.94  % Solved by: fo/fo7.sh
% 33.73/33.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 33.73/33.94  % done 35803 iterations in 33.477s
% 33.73/33.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 33.73/33.94  % SZS output start Refutation
% 33.73/33.94  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 33.73/33.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 33.73/33.94  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 33.73/33.94  thf(sk_B_11_type, type, sk_B_11: $i).
% 33.73/33.94  thf(sk_A_type, type, sk_A: $i).
% 33.73/33.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 33.73/33.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 33.73/33.94  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 33.73/33.94  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 33.73/33.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 33.73/33.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 33.73/33.94  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 33.73/33.94  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 33.73/33.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 33.73/33.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 33.73/33.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 33.73/33.94  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 33.73/33.94  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 33.73/33.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 33.73/33.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 33.73/33.94  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 33.73/33.94  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 33.73/33.94  thf(d10_xboole_0, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 33.73/33.94  thf('0', plain,
% 33.73/33.94      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 33.73/33.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 33.73/33.94  thf('1', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 33.73/33.94      inference('simplify', [status(thm)], ['0'])).
% 33.73/33.94  thf(t3_subset, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 33.73/33.94  thf('2', plain,
% 33.73/33.94      (![X65 : $i, X67 : $i]:
% 33.73/33.94         ((m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X67)) | ~ (r1_tarski @ X65 @ X67))),
% 33.73/33.94      inference('cnf', [status(esa)], [t3_subset])).
% 33.73/33.94  thf('3', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['1', '2'])).
% 33.73/33.94  thf(d5_subset_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 33.73/33.94       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 33.73/33.94  thf('4', plain,
% 33.73/33.94      (![X30 : $i, X31 : $i]:
% 33.73/33.94         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 33.73/33.94          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 33.73/33.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 33.73/33.94  thf('5', plain,
% 33.73/33.94      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['3', '4'])).
% 33.73/33.94  thf(t48_xboole_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 33.73/33.94  thf('6', plain,
% 33.73/33.94      (![X8 : $i, X9 : $i]:
% 33.73/33.94         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 33.73/33.94           = (k3_xboole_0 @ X8 @ X9))),
% 33.73/33.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.73/33.94  thf('7', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         ((k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0))
% 33.73/33.94           = (k3_xboole_0 @ X0 @ X0))),
% 33.73/33.94      inference('sup+', [status(thm)], ['5', '6'])).
% 33.73/33.94  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['1', '2'])).
% 33.73/33.94  thf(redefinition_k9_subset_1, axiom,
% 33.73/33.94    (![A:$i,B:$i,C:$i]:
% 33.73/33.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 33.73/33.94       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 33.73/33.94  thf('9', plain,
% 33.73/33.94      (![X46 : $i, X47 : $i, X48 : $i]:
% 33.73/33.94         (((k9_subset_1 @ X48 @ X46 @ X47) = (k3_xboole_0 @ X46 @ X47))
% 33.73/33.94          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 33.73/33.94      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 33.73/33.94  thf('10', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['8', '9'])).
% 33.73/33.94  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['1', '2'])).
% 33.73/33.94  thf(idempotence_k9_subset_1, axiom,
% 33.73/33.94    (![A:$i,B:$i,C:$i]:
% 33.73/33.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 33.73/33.94       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 33.73/33.94  thf('12', plain,
% 33.73/33.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 33.73/33.94         (((k9_subset_1 @ X38 @ X37 @ X37) = (X37))
% 33.73/33.94          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 33.73/33.94      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 33.73/33.94  thf('13', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['11', '12'])).
% 33.73/33.94  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 33.73/33.94      inference('sup+', [status(thm)], ['10', '13'])).
% 33.73/33.94  thf('15', plain,
% 33.73/33.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 33.73/33.94      inference('demod', [status(thm)], ['7', '14'])).
% 33.73/33.94  thf(t83_xboole_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 33.73/33.94  thf('16', plain,
% 33.73/33.94      (![X13 : $i, X15 : $i]:
% 33.73/33.94         ((r1_xboole_0 @ X13 @ X15) | ((k4_xboole_0 @ X13 @ X15) != (X13)))),
% 33.73/33.94      inference('cnf', [status(esa)], [t83_xboole_1])).
% 33.73/33.94  thf('17', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (((X0) != (X0)) | (r1_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['15', '16'])).
% 33.73/33.94  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0))),
% 33.73/33.94      inference('simplify', [status(thm)], ['17'])).
% 33.73/33.94  thf(d7_xboole_0, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( r1_xboole_0 @ A @ B ) <=>
% 33.73/33.94       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 33.73/33.94  thf('19', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('cnf', [status(esa)], [d7_xboole_0])).
% 33.73/33.94  thf('20', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         ((k3_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (k1_xboole_0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['18', '19'])).
% 33.73/33.94  thf('21', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         ((k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0))
% 33.73/33.94           = (k3_xboole_0 @ X0 @ X0))),
% 33.73/33.94      inference('sup+', [status(thm)], ['5', '6'])).
% 33.73/33.94  thf('22', plain,
% 33.73/33.94      (![X8 : $i, X9 : $i]:
% 33.73/33.94         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 33.73/33.94           = (k3_xboole_0 @ X8 @ X9))),
% 33.73/33.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.73/33.94  thf('23', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 33.73/33.94           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 33.73/33.94      inference('sup+', [status(thm)], ['21', '22'])).
% 33.73/33.94  thf(t47_xboole_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 33.73/33.94  thf('24', plain,
% 33.73/33.94      (![X6 : $i, X7 : $i]:
% 33.73/33.94         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 33.73/33.94           = (k4_xboole_0 @ X6 @ X7))),
% 33.73/33.94      inference('cnf', [status(esa)], [t47_xboole_1])).
% 33.73/33.94  thf('25', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         ((k4_xboole_0 @ X0 @ X0)
% 33.73/33.94           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 33.73/33.94      inference('demod', [status(thm)], ['23', '24'])).
% 33.73/33.94  thf('26', plain,
% 33.73/33.94      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['3', '4'])).
% 33.73/33.94  thf('27', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         ((k3_subset_1 @ X0 @ X0)
% 33.73/33.94           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 33.73/33.94      inference('demod', [status(thm)], ['25', '26'])).
% 33.73/33.94  thf('28', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 33.73/33.94      inference('sup+', [status(thm)], ['20', '27'])).
% 33.73/33.94  thf('29', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['1', '2'])).
% 33.73/33.94  thf(dt_k3_subset_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 33.73/33.94       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 33.73/33.94  thf('30', plain,
% 33.73/33.94      (![X32 : $i, X33 : $i]:
% 33.73/33.94         ((m1_subset_1 @ (k3_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))
% 33.73/33.94          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 33.73/33.94      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 33.73/33.94  thf('31', plain,
% 33.73/33.94      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['29', '30'])).
% 33.73/33.94  thf('32', plain,
% 33.73/33.94      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 33.73/33.94      inference('sup+', [status(thm)], ['28', '31'])).
% 33.73/33.94  thf(t18_pre_topc, axiom,
% 33.73/33.94    (![A:$i]:
% 33.73/33.94     ( ( l1_struct_0 @ A ) =>
% 33.73/33.94       ( ![B:$i]:
% 33.73/33.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.73/33.94           ( ( k4_subset_1 @
% 33.73/33.94               ( u1_struct_0 @ A ) @ B @ 
% 33.73/33.94               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 33.73/33.94             ( k2_struct_0 @ A ) ) ) ) ))).
% 33.73/33.94  thf('33', plain,
% 33.73/33.94      (![X154 : $i, X155 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X154 @ (k1_zfmisc_1 @ (u1_struct_0 @ X155)))
% 33.73/33.94          | ((k4_subset_1 @ (u1_struct_0 @ X155) @ X154 @ 
% 33.73/33.94              (k3_subset_1 @ (u1_struct_0 @ X155) @ X154))
% 33.73/33.94              = (k2_struct_0 @ X155))
% 33.73/33.94          | ~ (l1_struct_0 @ X155))),
% 33.73/33.94      inference('cnf', [status(esa)], [t18_pre_topc])).
% 33.73/33.94  thf('34', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (l1_struct_0 @ X0)
% 33.73/33.94          | ((k4_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ 
% 33.73/33.94              (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 33.73/33.94              = (k2_struct_0 @ X0)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['32', '33'])).
% 33.73/33.94  thf('35', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 33.73/33.94      inference('sup+', [status(thm)], ['20', '27'])).
% 33.73/33.94  thf('36', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['1', '2'])).
% 33.73/33.94  thf(involutiveness_k3_subset_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 33.73/33.94       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 33.73/33.94  thf('37', plain,
% 33.73/33.94      (![X40 : $i, X41 : $i]:
% 33.73/33.94         (((k3_subset_1 @ X41 @ (k3_subset_1 @ X41 @ X40)) = (X40))
% 33.73/33.94          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 33.73/33.94      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 33.73/33.94  thf('38', plain,
% 33.73/33.94      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['36', '37'])).
% 33.73/33.94  thf('39', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 33.73/33.94      inference('sup+', [status(thm)], ['35', '38'])).
% 33.73/33.94  thf('40', plain,
% 33.73/33.94      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 33.73/33.94      inference('sup+', [status(thm)], ['28', '31'])).
% 33.73/33.94  thf(t28_subset_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 33.73/33.94       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 33.73/33.94  thf('41', plain,
% 33.73/33.94      (![X53 : $i, X54 : $i]:
% 33.73/33.94         (((k4_subset_1 @ X53 @ X54 @ (k2_subset_1 @ X53))
% 33.73/33.94            = (k2_subset_1 @ X53))
% 33.73/33.94          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X53)))),
% 33.73/33.94      inference('cnf', [status(esa)], [t28_subset_1])).
% 33.73/33.94  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 33.73/33.94  thf('42', plain, (![X29 : $i]: ((k2_subset_1 @ X29) = (X29))),
% 33.73/33.94      inference('cnf', [status(esa)], [d4_subset_1])).
% 33.73/33.94  thf('43', plain, (![X29 : $i]: ((k2_subset_1 @ X29) = (X29))),
% 33.73/33.94      inference('cnf', [status(esa)], [d4_subset_1])).
% 33.73/33.94  thf('44', plain,
% 33.73/33.94      (![X53 : $i, X54 : $i]:
% 33.73/33.94         (((k4_subset_1 @ X53 @ X54 @ X53) = (X53))
% 33.73/33.94          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X53)))),
% 33.73/33.94      inference('demod', [status(thm)], ['41', '42', '43'])).
% 33.73/33.94  thf('45', plain,
% 33.73/33.94      (![X0 : $i]: ((k4_subset_1 @ X0 @ k1_xboole_0 @ X0) = (X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['40', '44'])).
% 33.73/33.94  thf('46', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 33.73/33.94      inference('demod', [status(thm)], ['34', '39', '45'])).
% 33.73/33.94  thf(t53_pre_topc, conjecture,
% 33.73/33.94    (![A:$i]:
% 33.73/33.94     ( ( l1_pre_topc @ A ) =>
% 33.73/33.94       ( ![B:$i]:
% 33.73/33.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.73/33.94           ( ( ( v3_pre_topc @ B @ A ) =>
% 33.73/33.94               ( ( k2_pre_topc @
% 33.73/33.94                   A @ 
% 33.73/33.94                   ( k7_subset_1 @
% 33.73/33.94                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 33.73/33.94                 ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) & 
% 33.73/33.94             ( ( ( v2_pre_topc @ A ) & 
% 33.73/33.94                 ( ( k2_pre_topc @
% 33.73/33.94                     A @ 
% 33.73/33.94                     ( k7_subset_1 @
% 33.73/33.94                       ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 33.73/33.94                   ( k7_subset_1 @
% 33.73/33.94                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) =>
% 33.73/33.94               ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 33.73/33.94  thf(zf_stmt_0, negated_conjecture,
% 33.73/33.94    (~( ![A:$i]:
% 33.73/33.94        ( ( l1_pre_topc @ A ) =>
% 33.73/33.94          ( ![B:$i]:
% 33.73/33.94            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.73/33.94              ( ( ( v3_pre_topc @ B @ A ) =>
% 33.73/33.94                  ( ( k2_pre_topc @
% 33.73/33.94                      A @ 
% 33.73/33.94                      ( k7_subset_1 @
% 33.73/33.94                        ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 33.73/33.94                    ( k7_subset_1 @
% 33.73/33.94                      ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) & 
% 33.73/33.94                ( ( ( v2_pre_topc @ A ) & 
% 33.73/33.94                    ( ( k2_pre_topc @
% 33.73/33.94                        A @ 
% 33.73/33.94                        ( k7_subset_1 @
% 33.73/33.94                          ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 33.73/33.94                      ( k7_subset_1 @
% 33.73/33.94                        ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) =>
% 33.73/33.94                  ( v3_pre_topc @ B @ A ) ) ) ) ) ) )),
% 33.73/33.94    inference('cnf.neg', [status(esa)], [t53_pre_topc])).
% 33.73/33.94  thf('47', plain,
% 33.73/33.94      ((m1_subset_1 @ sk_B_11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('48', plain,
% 33.73/33.94      (![X32 : $i, X33 : $i]:
% 33.73/33.94         ((m1_subset_1 @ (k3_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))
% 33.73/33.94          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 33.73/33.94      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 33.73/33.94  thf('49', plain,
% 33.73/33.94      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['47', '48'])).
% 33.73/33.94  thf('50', plain,
% 33.73/33.94      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 33.73/33.94        | ~ (l1_struct_0 @ sk_A))),
% 33.73/33.94      inference('sup+', [status(thm)], ['46', '49'])).
% 33.73/33.94  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf(dt_l1_pre_topc, axiom,
% 33.73/33.94    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 33.73/33.94  thf('52', plain,
% 33.73/33.94      (![X137 : $i]: ((l1_struct_0 @ X137) | ~ (l1_pre_topc @ X137))),
% 33.73/33.94      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 33.73/33.94  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 33.73/33.94      inference('sup-', [status(thm)], ['51', '52'])).
% 33.73/33.94  thf('54', plain,
% 33.73/33.94      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 33.73/33.94      inference('demod', [status(thm)], ['50', '53'])).
% 33.73/33.94  thf('55', plain,
% 33.73/33.94      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['47', '48'])).
% 33.73/33.94  thf('56', plain,
% 33.73/33.94      (![X154 : $i, X155 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X154 @ (k1_zfmisc_1 @ (u1_struct_0 @ X155)))
% 33.73/33.94          | ((k4_subset_1 @ (u1_struct_0 @ X155) @ X154 @ 
% 33.73/33.94              (k3_subset_1 @ (u1_struct_0 @ X155) @ X154))
% 33.73/33.94              = (k2_struct_0 @ X155))
% 33.73/33.94          | ~ (l1_struct_0 @ X155))),
% 33.73/33.94      inference('cnf', [status(esa)], [t18_pre_topc])).
% 33.73/33.94  thf('57', plain,
% 33.73/33.94      ((~ (l1_struct_0 @ sk_A)
% 33.73/33.94        | ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11)))
% 33.73/33.94            = (k2_struct_0 @ sk_A)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['55', '56'])).
% 33.73/33.94  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 33.73/33.94      inference('sup-', [status(thm)], ['51', '52'])).
% 33.73/33.94  thf('59', plain,
% 33.73/33.94      ((m1_subset_1 @ sk_B_11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('60', plain,
% 33.73/33.94      (![X40 : $i, X41 : $i]:
% 33.73/33.94         (((k3_subset_1 @ X41 @ (k3_subset_1 @ X41 @ X40)) = (X40))
% 33.73/33.94          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 33.73/33.94      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 33.73/33.94  thf('61', plain,
% 33.73/33.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11)) = (sk_B_11))),
% 33.73/33.94      inference('sup-', [status(thm)], ['59', '60'])).
% 33.73/33.94  thf('62', plain,
% 33.73/33.94      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['47', '48'])).
% 33.73/33.94  thf(t25_subset_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 33.73/33.94       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 33.73/33.94         ( k2_subset_1 @ A ) ) ))).
% 33.73/33.94  thf('63', plain,
% 33.73/33.94      (![X51 : $i, X52 : $i]:
% 33.73/33.94         (((k4_subset_1 @ X51 @ X52 @ (k3_subset_1 @ X51 @ X52))
% 33.73/33.94            = (k2_subset_1 @ X51))
% 33.73/33.94          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 33.73/33.94      inference('cnf', [status(esa)], [t25_subset_1])).
% 33.73/33.94  thf('64', plain, (![X29 : $i]: ((k2_subset_1 @ X29) = (X29))),
% 33.73/33.94      inference('cnf', [status(esa)], [d4_subset_1])).
% 33.73/33.94  thf('65', plain,
% 33.73/33.94      (![X51 : $i, X52 : $i]:
% 33.73/33.94         (((k4_subset_1 @ X51 @ X52 @ (k3_subset_1 @ X51 @ X52)) = (X51))
% 33.73/33.94          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 33.73/33.94      inference('demod', [status(thm)], ['63', '64'])).
% 33.73/33.94  thf('66', plain,
% 33.73/33.94      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11)))
% 33.73/33.94         = (u1_struct_0 @ sk_A))),
% 33.73/33.94      inference('sup-', [status(thm)], ['62', '65'])).
% 33.73/33.94  thf('67', plain,
% 33.73/33.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11)) = (sk_B_11))),
% 33.73/33.94      inference('sup-', [status(thm)], ['59', '60'])).
% 33.73/33.94  thf('68', plain,
% 33.73/33.94      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ sk_B_11)
% 33.73/33.94         = (u1_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['66', '67'])).
% 33.73/33.94  thf('69', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('70', plain,
% 33.73/33.94      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 33.73/33.94      inference('demod', [status(thm)], ['54', '69'])).
% 33.73/33.94  thf('71', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf(d6_pre_topc, axiom,
% 33.73/33.94    (![A:$i]:
% 33.73/33.94     ( ( l1_pre_topc @ A ) =>
% 33.73/33.94       ( ![B:$i]:
% 33.73/33.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.73/33.94           ( ( v4_pre_topc @ B @ A ) <=>
% 33.73/33.94             ( v3_pre_topc @
% 33.73/33.94               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 33.73/33.94               A ) ) ) ) ))).
% 33.73/33.94  thf('72', plain,
% 33.73/33.94      (![X121 : $i, X122 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X121 @ (k1_zfmisc_1 @ (u1_struct_0 @ X122)))
% 33.73/33.94          | ~ (v4_pre_topc @ X121 @ X122)
% 33.73/33.94          | (v3_pre_topc @ 
% 33.73/33.94             (k7_subset_1 @ (u1_struct_0 @ X122) @ (k2_struct_0 @ X122) @ X121) @ 
% 33.73/33.94             X122)
% 33.73/33.94          | ~ (l1_pre_topc @ X122))),
% 33.73/33.94      inference('cnf', [status(esa)], [d6_pre_topc])).
% 33.73/33.94  thf('73', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 33.73/33.94          | ~ (l1_pre_topc @ sk_A)
% 33.73/33.94          | (v3_pre_topc @ 
% 33.73/33.94             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 33.73/33.94             sk_A)
% 33.73/33.94          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 33.73/33.94      inference('sup-', [status(thm)], ['71', '72'])).
% 33.73/33.94  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('75', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('76', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['1', '2'])).
% 33.73/33.94  thf(redefinition_k7_subset_1, axiom,
% 33.73/33.94    (![A:$i,B:$i,C:$i]:
% 33.73/33.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 33.73/33.94       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 33.73/33.94  thf('77', plain,
% 33.73/33.94      (![X43 : $i, X44 : $i, X45 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 33.73/33.94          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k4_xboole_0 @ X43 @ X45)))),
% 33.73/33.94      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 33.73/33.94  thf('78', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('79', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 33.73/33.94          | (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ X0) @ sk_A)
% 33.73/33.94          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['73', '74', '75', '78'])).
% 33.73/33.94  thf('80', plain,
% 33.73/33.94      ((~ (v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ sk_A)
% 33.73/33.94        | (v3_pre_topc @ 
% 33.73/33.94           (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)) @ 
% 33.73/33.94           sk_A))),
% 33.73/33.94      inference('sup-', [status(thm)], ['70', '79'])).
% 33.73/33.94  thf('81', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 33.73/33.94      inference('demod', [status(thm)], ['34', '39', '45'])).
% 33.73/33.94  thf('82', plain,
% 33.73/33.94      ((m1_subset_1 @ sk_B_11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('83', plain,
% 33.73/33.94      (![X30 : $i, X31 : $i]:
% 33.73/33.94         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 33.73/33.94          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 33.73/33.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 33.73/33.94  thf('84', plain,
% 33.73/33.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('sup-', [status(thm)], ['82', '83'])).
% 33.73/33.94  thf('85', plain,
% 33.73/33.94      (![X8 : $i, X9 : $i]:
% 33.73/33.94         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 33.73/33.94           = (k3_xboole_0 @ X8 @ X9))),
% 33.73/33.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.73/33.94  thf('86', plain,
% 33.73/33.94      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('sup+', [status(thm)], ['84', '85'])).
% 33.73/33.94  thf('87', plain,
% 33.73/33.94      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94        | ~ (l1_struct_0 @ sk_A))),
% 33.73/33.94      inference('sup+', [status(thm)], ['81', '86'])).
% 33.73/33.94  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 33.73/33.94      inference('sup-', [status(thm)], ['51', '52'])).
% 33.73/33.94  thf('89', plain,
% 33.73/33.94      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 33.73/33.94         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['87', '88'])).
% 33.73/33.94  thf('90', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('91', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('92', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 33.73/33.94      inference('demod', [status(thm)], ['34', '39', '45'])).
% 33.73/33.94  thf('93', plain,
% 33.73/33.94      ((m1_subset_1 @ sk_B_11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('94', plain,
% 33.73/33.94      (((m1_subset_1 @ sk_B_11 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 33.73/33.94        | ~ (l1_struct_0 @ sk_A))),
% 33.73/33.94      inference('sup+', [status(thm)], ['92', '93'])).
% 33.73/33.94  thf('95', plain, ((l1_struct_0 @ sk_A)),
% 33.73/33.94      inference('sup-', [status(thm)], ['51', '52'])).
% 33.73/33.94  thf('96', plain,
% 33.73/33.94      ((m1_subset_1 @ sk_B_11 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 33.73/33.94      inference('demod', [status(thm)], ['94', '95'])).
% 33.73/33.94  thf('97', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf(t22_pre_topc, axiom,
% 33.73/33.94    (![A:$i]:
% 33.73/33.94     ( ( l1_struct_0 @ A ) =>
% 33.73/33.94       ( ![B:$i]:
% 33.73/33.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.73/33.94           ( ( k7_subset_1 @
% 33.73/33.94               ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ 
% 33.73/33.94               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 33.73/33.94             ( B ) ) ) ) ))).
% 33.73/33.94  thf('98', plain,
% 33.73/33.94      (![X156 : $i, X157 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X156 @ (k1_zfmisc_1 @ (u1_struct_0 @ X157)))
% 33.73/33.94          | ((k7_subset_1 @ (u1_struct_0 @ X157) @ (k2_struct_0 @ X157) @ 
% 33.73/33.94              (k7_subset_1 @ (u1_struct_0 @ X157) @ (k2_struct_0 @ X157) @ X156))
% 33.73/33.94              = (X156))
% 33.73/33.94          | ~ (l1_struct_0 @ X157))),
% 33.73/33.94      inference('cnf', [status(esa)], [t22_pre_topc])).
% 33.73/33.94  thf('99', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 33.73/33.94          | ~ (l1_struct_0 @ sk_A)
% 33.73/33.94          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 33.73/33.94              = (X0)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['97', '98'])).
% 33.73/33.94  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 33.73/33.94      inference('sup-', [status(thm)], ['51', '52'])).
% 33.73/33.94  thf('101', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('102', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('103', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('104', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('105', plain,
% 33.73/33.94      (![X8 : $i, X9 : $i]:
% 33.73/33.94         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 33.73/33.94           = (k3_xboole_0 @ X8 @ X9))),
% 33.73/33.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.73/33.94  thf('106', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 33.73/33.94          | ((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ X0) = (X0)))),
% 33.73/33.94      inference('demod', [status(thm)],
% 33.73/33.94                ['99', '100', '101', '102', '103', '104', '105'])).
% 33.73/33.94  thf('107', plain,
% 33.73/33.94      (((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11) = (sk_B_11))),
% 33.73/33.94      inference('sup-', [status(thm)], ['96', '106'])).
% 33.73/33.94  thf('108', plain,
% 33.73/33.94      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)) = (sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['89', '90', '91', '107'])).
% 33.73/33.94  thf('109', plain,
% 33.73/33.94      ((~ (v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ sk_A)
% 33.73/33.94        | (v3_pre_topc @ sk_B_11 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['80', '108'])).
% 33.73/33.94  thf('110', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ 
% 33.73/33.94          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94              sk_B_11))
% 33.73/33.94        | ~ (v3_pre_topc @ sk_B_11 @ sk_A))),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('111', plain,
% 33.73/33.94      ((~ (v3_pre_topc @ sk_B_11 @ sk_A))
% 33.73/33.94         <= (~ ((v3_pre_topc @ sk_B_11 @ sk_A)))),
% 33.73/33.94      inference('split', [status(esa)], ['110'])).
% 33.73/33.94  thf('112', plain,
% 33.73/33.94      (((v3_pre_topc @ sk_B_11 @ sk_A)
% 33.73/33.94        | ((k2_pre_topc @ sk_A @ 
% 33.73/33.94            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94             sk_B_11))
% 33.73/33.94            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94               sk_B_11)))),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('113', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('114', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('115', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 33.73/33.94      inference('demod', [status(thm)], ['34', '39', '45'])).
% 33.73/33.94  thf('116', plain,
% 33.73/33.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('sup-', [status(thm)], ['82', '83'])).
% 33.73/33.94  thf('117', plain,
% 33.73/33.94      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94        | ~ (l1_struct_0 @ sk_A))),
% 33.73/33.94      inference('sup+', [status(thm)], ['115', '116'])).
% 33.73/33.94  thf('118', plain, ((l1_struct_0 @ sk_A)),
% 33.73/33.94      inference('sup-', [status(thm)], ['51', '52'])).
% 33.73/33.94  thf('119', plain,
% 33.73/33.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['117', '118'])).
% 33.73/33.94  thf('120', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('121', plain,
% 33.73/33.94      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['119', '120'])).
% 33.73/33.94  thf('122', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('123', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('124', plain,
% 33.73/33.94      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['119', '120'])).
% 33.73/33.94  thf('125', plain,
% 33.73/33.94      (((v3_pre_topc @ sk_B_11 @ sk_A)
% 33.73/33.94        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94            = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)))),
% 33.73/33.94      inference('demod', [status(thm)],
% 33.73/33.94                ['112', '113', '114', '121', '122', '123', '124'])).
% 33.73/33.94  thf('126', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('127', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ 
% 33.73/33.94          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94              sk_B_11)))
% 33.73/33.94         <= (~
% 33.73/33.94             (((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('split', [status(esa)], ['110'])).
% 33.73/33.94  thf('128', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ 
% 33.73/33.94          (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94              sk_B_11)))
% 33.73/33.94         <= (~
% 33.73/33.94             (((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('sup-', [status(thm)], ['126', '127'])).
% 33.73/33.94  thf('129', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('130', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('131', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('132', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          != (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11)))
% 33.73/33.94         <= (~
% 33.73/33.94             (((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 33.73/33.94  thf('133', plain,
% 33.73/33.94      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['119', '120'])).
% 33.73/33.94  thf('134', plain,
% 33.73/33.94      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['119', '120'])).
% 33.73/33.94  thf('135', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          != (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)))
% 33.73/33.94         <= (~
% 33.73/33.94             (((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('demod', [status(thm)], ['132', '133', '134'])).
% 33.73/33.94  thf('136', plain,
% 33.73/33.94      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94           != (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94         | (v3_pre_topc @ sk_B_11 @ sk_A)))
% 33.73/33.94         <= (~
% 33.73/33.94             (((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('sup-', [status(thm)], ['125', '135'])).
% 33.73/33.94  thf('137', plain,
% 33.73/33.94      (((v3_pre_topc @ sk_B_11 @ sk_A))
% 33.73/33.94         <= (~
% 33.73/33.94             (((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('simplify', [status(thm)], ['136'])).
% 33.73/33.94  thf('138', plain,
% 33.73/33.94      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)) = (sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['89', '90', '91', '107'])).
% 33.73/33.94  thf('139', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('140', plain,
% 33.73/33.94      (![X121 : $i, X122 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X121 @ (k1_zfmisc_1 @ (u1_struct_0 @ X122)))
% 33.73/33.94          | ~ (v3_pre_topc @ 
% 33.73/33.94               (k7_subset_1 @ (u1_struct_0 @ X122) @ (k2_struct_0 @ X122) @ 
% 33.73/33.94                X121) @ 
% 33.73/33.94               X122)
% 33.73/33.94          | (v4_pre_topc @ X121 @ X122)
% 33.73/33.94          | ~ (l1_pre_topc @ X122))),
% 33.73/33.94      inference('cnf', [status(esa)], [d6_pre_topc])).
% 33.73/33.94  thf('141', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (v3_pre_topc @ 
% 33.73/33.94             (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 33.73/33.94             sk_A)
% 33.73/33.94          | ~ (l1_pre_topc @ sk_A)
% 33.73/33.94          | (v4_pre_topc @ X0 @ sk_A)
% 33.73/33.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 33.73/33.94      inference('sup-', [status(thm)], ['139', '140'])).
% 33.73/33.94  thf('142', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('144', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('145', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ X0) @ sk_A)
% 33.73/33.94          | (v4_pre_topc @ X0 @ sk_A)
% 33.73/33.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 33.73/33.94      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 33.73/33.94  thf('146', plain,
% 33.73/33.94      ((~ (v3_pre_topc @ sk_B_11 @ sk_A)
% 33.73/33.94        | ~ (m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 33.73/33.94        | (v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ sk_A))),
% 33.73/33.94      inference('sup-', [status(thm)], ['138', '145'])).
% 33.73/33.94  thf('147', plain,
% 33.73/33.94      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 33.73/33.94      inference('demod', [status(thm)], ['54', '69'])).
% 33.73/33.94  thf('148', plain,
% 33.73/33.94      ((~ (v3_pre_topc @ sk_B_11 @ sk_A)
% 33.73/33.94        | (v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['146', '147'])).
% 33.73/33.94  thf('149', plain,
% 33.73/33.94      (((v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ sk_A))
% 33.73/33.94         <= (~
% 33.73/33.94             (((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('sup-', [status(thm)], ['137', '148'])).
% 33.73/33.94  thf('150', plain,
% 33.73/33.94      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['47', '48'])).
% 33.73/33.94  thf(t52_pre_topc, axiom,
% 33.73/33.94    (![A:$i]:
% 33.73/33.94     ( ( l1_pre_topc @ A ) =>
% 33.73/33.94       ( ![B:$i]:
% 33.73/33.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.73/33.94           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 33.73/33.94             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 33.73/33.94               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 33.73/33.94  thf('151', plain,
% 33.73/33.94      (![X165 : $i, X166 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X165 @ (k1_zfmisc_1 @ (u1_struct_0 @ X166)))
% 33.73/33.94          | ~ (v4_pre_topc @ X165 @ X166)
% 33.73/33.94          | ((k2_pre_topc @ X166 @ X165) = (X165))
% 33.73/33.94          | ~ (l1_pre_topc @ X166))),
% 33.73/33.94      inference('cnf', [status(esa)], [t52_pre_topc])).
% 33.73/33.94  thf('152', plain,
% 33.73/33.94      ((~ (l1_pre_topc @ sk_A)
% 33.73/33.94        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94             sk_A))),
% 33.73/33.94      inference('sup-', [status(thm)], ['150', '151'])).
% 33.73/33.94  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('154', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94             sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['152', '153'])).
% 33.73/33.94  thf('155', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('156', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('157', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('158', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94        | ~ (v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94             sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 33.73/33.94  thf('159', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)))
% 33.73/33.94         <= (~
% 33.73/33.94             (((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('sup-', [status(thm)], ['149', '158'])).
% 33.73/33.94  thf('160', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          != (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)))
% 33.73/33.94         <= (~
% 33.73/33.94             (((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('demod', [status(thm)], ['132', '133', '134'])).
% 33.73/33.94  thf('161', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ 
% 33.73/33.94          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94             sk_B_11)))),
% 33.73/33.94      inference('simplify_reflect-', [status(thm)], ['159', '160'])).
% 33.73/33.94  thf('162', plain,
% 33.73/33.94      (~ ((v3_pre_topc @ sk_B_11 @ sk_A)) | 
% 33.73/33.94       ~
% 33.73/33.94       (((k2_pre_topc @ sk_A @ 
% 33.73/33.94          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94             sk_B_11)))),
% 33.73/33.94      inference('split', [status(esa)], ['110'])).
% 33.73/33.94  thf('163', plain, (~ ((v3_pre_topc @ sk_B_11 @ sk_A))),
% 33.73/33.94      inference('sat_resolution*', [status(thm)], ['161', '162'])).
% 33.73/33.94  thf('164', plain, (~ (v3_pre_topc @ sk_B_11 @ sk_A)),
% 33.73/33.94      inference('simpl_trail', [status(thm)], ['111', '163'])).
% 33.73/33.94  thf('165', plain,
% 33.73/33.94      (~ (v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ sk_A)),
% 33.73/33.94      inference('clc', [status(thm)], ['109', '164'])).
% 33.73/33.94  thf('166', plain,
% 33.73/33.94      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ 
% 33.73/33.94        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 33.73/33.94      inference('demod', [status(thm)], ['54', '69'])).
% 33.73/33.94  thf('167', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ 
% 33.73/33.94          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94              sk_B_11))
% 33.73/33.94        | (v2_pre_topc @ sk_A))),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('168', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 33.73/33.94      inference('split', [status(esa)], ['167'])).
% 33.73/33.94  thf('169', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('170', plain,
% 33.73/33.94      (![X165 : $i, X166 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X165 @ (k1_zfmisc_1 @ (u1_struct_0 @ X166)))
% 33.73/33.94          | ~ (v2_pre_topc @ X166)
% 33.73/33.94          | ((k2_pre_topc @ X166 @ X165) != (X165))
% 33.73/33.94          | (v4_pre_topc @ X165 @ X166)
% 33.73/33.94          | ~ (l1_pre_topc @ X166))),
% 33.73/33.94      inference('cnf', [status(esa)], [t52_pre_topc])).
% 33.73/33.94  thf('171', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 33.73/33.94          | ~ (l1_pre_topc @ sk_A)
% 33.73/33.94          | (v4_pre_topc @ X0 @ sk_A)
% 33.73/33.94          | ((k2_pre_topc @ sk_A @ X0) != (X0))
% 33.73/33.94          | ~ (v2_pre_topc @ sk_A))),
% 33.73/33.94      inference('sup-', [status(thm)], ['169', '170'])).
% 33.73/33.94  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('173', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 33.73/33.94          | (v4_pre_topc @ X0 @ sk_A)
% 33.73/33.94          | ((k2_pre_topc @ sk_A @ X0) != (X0))
% 33.73/33.94          | ~ (v2_pre_topc @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['171', '172'])).
% 33.73/33.94  thf('174', plain,
% 33.73/33.94      ((![X0 : $i]:
% 33.73/33.94          (((k2_pre_topc @ sk_A @ X0) != (X0))
% 33.73/33.94           | (v4_pre_topc @ X0 @ sk_A)
% 33.73/33.94           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))))
% 33.73/33.94         <= (((v2_pre_topc @ sk_A)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['168', '173'])).
% 33.73/33.94  thf('175', plain,
% 33.73/33.94      (((v2_pre_topc @ sk_A)) | 
% 33.73/33.94       ~
% 33.73/33.94       (((k2_pre_topc @ sk_A @ 
% 33.73/33.94          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94             sk_B_11)))),
% 33.73/33.94      inference('split', [status(esa)], ['167'])).
% 33.73/33.94  thf('176', plain, (((v2_pre_topc @ sk_A))),
% 33.73/33.94      inference('sat_resolution*', [status(thm)], ['161', '175'])).
% 33.73/33.94  thf('177', plain,
% 33.73/33.94      (![X0 : $i]:
% 33.73/33.94         (((k2_pre_topc @ sk_A @ X0) != (X0))
% 33.73/33.94          | (v4_pre_topc @ X0 @ sk_A)
% 33.73/33.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 33.73/33.94      inference('simpl_trail', [status(thm)], ['174', '176'])).
% 33.73/33.94  thf('178', plain,
% 33.73/33.94      (((v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ sk_A)
% 33.73/33.94        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94            != (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)))),
% 33.73/33.94      inference('sup-', [status(thm)], ['166', '177'])).
% 33.73/33.94  thf('179', plain,
% 33.73/33.94      (((v3_pre_topc @ sk_B_11 @ sk_A)
% 33.73/33.94        | ((k2_pre_topc @ sk_A @ 
% 33.73/33.94            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94             sk_B_11))
% 33.73/33.94            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94               sk_B_11)))),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('180', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ 
% 33.73/33.94          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94             sk_B_11)))
% 33.73/33.94         <= ((((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('split', [status(esa)], ['179'])).
% 33.73/33.94  thf('181', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('182', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('183', plain,
% 33.73/33.94      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['119', '120'])).
% 33.73/33.94  thf('184', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 33.73/33.94      inference('demod', [status(thm)], ['57', '58', '61', '68'])).
% 33.73/33.94  thf('185', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup-', [status(thm)], ['76', '77'])).
% 33.73/33.94  thf('186', plain,
% 33.73/33.94      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('demod', [status(thm)], ['119', '120'])).
% 33.73/33.94  thf('187', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)))
% 33.73/33.94         <= ((((k2_pre_topc @ sk_A @ 
% 33.73/33.94                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                 sk_B_11))
% 33.73/33.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94                   sk_B_11))))),
% 33.73/33.94      inference('demod', [status(thm)],
% 33.73/33.94                ['180', '181', '182', '183', '184', '185', '186'])).
% 33.73/33.94  thf('188', plain,
% 33.73/33.94      ((((k2_pre_topc @ sk_A @ 
% 33.73/33.94          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 33.73/33.94             sk_B_11)))),
% 33.73/33.94      inference('sat_resolution*', [status(thm)], ['161'])).
% 33.73/33.94  thf('189', plain,
% 33.73/33.94      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))
% 33.73/33.94         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11))),
% 33.73/33.94      inference('simpl_trail', [status(thm)], ['187', '188'])).
% 33.73/33.94  thf('190', plain,
% 33.73/33.94      (((v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ sk_A)
% 33.73/33.94        | ((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)
% 33.73/33.94            != (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11)))),
% 33.73/33.94      inference('demod', [status(thm)], ['178', '189'])).
% 33.73/33.94  thf('191', plain,
% 33.73/33.94      ((v4_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_11) @ sk_A)),
% 33.73/33.94      inference('simplify', [status(thm)], ['190'])).
% 33.73/33.94  thf('192', plain, ($false), inference('demod', [status(thm)], ['165', '191'])).
% 33.73/33.94  
% 33.73/33.94  % SZS output end Refutation
% 33.73/33.94  
% 33.77/33.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
