%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1868+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rTFysQGrWP

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:28 EST 2020

% Result     : Theorem 7.17s
% Output     : Refutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :  284 (1146 expanded)
%              Number of leaves         :   42 ( 351 expanded)
%              Depth                    :   45
%              Number of atoms          : 2444 (10569 expanded)
%              Number of equality atoms :  125 ( 398 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t36_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k6_domain_1 @ X21 @ X22 )
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k9_subset_1 @ X25 @ X23 @ X24 )
        = ( k3_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k9_subset_1 @ X25 @ X23 @ X24 )
        = ( k3_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('37',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('49',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d5_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r1_tarski @ ( sk_C @ X6 @ X7 ) @ X6 )
      | ( v2_tex_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v2_tex_2 @ ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('64',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('67',plain,
    ( ( ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('69',plain,
    ( ( ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('70',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('71',plain,
    ( ( ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('73',plain,
    ( ( ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','75'])).

thf('77',plain,
    ( ( r1_tarski @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['59','76'])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('78',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29
        = ( k1_tarski @ X28 ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tarski @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['59','76'])).

thf('81',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ X29 @ ( k1_tarski @ X30 ) )
      | ( X29
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('85',plain,(
    ! [X30: $i] :
      ( r1_tarski @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('90',plain,(
    ! [X20: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('91',plain,(
    ! [X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(dt_k1_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k1_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('93',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_struct_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('99',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X7 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 @ X9 )
       != ( sk_C @ X6 @ X7 ) )
      | ( v2_tex_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ X0 )
       != ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ X0 )
       != ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
     != ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('106',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_struct_0])).

thf('107',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( k1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) )
        = ( k1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) )
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_struct_0 @ X0 ) )
        = ( k1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_struct_0 @ X0 ) )
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('117',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k9_subset_1 @ X25 @ X23 @ X24 )
        = ( k3_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('120',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_struct_0])).

thf('121',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k1_struct_0 @ X0 ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('124',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['122','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('130',plain,
    ( ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['119','130'])).

thf('132',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('133',plain,
    ( ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['118','133'])).

thf('135',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ X29 @ ( k1_tarski @ X30 ) )
      | ( X29 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('136',plain,(
    ! [X30: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('138',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ ( k1_tarski @ X0 ) @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('142',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k9_subset_1 @ X25 @ X23 @ X24 )
        = ( k3_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ ( k1_tarski @ X0 ) @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X30: $i] :
      ( r1_tarski @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('146',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k9_subset_1 @ X25 @ X23 @ X24 )
        = ( k3_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['144','149'])).

thf('151',plain,(
    ! [X30: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('152',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('156',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','154','155'])).

thf('157',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['115','156'])).

thf('158',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('159',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('161',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('163',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('167',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['114','167'])).

thf('169',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('170',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_struct_0])).

thf('172',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('174',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k9_subset_1 @ X25 @ X23 @ X24 )
        = ( k3_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','153'])).

thf('182',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('183',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('184',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('185',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('186',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['186','189'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('191',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('192',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('193',plain,(
    ! [X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('194',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['191','194'])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('199',plain,(
    v3_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['190','195','196','197','198'])).

thf('200',plain,
    ( ( k1_xboole_0
     != ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','180','181','182','183','199'])).

thf('201',plain,(
    ~ ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','75'])).

thf('202',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( k1_xboole_0
     != ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['89','202'])).

thf('204',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('205',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v2_tex_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('206',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ~ ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','75'])).

thf('210',plain,
    ( ( m1_subset_1 @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('212',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('214',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['203','214'])).

thf('216',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','216'])).

thf('218',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','218'])).

thf('220',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ sk_B ) @ X0 )
       != ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) )
       != ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) )
       != ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,
    ( ( ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
     != ( sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['220','224'])).

thf('226',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','226'])).

thf('228',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('229',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ~ ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','75'])).

thf('231',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','231'])).

thf('233',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('239',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    $false ),
    inference(demod,[status(thm)],['0','239'])).


%------------------------------------------------------------------------------
