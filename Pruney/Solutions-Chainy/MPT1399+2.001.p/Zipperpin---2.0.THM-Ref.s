%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wf3LU6H7Q5

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:02 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 478 expanded)
%              Number of leaves         :   42 ( 162 expanded)
%              Depth                    :   28
%              Number of atoms          : 1005 (6305 expanded)
%              Number of equality atoms :   53 ( 335 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('2',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( v4_pre_topc @ X53 @ X54 )
      | ~ ( v1_xboole_0 @ X53 )
      | ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ( v4_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X35: $i] :
      ( v1_xboole_0 @ ( sk_B @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('7',plain,(
    ! [X35: $i] :
      ( v1_xboole_0 @ ( sk_B @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('9',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X25: $i] :
      ( ( X25 = sk_C_1 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('15',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ~ ( v4_pre_topc @ X58 @ X59 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 ) @ X59 )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_C_1 ) @ X0 )
      | ~ ( v4_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C_1 )
      = ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('30',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ sk_C_1 )
      = X7 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C_1 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ sk_C_1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C_1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('36',plain,(
    ! [X0: $i] :
      ( sk_C_1
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C_1 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C_1 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ( r2_hidden @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('49',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( v3_pre_topc @ X55 @ X56 )
      | ~ ( v1_xboole_0 @ X55 )
      | ~ ( l1_pre_topc @ X56 )
      | ~ ( v2_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ( v3_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C_1 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','40'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 ) @ X59 )
      | ( v4_pre_topc @ X58 @ X59 )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('61',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( sk_C_1
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('64',plain,(
    ! [X0: $i] :
      ( sk_C_1
      = ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('69',plain,(
    ! [X62: $i] :
      ( ~ ( v3_pre_topc @ X62 @ sk_A )
      | ~ ( v4_pre_topc @ X62 @ sk_A )
      | ~ ( r2_hidden @ sk_B_3 @ X62 )
      | ( r2_hidden @ X62 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('76',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('80',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('81',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ sk_C_1 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('87',plain,(
    ! [X23: $i] :
      ( ( r1_xboole_0 @ X23 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('88',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['77','92'])).

thf('94',plain,
    ( ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['74','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','94'])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('100',plain,(
    ! [X57: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X57 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ( v2_struct_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('101',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( v1_xboole_0 @ X37 )
      | ~ ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_xboole_0 @ ( sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X57: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_2 @ X57 ) )
      | ~ ( l1_pre_topc @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ( v2_struct_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wf3LU6H7Q5
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 673 iterations in 0.257s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.70  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.46/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.46/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.70  thf(t28_connsp_2, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( m1_subset_1 @
% 0.46/0.70                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.70               ( ~( ( ![D:$i]:
% 0.46/0.70                      ( ( m1_subset_1 @
% 0.46/0.70                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70                        ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.70                          ( ( v3_pre_topc @ D @ A ) & 
% 0.46/0.70                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.46/0.70                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.70            ( l1_pre_topc @ A ) ) =>
% 0.46/0.70          ( ![B:$i]:
% 0.46/0.70            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70              ( ![C:$i]:
% 0.46/0.70                ( ( m1_subset_1 @
% 0.46/0.70                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.70                  ( ~( ( ![D:$i]:
% 0.46/0.70                         ( ( m1_subset_1 @
% 0.46/0.70                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70                           ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.70                             ( ( v3_pre_topc @ D @ A ) & 
% 0.46/0.70                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.46/0.70                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.46/0.70  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t4_subset_1, axiom,
% 0.46/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.70  thf('2', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('3', plain, (![X36 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf(cc2_pre_topc, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (![X53 : $i, X54 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.46/0.70          | (v4_pre_topc @ X53 @ X54)
% 0.46/0.70          | ~ (v1_xboole_0 @ X53)
% 0.46/0.70          | ~ (l1_pre_topc @ X54)
% 0.46/0.70          | ~ (v2_pre_topc @ X54))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_pre_topc @ X0)
% 0.46/0.70          | ~ (l1_pre_topc @ X0)
% 0.46/0.70          | ~ (v1_xboole_0 @ sk_C_1)
% 0.46/0.70          | (v4_pre_topc @ sk_C_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf(rc2_subset_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ?[B:$i]:
% 0.46/0.70       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.46/0.70  thf('6', plain, (![X35 : $i]: (v1_xboole_0 @ (sk_B @ X35))),
% 0.46/0.70      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.46/0.70  thf('7', plain, (![X35 : $i]: (v1_xboole_0 @ (sk_B @ X35))),
% 0.46/0.70      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.46/0.70  thf(t6_boole, axiom,
% 0.46/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      (![X25 : $i]: (((X25) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X25))),
% 0.46/0.70      inference('cnf', [status(esa)], [t6_boole])).
% 0.46/0.70  thf('9', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('10', plain, (![X25 : $i]: (((X25) = (sk_C_1)) | ~ (v1_xboole_0 @ X25))),
% 0.46/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('11', plain, (![X0 : $i]: ((sk_B @ X0) = (sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['7', '10'])).
% 0.46/0.70  thf('12', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.46/0.70      inference('demod', [status(thm)], ['6', '11'])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_pre_topc @ X0)
% 0.46/0.70          | ~ (l1_pre_topc @ X0)
% 0.46/0.70          | (v4_pre_topc @ sk_C_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['5', '12'])).
% 0.46/0.70  thf('14', plain, (![X36 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf(t29_tops_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_pre_topc @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70           ( ( v4_pre_topc @ B @ A ) <=>
% 0.46/0.70             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X58 : $i, X59 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 0.46/0.70          | ~ (v4_pre_topc @ X58 @ X59)
% 0.46/0.70          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X59) @ X58) @ X59)
% 0.46/0.70          | ~ (l1_pre_topc @ X59))),
% 0.46/0.70      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (l1_pre_topc @ X0)
% 0.46/0.70          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ sk_C_1) @ X0)
% 0.46/0.70          | ~ (v4_pre_topc @ sk_C_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('17', plain, (![X36 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf(d5_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (![X31 : $i, X32 : $i]:
% 0.46/0.70         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 0.46/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C_1) = (k4_xboole_0 @ X0 @ sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.70  thf(t48_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X13 : $i, X14 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.46/0.70           = (k3_xboole_0 @ X13 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf(t2_boole, axiom,
% 0.46/0.70    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.70  thf('22', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('23', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('24', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ sk_C_1) = (sk_C_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.70  thf(t52_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.46/0.70       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.46/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 0.46/0.70              (k3_xboole_0 @ X18 @ X20)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ sk_C_1))
% 0.46/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ sk_C_1))),
% 0.46/0.70      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.70  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.70  thf(t1_boole, axiom,
% 0.46/0.70    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.70  thf('29', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.70  thf('30', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('31', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ sk_C_1) = (X7))),
% 0.46/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_C_1 @ X0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['28', '31'])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ sk_C_1))
% 0.46/0.70           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('demod', [status(thm)], ['26', '27', '32'])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_C_1) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['20', '33'])).
% 0.46/0.70  thf('35', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ sk_C_1) = (sk_C_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.70  thf('36', plain, (![X0 : $i]: ((sk_C_1) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (![X13 : $i, X14 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.46/0.70           = (k3_xboole_0 @ X13 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C_1) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['36', '37'])).
% 0.46/0.70  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.70  thf('39', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.70  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C_1) = (X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.70  thf('41', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C_1) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['19', '40'])).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (l1_pre_topc @ X0)
% 0.46/0.70          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.70          | ~ (v4_pre_topc @ sk_C_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['16', '41'])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (l1_pre_topc @ X0)
% 0.46/0.70          | ~ (v2_pre_topc @ X0)
% 0.46/0.70          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.70          | ~ (l1_pre_topc @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['13', '42'])).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.70          | ~ (v2_pre_topc @ X0)
% 0.46/0.70          | ~ (l1_pre_topc @ X0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.70  thf('45', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(d2_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.70         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.70       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.70         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (![X28 : $i, X29 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X28 @ X29)
% 0.46/0.70          | (r2_hidden @ X28 @ X29)
% 0.46/0.70          | (v1_xboole_0 @ X29))),
% 0.46/0.70      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.70        | (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.70  thf('48', plain, (![X36 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf(cc1_tops_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      (![X55 : $i, X56 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.46/0.70          | (v3_pre_topc @ X55 @ X56)
% 0.46/0.70          | ~ (v1_xboole_0 @ X55)
% 0.46/0.70          | ~ (l1_pre_topc @ X56)
% 0.46/0.70          | ~ (v2_pre_topc @ X56))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_pre_topc @ X0)
% 0.46/0.70          | ~ (l1_pre_topc @ X0)
% 0.46/0.70          | ~ (v1_xboole_0 @ sk_C_1)
% 0.46/0.70          | (v3_pre_topc @ sk_C_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('51', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.46/0.70      inference('demod', [status(thm)], ['6', '11'])).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_pre_topc @ X0)
% 0.46/0.70          | ~ (l1_pre_topc @ X0)
% 0.46/0.70          | (v3_pre_topc @ sk_C_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.70  thf('53', plain, (![X36 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf(dt_k3_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (![X33 : $i, X34 : $i]:
% 0.46/0.70         ((m1_subset_1 @ (k3_subset_1 @ X33 @ X34) @ (k1_zfmisc_1 @ X33))
% 0.46/0.70          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (m1_subset_1 @ (k3_subset_1 @ X0 @ sk_C_1) @ (k1_zfmisc_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf('56', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C_1) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['19', '40'])).
% 0.46/0.70  thf('57', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      (![X58 : $i, X59 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 0.46/0.70          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X59) @ X58) @ X59)
% 0.46/0.70          | (v4_pre_topc @ X58 @ X59)
% 0.46/0.70          | ~ (l1_pre_topc @ X59))),
% 0.46/0.70      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (l1_pre_topc @ X0)
% 0.46/0.70          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.70          | ~ (v3_pre_topc @ 
% 0.46/0.70               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('60', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (![X31 : $i, X32 : $i]:
% 0.46/0.70         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 0.46/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.70  thf('63', plain, (![X0 : $i]: ((sk_C_1) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.70  thf('64', plain, (![X0 : $i]: ((sk_C_1) = (k3_subset_1 @ X0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['62', '63'])).
% 0.46/0.70  thf('65', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (l1_pre_topc @ X0)
% 0.46/0.70          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.70          | ~ (v3_pre_topc @ sk_C_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.70  thf('66', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (l1_pre_topc @ X0)
% 0.46/0.70          | ~ (v2_pre_topc @ X0)
% 0.46/0.70          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.70          | ~ (l1_pre_topc @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['52', '65'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.70          | ~ (v2_pre_topc @ X0)
% 0.46/0.70          | ~ (l1_pre_topc @ X0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['66'])).
% 0.46/0.70  thf('68', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('69', plain,
% 0.46/0.70      (![X62 : $i]:
% 0.46/0.70         (~ (v3_pre_topc @ X62 @ sk_A)
% 0.46/0.70          | ~ (v4_pre_topc @ X62 @ sk_A)
% 0.46/0.70          | ~ (r2_hidden @ sk_B_3 @ X62)
% 0.46/0.70          | (r2_hidden @ X62 @ sk_C_1)
% 0.46/0.70          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.46/0.70        | ~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.46/0.70        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.70        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.70        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.70        | ~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.46/0.70        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['67', '70'])).
% 0.46/0.70  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('74', plain,
% 0.46/0.70      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.70        | ~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.46/0.70        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.46/0.70  thf('75', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ sk_C_1) = (sk_C_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.70  thf(t4_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.70            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.70       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.70            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.70  thf('76', plain,
% 0.46/0.70      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.46/0.70          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.70  thf('77', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X1 @ sk_C_1) | ~ (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.70  thf('78', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ sk_C_1) = (sk_C_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.70  thf('79', plain,
% 0.46/0.70      (![X3 : $i, X4 : $i]:
% 0.46/0.70         ((r1_xboole_0 @ X3 @ X4)
% 0.46/0.70          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.70  thf('80', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.70  thf('81', plain,
% 0.46/0.70      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.46/0.70          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.70  thf('82', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['80', '81'])).
% 0.46/0.70  thf('83', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((r1_xboole_0 @ X1 @ X0)
% 0.46/0.71          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['79', '82'])).
% 0.46/0.71  thf('84', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_C_1))
% 0.46/0.71          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.46/0.71      inference('sup-', [status(thm)], ['78', '83'])).
% 0.46/0.71  thf('85', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ sk_C_1) = (sk_C_1))),
% 0.46/0.71      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.71  thf('86', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (r1_xboole_0 @ sk_C_1 @ sk_C_1) | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.46/0.71      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.71  thf(t66_xboole_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.46/0.71       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.46/0.71  thf('87', plain,
% 0.46/0.71      (![X23 : $i]: ((r1_xboole_0 @ X23 @ X23) | ((X23) != (k1_xboole_0)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.46/0.71  thf('88', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.46/0.71      inference('simplify', [status(thm)], ['87'])).
% 0.46/0.71  thf('89', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('90', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('91', plain, ((r1_xboole_0 @ sk_C_1 @ sk_C_1)),
% 0.46/0.71      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.46/0.71  thf('92', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_C_1)),
% 0.46/0.71      inference('demod', [status(thm)], ['86', '91'])).
% 0.46/0.71  thf('93', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ sk_C_1)),
% 0.46/0.71      inference('demod', [status(thm)], ['77', '92'])).
% 0.46/0.71  thf('94', plain,
% 0.46/0.71      ((~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.46/0.71        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.71      inference('clc', [status(thm)], ['74', '93'])).
% 0.46/0.71  thf('95', plain,
% 0.46/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['47', '94'])).
% 0.46/0.71  thf('96', plain,
% 0.46/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.71        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['44', '95'])).
% 0.46/0.71  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('99', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.46/0.71  thf(rc3_tops_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.71       ( ?[B:$i]:
% 0.46/0.71         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.46/0.71           ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.71           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.71  thf('100', plain,
% 0.46/0.71      (![X57 : $i]:
% 0.46/0.71         ((m1_subset_1 @ (sk_B_2 @ X57) @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.46/0.71          | ~ (l1_pre_topc @ X57)
% 0.46/0.71          | ~ (v2_pre_topc @ X57)
% 0.46/0.71          | (v2_struct_0 @ X57))),
% 0.46/0.71      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.46/0.71  thf(cc1_subset_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( v1_xboole_0 @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.46/0.71  thf('101', plain,
% 0.46/0.71      (![X37 : $i, X38 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.46/0.71          | (v1_xboole_0 @ X37)
% 0.46/0.71          | ~ (v1_xboole_0 @ X38))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.46/0.71  thf('102', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((v2_struct_0 @ X0)
% 0.46/0.71          | ~ (v2_pre_topc @ X0)
% 0.46/0.71          | ~ (l1_pre_topc @ X0)
% 0.46/0.71          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.46/0.71          | (v1_xboole_0 @ (sk_B_2 @ X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['100', '101'])).
% 0.46/0.71  thf('103', plain,
% 0.46/0.71      (((v1_xboole_0 @ (sk_B_2 @ sk_A))
% 0.46/0.71        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.71        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.71        | (v2_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['99', '102'])).
% 0.46/0.71  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('106', plain, (((v1_xboole_0 @ (sk_B_2 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.46/0.71  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('108', plain, ((v1_xboole_0 @ (sk_B_2 @ sk_A))),
% 0.46/0.71      inference('clc', [status(thm)], ['106', '107'])).
% 0.46/0.71  thf('109', plain,
% 0.46/0.71      (![X57 : $i]:
% 0.46/0.71         (~ (v1_xboole_0 @ (sk_B_2 @ X57))
% 0.46/0.71          | ~ (l1_pre_topc @ X57)
% 0.46/0.71          | ~ (v2_pre_topc @ X57)
% 0.46/0.71          | (v2_struct_0 @ X57))),
% 0.46/0.71      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.46/0.71  thf('110', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['108', '109'])).
% 0.46/0.71  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('113', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.71      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.46/0.71  thf('114', plain, ($false), inference('demod', [status(thm)], ['0', '113'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
