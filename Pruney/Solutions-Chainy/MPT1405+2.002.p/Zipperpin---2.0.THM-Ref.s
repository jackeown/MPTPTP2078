%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qNVqaMWb1

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:14 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 135 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  715 (1243 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('0',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X23 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k2_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','12'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('16',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18','19'])).

thf('21',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X25 )
      | ( ( k1_tops_1 @ X25 @ X26 )
        = X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('24',plain,
    ( ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( v3_pre_topc @ X26 @ X25 )
        | ( ( k1_tops_1 @ X25 @ X26 )
          = X26 ) )
   <= ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( v3_pre_topc @ X26 @ X25 )
        | ( ( k1_tops_1 @ X25 @ X26 )
          = X26 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) )
   <= ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('27',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( v3_pre_topc @ X26 @ X25 )
        | ( ( k1_tops_1 @ X25 @ X26 )
          = X26 ) )
    | ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X25 )
      | ( ( k1_tops_1 @ X25 @ X26 )
        = X26 ) ) ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X25 )
      | ( ( k1_tops_1 @ X25 @ X26 )
        = X26 ) ) ),
    inference(simpl_trail,[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( r1_tarski @ X29 @ ( k1_tops_1 @ X30 @ X31 ) )
      | ( m2_connsp_2 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['46','49','50','51','54'])).

thf('56',plain,
    ( ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('58',plain,(
    m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qNVqaMWb1
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:02:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.63/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.83  % Solved by: fo/fo7.sh
% 0.63/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.83  % done 899 iterations in 0.384s
% 0.63/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.83  % SZS output start Refutation
% 0.63/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.63/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.63/0.83  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.63/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.63/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.63/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.63/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.63/0.83  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.63/0.83  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.63/0.83  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.63/0.83  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.63/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.63/0.83  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.63/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.63/0.83  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.63/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.63/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.63/0.83  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.63/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.63/0.83  thf(t35_connsp_2, conjecture,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.83           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.63/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.83    (~( ![A:$i]:
% 0.63/0.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.63/0.83            ( l1_pre_topc @ A ) ) =>
% 0.63/0.83          ( ![B:$i]:
% 0.63/0.83            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.83              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.63/0.83    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.63/0.83  thf('0', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf(d3_struct_0, axiom,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.63/0.83  thf('1', plain,
% 0.63/0.83      (![X21 : $i]:
% 0.63/0.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.63/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.63/0.83  thf('2', plain,
% 0.63/0.83      (![X21 : $i]:
% 0.63/0.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.63/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.63/0.83  thf(t4_subset_1, axiom,
% 0.63/0.83    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.63/0.83  thf('3', plain,
% 0.63/0.83      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.63/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.63/0.83  thf(cc2_pre_topc, axiom,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.83           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.63/0.83  thf('4', plain,
% 0.63/0.83      (![X19 : $i, X20 : $i]:
% 0.63/0.83         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.63/0.83          | (v4_pre_topc @ X19 @ X20)
% 0.63/0.83          | ~ (v1_xboole_0 @ X19)
% 0.63/0.83          | ~ (l1_pre_topc @ X20)
% 0.63/0.83          | ~ (v2_pre_topc @ X20))),
% 0.63/0.83      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.63/0.83  thf('5', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (~ (v2_pre_topc @ X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0)
% 0.63/0.83          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.63/0.83          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['3', '4'])).
% 0.63/0.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.63/0.83  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.63/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.63/0.83  thf('7', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (~ (v2_pre_topc @ X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0)
% 0.63/0.83          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.63/0.83      inference('demod', [status(thm)], ['5', '6'])).
% 0.63/0.83  thf('8', plain,
% 0.63/0.83      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.63/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.63/0.83  thf(d6_pre_topc, axiom,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( l1_pre_topc @ A ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.83           ( ( v4_pre_topc @ B @ A ) <=>
% 0.63/0.83             ( v3_pre_topc @
% 0.63/0.83               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.63/0.83               A ) ) ) ) ))).
% 0.63/0.83  thf('9', plain,
% 0.63/0.83      (![X22 : $i, X23 : $i]:
% 0.63/0.83         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.63/0.83          | ~ (v4_pre_topc @ X22 @ X23)
% 0.63/0.83          | (v3_pre_topc @ 
% 0.63/0.83             (k7_subset_1 @ (u1_struct_0 @ X23) @ (k2_struct_0 @ X23) @ X22) @ 
% 0.63/0.83             X23)
% 0.63/0.83          | ~ (l1_pre_topc @ X23))),
% 0.63/0.83      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.63/0.83  thf('10', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (~ (l1_pre_topc @ X0)
% 0.63/0.83          | (v3_pre_topc @ 
% 0.63/0.83             (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ 
% 0.63/0.83              k1_xboole_0) @ 
% 0.63/0.83             X0)
% 0.63/0.83          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['8', '9'])).
% 0.63/0.83  thf('11', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (~ (l1_pre_topc @ X0)
% 0.63/0.83          | ~ (v2_pre_topc @ X0)
% 0.63/0.83          | (v3_pre_topc @ 
% 0.63/0.83             (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ 
% 0.63/0.83              k1_xboole_0) @ 
% 0.63/0.83             X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['7', '10'])).
% 0.63/0.83  thf('12', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v3_pre_topc @ 
% 0.63/0.83           (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.63/0.83           X0)
% 0.63/0.83          | ~ (v2_pre_topc @ X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0))),
% 0.63/0.83      inference('simplify', [status(thm)], ['11'])).
% 0.63/0.83  thf('13', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v3_pre_topc @ 
% 0.63/0.83           (k7_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.63/0.83           X0)
% 0.63/0.83          | ~ (l1_struct_0 @ X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0)
% 0.63/0.83          | ~ (v2_pre_topc @ X0))),
% 0.63/0.83      inference('sup+', [status(thm)], ['2', '12'])).
% 0.63/0.83  thf(dt_k2_subset_1, axiom,
% 0.63/0.83    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.63/0.83  thf('14', plain,
% 0.63/0.83      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.63/0.83      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.63/0.83  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.63/0.83  thf('15', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.63/0.83      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.63/0.83  thf('16', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.63/0.83      inference('demod', [status(thm)], ['14', '15'])).
% 0.63/0.83  thf(redefinition_k7_subset_1, axiom,
% 0.63/0.83    (![A:$i,B:$i,C:$i]:
% 0.63/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.63/0.83       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.63/0.83  thf('17', plain,
% 0.63/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.63/0.83         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.63/0.83          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.63/0.83      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.63/0.83  thf('18', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.63/0.83  thf(t3_boole, axiom,
% 0.63/0.83    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.63/0.83  thf('19', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.63/0.83      inference('cnf', [status(esa)], [t3_boole])).
% 0.63/0.83  thf('20', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.63/0.83          | ~ (l1_struct_0 @ X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0)
% 0.63/0.83          | ~ (v2_pre_topc @ X0))),
% 0.63/0.83      inference('demod', [status(thm)], ['13', '18', '19'])).
% 0.63/0.83  thf('21', plain,
% 0.63/0.83      (![X21 : $i]:
% 0.63/0.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.63/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.63/0.83  thf('22', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.63/0.83      inference('demod', [status(thm)], ['14', '15'])).
% 0.63/0.83  thf(t55_tops_1, axiom,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( l1_pre_topc @ B ) =>
% 0.63/0.83           ( ![C:$i]:
% 0.63/0.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.83               ( ![D:$i]:
% 0.63/0.83                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.63/0.83                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.63/0.83                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.63/0.83                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.63/0.83                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.63/0.83  thf('23', plain,
% 0.63/0.83      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.63/0.83         (~ (l1_pre_topc @ X25)
% 0.63/0.83          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.63/0.83          | ~ (v3_pre_topc @ X26 @ X25)
% 0.63/0.83          | ((k1_tops_1 @ X25 @ X26) = (X26))
% 0.63/0.83          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.63/0.83          | ~ (l1_pre_topc @ X28)
% 0.63/0.83          | ~ (v2_pre_topc @ X28))),
% 0.63/0.83      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.63/0.83  thf('24', plain,
% 0.63/0.83      ((![X25 : $i, X26 : $i]:
% 0.63/0.83          (~ (l1_pre_topc @ X25)
% 0.63/0.83           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.63/0.83           | ~ (v3_pre_topc @ X26 @ X25)
% 0.63/0.83           | ((k1_tops_1 @ X25 @ X26) = (X26))))
% 0.63/0.83         <= ((![X25 : $i, X26 : $i]:
% 0.63/0.83                (~ (l1_pre_topc @ X25)
% 0.63/0.83                 | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.63/0.83                 | ~ (v3_pre_topc @ X26 @ X25)
% 0.63/0.83                 | ((k1_tops_1 @ X25 @ X26) = (X26)))))),
% 0.63/0.83      inference('split', [status(esa)], ['23'])).
% 0.63/0.83  thf('25', plain,
% 0.63/0.83      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('26', plain,
% 0.63/0.83      ((![X27 : $i, X28 : $i]:
% 0.63/0.83          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.63/0.83           | ~ (l1_pre_topc @ X28)
% 0.63/0.83           | ~ (v2_pre_topc @ X28)))
% 0.63/0.83         <= ((![X27 : $i, X28 : $i]:
% 0.63/0.83                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.63/0.83                 | ~ (l1_pre_topc @ X28)
% 0.63/0.83                 | ~ (v2_pre_topc @ X28))))),
% 0.63/0.83      inference('split', [status(esa)], ['23'])).
% 0.63/0.83  thf('27', plain,
% 0.63/0.83      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.63/0.83         <= ((![X27 : $i, X28 : $i]:
% 0.63/0.83                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.63/0.83                 | ~ (l1_pre_topc @ X28)
% 0.63/0.83                 | ~ (v2_pre_topc @ X28))))),
% 0.63/0.83      inference('sup-', [status(thm)], ['25', '26'])).
% 0.63/0.83  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('30', plain,
% 0.63/0.83      (~
% 0.63/0.83       (![X27 : $i, X28 : $i]:
% 0.63/0.83          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.63/0.83           | ~ (l1_pre_topc @ X28)
% 0.63/0.83           | ~ (v2_pre_topc @ X28)))),
% 0.63/0.83      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.63/0.83  thf('31', plain,
% 0.63/0.83      ((![X25 : $i, X26 : $i]:
% 0.63/0.83          (~ (l1_pre_topc @ X25)
% 0.63/0.83           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.63/0.83           | ~ (v3_pre_topc @ X26 @ X25)
% 0.63/0.83           | ((k1_tops_1 @ X25 @ X26) = (X26)))) | 
% 0.63/0.83       (![X27 : $i, X28 : $i]:
% 0.63/0.83          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.63/0.83           | ~ (l1_pre_topc @ X28)
% 0.63/0.83           | ~ (v2_pre_topc @ X28)))),
% 0.63/0.83      inference('split', [status(esa)], ['23'])).
% 0.63/0.83  thf('32', plain,
% 0.63/0.83      ((![X25 : $i, X26 : $i]:
% 0.63/0.83          (~ (l1_pre_topc @ X25)
% 0.63/0.83           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.63/0.83           | ~ (v3_pre_topc @ X26 @ X25)
% 0.63/0.83           | ((k1_tops_1 @ X25 @ X26) = (X26))))),
% 0.63/0.83      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.63/0.83  thf('33', plain,
% 0.63/0.83      (![X25 : $i, X26 : $i]:
% 0.63/0.83         (~ (l1_pre_topc @ X25)
% 0.63/0.83          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.63/0.83          | ~ (v3_pre_topc @ X26 @ X25)
% 0.63/0.83          | ((k1_tops_1 @ X25 @ X26) = (X26)))),
% 0.63/0.83      inference('simpl_trail', [status(thm)], ['24', '32'])).
% 0.63/0.83  thf('34', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.63/0.83          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['22', '33'])).
% 0.63/0.83  thf('35', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.63/0.83          | ~ (l1_struct_0 @ X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0)
% 0.63/0.83          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.63/0.83      inference('sup-', [status(thm)], ['21', '34'])).
% 0.63/0.83  thf('36', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (~ (v2_pre_topc @ X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0)
% 0.63/0.83          | ~ (l1_struct_0 @ X0)
% 0.63/0.83          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.63/0.83          | ~ (l1_pre_topc @ X0)
% 0.63/0.83          | ~ (l1_struct_0 @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['20', '35'])).
% 0.63/0.83  thf('37', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.63/0.83          | ~ (l1_struct_0 @ X0)
% 0.63/0.83          | ~ (l1_pre_topc @ X0)
% 0.63/0.83          | ~ (v2_pre_topc @ X0))),
% 0.63/0.83      inference('simplify', [status(thm)], ['36'])).
% 0.63/0.83  thf('38', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.63/0.83      inference('demod', [status(thm)], ['14', '15'])).
% 0.63/0.83  thf('39', plain,
% 0.63/0.83      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf(d2_connsp_2, axiom,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.83           ( ![C:$i]:
% 0.63/0.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.83               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.63/0.83                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.63/0.83  thf('40', plain,
% 0.63/0.83      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.63/0.83         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.63/0.83          | ~ (r1_tarski @ X29 @ (k1_tops_1 @ X30 @ X31))
% 0.63/0.83          | (m2_connsp_2 @ X31 @ X30 @ X29)
% 0.63/0.83          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.63/0.83          | ~ (l1_pre_topc @ X30)
% 0.63/0.83          | ~ (v2_pre_topc @ X30))),
% 0.63/0.83      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.63/0.83  thf('41', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (~ (v2_pre_topc @ sk_A)
% 0.63/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.63/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.63/0.83          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.63/0.83          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.63/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.63/0.83  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('44', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.63/0.83          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.63/0.83          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.63/0.83      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.63/0.83  thf('45', plain,
% 0.63/0.83      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.63/0.83        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['38', '44'])).
% 0.63/0.83  thf('46', plain,
% 0.63/0.83      ((~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.63/0.83        | ~ (v2_pre_topc @ sk_A)
% 0.63/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.83        | ~ (l1_struct_0 @ sk_A)
% 0.63/0.83        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['37', '45'])).
% 0.63/0.83  thf('47', plain,
% 0.63/0.83      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf(t3_subset, axiom,
% 0.63/0.83    (![A:$i,B:$i]:
% 0.63/0.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.63/0.83  thf('48', plain,
% 0.63/0.83      (![X13 : $i, X14 : $i]:
% 0.63/0.83         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.63/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.63/0.83  thf('49', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.63/0.83      inference('sup-', [status(thm)], ['47', '48'])).
% 0.63/0.83  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf(dt_l1_pre_topc, axiom,
% 0.63/0.83    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.63/0.83  thf('53', plain,
% 0.63/0.83      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.63/0.83      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.63/0.83  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.83      inference('sup-', [status(thm)], ['52', '53'])).
% 0.63/0.83  thf('55', plain, ((m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_1)),
% 0.63/0.83      inference('demod', [status(thm)], ['46', '49', '50', '51', '54'])).
% 0.63/0.83  thf('56', plain,
% 0.63/0.83      (((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1)
% 0.63/0.83        | ~ (l1_struct_0 @ sk_A))),
% 0.63/0.83      inference('sup+', [status(thm)], ['1', '55'])).
% 0.63/0.83  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.83      inference('sup-', [status(thm)], ['52', '53'])).
% 0.63/0.83  thf('58', plain, ((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1)),
% 0.63/0.83      inference('demod', [status(thm)], ['56', '57'])).
% 0.63/0.83  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.63/0.83  
% 0.63/0.83  % SZS output end Refutation
% 0.63/0.83  
% 0.67/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
