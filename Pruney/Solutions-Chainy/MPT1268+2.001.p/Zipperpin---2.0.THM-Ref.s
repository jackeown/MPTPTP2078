%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IA3QcHzrq5

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:15 EST 2020

% Result     : Theorem 4.14s
% Output     : Refutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 811 expanded)
%              Number of leaves         :   35 ( 254 expanded)
%              Depth                    :   23
%              Number of atoms          : 1771 (9295 expanded)
%              Number of equality atoms :   86 ( 521 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t86_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( r1_tarski @ C @ B )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r1_tarski @ C @ B )
                      & ( v3_pre_topc @ C @ A ) )
                   => ( C = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tops_1])).

thf('0',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X34 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X34 @ sk_A )
      | ~ ( r1_tarski @ X34 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X34: $i] :
        ( ( X34 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X15 @ X14 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X34: $i] :
        ( ( X34 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_B ) )
   <= ! [X34: $i] :
        ( ( X34 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X34: $i] :
        ( ( X34 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X25 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('34',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X34: $i] :
        ( ( X34 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('40',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k1_tops_1 @ X33 @ X32 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X34: $i] :
        ( ( X34 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X34: $i] :
        ( ( X34 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ~ ! [X34: $i] :
          ( ( X34 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X34 @ sk_A )
          | ~ ( r1_tarski @ X34 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('50',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf('57',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['50'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X30 )
      | ~ ( r1_tarski @ X29 @ X31 )
      | ( r1_tarski @ X29 @ ( k1_tops_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ sk_C @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['64','66'])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf('69',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('70',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( sk_C
        = ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v2_tops_1 @ X32 @ X33 )
      | ( ( k1_tops_1 @ X33 @ X32 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('85',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_B )
      = sk_C )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('87',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
      = ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('91',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('93',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_B )
      = sk_C )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('94',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('98',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('102',plain,
    ( ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('104',plain,
    ( ( ( k3_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('107',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X15 @ X14 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('110',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k7_subset_1 @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k7_subset_1 @ sk_B @ sk_C @ X0 ) @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('114',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( k7_subset_1 @ sk_B @ sk_C @ X0 )
        = ( k4_xboole_0 @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['105','116'])).

thf('118',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_B )
        = ( k3_xboole_0 @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('121',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) )
        = ( k3_xboole_0 @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['104','123'])).

thf('125',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('126',plain,
    ( ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('128',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('130',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('131',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X30 )
      | ~ ( r1_tarski @ X29 @ X31 )
      | ( r1_tarski @ X29 @ ( k1_tops_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k1_tops_1 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X2 )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
      | ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_B ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['128','137'])).

thf('139',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('140',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X25 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('141',plain,
    ( ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('146',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('147',plain,
    ( ( ( k3_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['105','116'])).

thf('149',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['138','144','145','146','149'])).

thf('151',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','150'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('152',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('153',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['75','157'])).

thf('159',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('160',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','48','49','51','53','55','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IA3QcHzrq5
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 4.14/4.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.14/4.32  % Solved by: fo/fo7.sh
% 4.14/4.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.14/4.32  % done 8626 iterations in 3.863s
% 4.14/4.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.14/4.32  % SZS output start Refutation
% 4.14/4.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.14/4.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.14/4.32  thf(sk_B_type, type, sk_B: $i).
% 4.14/4.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.14/4.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.14/4.32  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.14/4.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.14/4.32  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 4.14/4.32  thf(sk_A_type, type, sk_A: $i).
% 4.14/4.32  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.14/4.32  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.14/4.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.14/4.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.14/4.32  thf(sk_C_type, type, sk_C: $i).
% 4.14/4.32  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 4.14/4.32  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.14/4.32  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 4.14/4.32  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 4.14/4.32  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.14/4.32  thf(t86_tops_1, conjecture,
% 4.14/4.32    (![A:$i]:
% 4.14/4.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.14/4.32       ( ![B:$i]:
% 4.14/4.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.14/4.32           ( ( v2_tops_1 @ B @ A ) <=>
% 4.14/4.32             ( ![C:$i]:
% 4.14/4.32               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.14/4.32                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 4.14/4.32                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 4.14/4.32  thf(zf_stmt_0, negated_conjecture,
% 4.14/4.32    (~( ![A:$i]:
% 4.14/4.32        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.14/4.32          ( ![B:$i]:
% 4.14/4.32            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.14/4.32              ( ( v2_tops_1 @ B @ A ) <=>
% 4.14/4.32                ( ![C:$i]:
% 4.14/4.32                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.14/4.32                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 4.14/4.32                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 4.14/4.32    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 4.14/4.32  thf('0', plain,
% 4.14/4.32      (![X34 : $i]:
% 4.14/4.32         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32          | ((X34) = (k1_xboole_0))
% 4.14/4.32          | ~ (v3_pre_topc @ X34 @ sk_A)
% 4.14/4.32          | ~ (r1_tarski @ X34 @ sk_B)
% 4.14/4.32          | (v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('1', plain,
% 4.14/4.32      ((![X34 : $i]:
% 4.14/4.32          (((X34) = (k1_xboole_0))
% 4.14/4.32           | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32           | ~ (v3_pre_topc @ X34 @ sk_A)
% 4.14/4.32           | ~ (r1_tarski @ X34 @ sk_B))) | 
% 4.14/4.32       ((v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('split', [status(esa)], ['0'])).
% 4.14/4.32  thf('2', plain,
% 4.14/4.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf(t44_tops_1, axiom,
% 4.14/4.32    (![A:$i]:
% 4.14/4.32     ( ( l1_pre_topc @ A ) =>
% 4.14/4.32       ( ![B:$i]:
% 4.14/4.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.14/4.32           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 4.14/4.32  thf('3', plain,
% 4.14/4.32      (![X27 : $i, X28 : $i]:
% 4.14/4.32         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 4.14/4.32          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ X27)
% 4.14/4.32          | ~ (l1_pre_topc @ X28))),
% 4.14/4.32      inference('cnf', [status(esa)], [t44_tops_1])).
% 4.14/4.32  thf('4', plain,
% 4.14/4.32      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 4.14/4.32      inference('sup-', [status(thm)], ['2', '3'])).
% 4.14/4.32  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('6', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.14/4.32      inference('demod', [status(thm)], ['4', '5'])).
% 4.14/4.32  thf(t28_xboole_1, axiom,
% 4.14/4.32    (![A:$i,B:$i]:
% 4.14/4.32     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.14/4.32  thf('7', plain,
% 4.14/4.32      (![X7 : $i, X8 : $i]:
% 4.14/4.32         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.14/4.32      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.14/4.32  thf('8', plain,
% 4.14/4.32      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 4.14/4.32         = (k1_tops_1 @ sk_A @ sk_B))),
% 4.14/4.32      inference('sup-', [status(thm)], ['6', '7'])).
% 4.14/4.32  thf(commutativity_k2_tarski, axiom,
% 4.14/4.32    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.14/4.32  thf('9', plain,
% 4.14/4.32      (![X12 : $i, X13 : $i]:
% 4.14/4.32         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 4.14/4.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.14/4.32  thf(t12_setfam_1, axiom,
% 4.14/4.32    (![A:$i,B:$i]:
% 4.14/4.32     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.14/4.32  thf('10', plain,
% 4.14/4.32      (![X20 : $i, X21 : $i]:
% 4.14/4.32         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 4.14/4.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.14/4.32  thf('11', plain,
% 4.14/4.32      (![X0 : $i, X1 : $i]:
% 4.14/4.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 4.14/4.32      inference('sup+', [status(thm)], ['9', '10'])).
% 4.14/4.32  thf('12', plain,
% 4.14/4.32      (![X20 : $i, X21 : $i]:
% 4.14/4.32         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 4.14/4.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.14/4.32  thf('13', plain,
% 4.14/4.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.14/4.32      inference('sup+', [status(thm)], ['11', '12'])).
% 4.14/4.32  thf('14', plain,
% 4.14/4.32      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 4.14/4.32         = (k1_tops_1 @ sk_A @ sk_B))),
% 4.14/4.32      inference('demod', [status(thm)], ['8', '13'])).
% 4.14/4.32  thf(t48_xboole_1, axiom,
% 4.14/4.32    (![A:$i,B:$i]:
% 4.14/4.32     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.14/4.32  thf('15', plain,
% 4.14/4.32      (![X10 : $i, X11 : $i]:
% 4.14/4.32         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 4.14/4.32           = (k3_xboole_0 @ X10 @ X11))),
% 4.14/4.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.14/4.32  thf('16', plain,
% 4.14/4.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf(dt_k7_subset_1, axiom,
% 4.14/4.32    (![A:$i,B:$i,C:$i]:
% 4.14/4.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.14/4.32       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.14/4.32  thf('17', plain,
% 4.14/4.32      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.14/4.32         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 4.14/4.32          | (m1_subset_1 @ (k7_subset_1 @ X15 @ X14 @ X16) @ 
% 4.14/4.32             (k1_zfmisc_1 @ X15)))),
% 4.14/4.32      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 4.14/4.32  thf('18', plain,
% 4.14/4.32      (![X0 : $i]:
% 4.14/4.32         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 4.14/4.32          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('sup-', [status(thm)], ['16', '17'])).
% 4.14/4.32  thf('19', plain,
% 4.14/4.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf(redefinition_k7_subset_1, axiom,
% 4.14/4.32    (![A:$i,B:$i,C:$i]:
% 4.14/4.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.14/4.32       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 4.14/4.32  thf('20', plain,
% 4.14/4.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.14/4.32         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 4.14/4.32          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 4.14/4.32      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.14/4.32  thf('21', plain,
% 4.14/4.32      (![X0 : $i]:
% 4.14/4.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 4.14/4.32           = (k4_xboole_0 @ sk_B @ X0))),
% 4.14/4.32      inference('sup-', [status(thm)], ['19', '20'])).
% 4.14/4.32  thf('22', plain,
% 4.14/4.32      (![X0 : $i]:
% 4.14/4.32         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 4.14/4.32          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('demod', [status(thm)], ['18', '21'])).
% 4.14/4.32  thf(t3_subset, axiom,
% 4.14/4.32    (![A:$i,B:$i]:
% 4.14/4.32     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.14/4.32  thf('23', plain,
% 4.14/4.32      (![X22 : $i, X23 : $i]:
% 4.14/4.32         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 4.14/4.32      inference('cnf', [status(esa)], [t3_subset])).
% 4.14/4.32  thf('24', plain,
% 4.14/4.32      (![X0 : $i]:
% 4.14/4.32         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 4.14/4.32      inference('sup-', [status(thm)], ['22', '23'])).
% 4.14/4.32  thf('25', plain,
% 4.14/4.32      (![X0 : $i]:
% 4.14/4.32         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 4.14/4.32      inference('sup+', [status(thm)], ['15', '24'])).
% 4.14/4.32  thf('26', plain,
% 4.14/4.32      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 4.14/4.32      inference('sup+', [status(thm)], ['14', '25'])).
% 4.14/4.32  thf('27', plain,
% 4.14/4.32      (![X22 : $i, X24 : $i]:
% 4.14/4.32         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 4.14/4.32      inference('cnf', [status(esa)], [t3_subset])).
% 4.14/4.32  thf('28', plain,
% 4.14/4.32      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.14/4.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('sup-', [status(thm)], ['26', '27'])).
% 4.14/4.32  thf('29', plain,
% 4.14/4.32      ((![X34 : $i]:
% 4.14/4.32          (((X34) = (k1_xboole_0))
% 4.14/4.32           | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32           | ~ (v3_pre_topc @ X34 @ sk_A)
% 4.14/4.32           | ~ (r1_tarski @ X34 @ sk_B)))
% 4.14/4.32         <= ((![X34 : $i]:
% 4.14/4.32                (((X34) = (k1_xboole_0))
% 4.14/4.32                 | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32                 | ~ (v3_pre_topc @ X34 @ sk_A)
% 4.14/4.32                 | ~ (r1_tarski @ X34 @ sk_B))))),
% 4.14/4.32      inference('split', [status(esa)], ['0'])).
% 4.14/4.32  thf('30', plain,
% 4.14/4.32      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 4.14/4.32         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.14/4.32         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 4.14/4.32         <= ((![X34 : $i]:
% 4.14/4.32                (((X34) = (k1_xboole_0))
% 4.14/4.32                 | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32                 | ~ (v3_pre_topc @ X34 @ sk_A)
% 4.14/4.32                 | ~ (r1_tarski @ X34 @ sk_B))))),
% 4.14/4.32      inference('sup-', [status(thm)], ['28', '29'])).
% 4.14/4.32  thf('31', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.14/4.32      inference('demod', [status(thm)], ['4', '5'])).
% 4.14/4.32  thf('32', plain,
% 4.14/4.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf(fc9_tops_1, axiom,
% 4.14/4.32    (![A:$i,B:$i]:
% 4.14/4.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.14/4.32         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.14/4.32       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 4.14/4.32  thf('33', plain,
% 4.14/4.32      (![X25 : $i, X26 : $i]:
% 4.14/4.32         (~ (l1_pre_topc @ X25)
% 4.14/4.32          | ~ (v2_pre_topc @ X25)
% 4.14/4.32          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 4.14/4.32          | (v3_pre_topc @ (k1_tops_1 @ X25 @ X26) @ X25))),
% 4.14/4.32      inference('cnf', [status(esa)], [fc9_tops_1])).
% 4.14/4.32  thf('34', plain,
% 4.14/4.32      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.14/4.32        | ~ (v2_pre_topc @ sk_A)
% 4.14/4.32        | ~ (l1_pre_topc @ sk_A))),
% 4.14/4.32      inference('sup-', [status(thm)], ['32', '33'])).
% 4.14/4.32  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('37', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 4.14/4.32      inference('demod', [status(thm)], ['34', '35', '36'])).
% 4.14/4.32  thf('38', plain,
% 4.14/4.32      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 4.14/4.32         <= ((![X34 : $i]:
% 4.14/4.32                (((X34) = (k1_xboole_0))
% 4.14/4.32                 | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32                 | ~ (v3_pre_topc @ X34 @ sk_A)
% 4.14/4.32                 | ~ (r1_tarski @ X34 @ sk_B))))),
% 4.14/4.32      inference('demod', [status(thm)], ['30', '31', '37'])).
% 4.14/4.32  thf('39', plain,
% 4.14/4.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf(t84_tops_1, axiom,
% 4.14/4.32    (![A:$i]:
% 4.14/4.32     ( ( l1_pre_topc @ A ) =>
% 4.14/4.32       ( ![B:$i]:
% 4.14/4.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.14/4.32           ( ( v2_tops_1 @ B @ A ) <=>
% 4.14/4.32             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 4.14/4.32  thf('40', plain,
% 4.14/4.32      (![X32 : $i, X33 : $i]:
% 4.14/4.32         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 4.14/4.32          | ((k1_tops_1 @ X33 @ X32) != (k1_xboole_0))
% 4.14/4.32          | (v2_tops_1 @ X32 @ X33)
% 4.14/4.32          | ~ (l1_pre_topc @ X33))),
% 4.14/4.32      inference('cnf', [status(esa)], [t84_tops_1])).
% 4.14/4.32  thf('41', plain,
% 4.14/4.32      ((~ (l1_pre_topc @ sk_A)
% 4.14/4.32        | (v2_tops_1 @ sk_B @ sk_A)
% 4.14/4.32        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 4.14/4.32      inference('sup-', [status(thm)], ['39', '40'])).
% 4.14/4.32  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('43', plain,
% 4.14/4.32      (((v2_tops_1 @ sk_B @ sk_A)
% 4.14/4.32        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 4.14/4.32      inference('demod', [status(thm)], ['41', '42'])).
% 4.14/4.32  thf('44', plain,
% 4.14/4.32      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 4.14/4.32         <= ((![X34 : $i]:
% 4.14/4.32                (((X34) = (k1_xboole_0))
% 4.14/4.32                 | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32                 | ~ (v3_pre_topc @ X34 @ sk_A)
% 4.14/4.32                 | ~ (r1_tarski @ X34 @ sk_B))))),
% 4.14/4.32      inference('sup-', [status(thm)], ['38', '43'])).
% 4.14/4.32  thf('45', plain,
% 4.14/4.32      (((v2_tops_1 @ sk_B @ sk_A))
% 4.14/4.32         <= ((![X34 : $i]:
% 4.14/4.32                (((X34) = (k1_xboole_0))
% 4.14/4.32                 | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32                 | ~ (v3_pre_topc @ X34 @ sk_A)
% 4.14/4.32                 | ~ (r1_tarski @ X34 @ sk_B))))),
% 4.14/4.32      inference('simplify', [status(thm)], ['44'])).
% 4.14/4.32  thf('46', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('47', plain,
% 4.14/4.32      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 4.14/4.32      inference('split', [status(esa)], ['46'])).
% 4.14/4.32  thf('48', plain,
% 4.14/4.32      (~
% 4.14/4.32       (![X34 : $i]:
% 4.14/4.32          (((X34) = (k1_xboole_0))
% 4.14/4.32           | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32           | ~ (v3_pre_topc @ X34 @ sk_A)
% 4.14/4.32           | ~ (r1_tarski @ X34 @ sk_B))) | 
% 4.14/4.32       ((v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('sup-', [status(thm)], ['45', '47'])).
% 4.14/4.32  thf('49', plain,
% 4.14/4.32      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('split', [status(esa)], ['46'])).
% 4.14/4.32  thf('50', plain,
% 4.14/4.32      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('51', plain,
% 4.14/4.32      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('split', [status(esa)], ['50'])).
% 4.14/4.32  thf('52', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('53', plain,
% 4.14/4.32      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('split', [status(esa)], ['52'])).
% 4.14/4.32  thf('54', plain,
% 4.14/4.32      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('55', plain,
% 4.14/4.32      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 4.14/4.32       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('split', [status(esa)], ['54'])).
% 4.14/4.32  thf('56', plain,
% 4.14/4.32      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.14/4.32         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('split', [status(esa)], ['54'])).
% 4.14/4.32  thf('57', plain,
% 4.14/4.32      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 4.14/4.32      inference('split', [status(esa)], ['50'])).
% 4.14/4.32  thf('58', plain,
% 4.14/4.32      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.14/4.32         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('split', [status(esa)], ['54'])).
% 4.14/4.32  thf(t56_tops_1, axiom,
% 4.14/4.32    (![A:$i]:
% 4.14/4.32     ( ( l1_pre_topc @ A ) =>
% 4.14/4.32       ( ![B:$i]:
% 4.14/4.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.14/4.32           ( ![C:$i]:
% 4.14/4.32             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.14/4.32               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 4.14/4.32                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 4.14/4.32  thf('59', plain,
% 4.14/4.32      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.14/4.32         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 4.14/4.32          | ~ (v3_pre_topc @ X29 @ X30)
% 4.14/4.32          | ~ (r1_tarski @ X29 @ X31)
% 4.14/4.32          | (r1_tarski @ X29 @ (k1_tops_1 @ X30 @ X31))
% 4.14/4.32          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 4.14/4.32          | ~ (l1_pre_topc @ X30))),
% 4.14/4.32      inference('cnf', [status(esa)], [t56_tops_1])).
% 4.14/4.32  thf('60', plain,
% 4.14/4.32      ((![X0 : $i]:
% 4.14/4.32          (~ (l1_pre_topc @ sk_A)
% 4.14/4.32           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 4.14/4.32           | ~ (r1_tarski @ sk_C @ X0)
% 4.14/4.32           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 4.14/4.32         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('sup-', [status(thm)], ['58', '59'])).
% 4.14/4.32  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('62', plain,
% 4.14/4.32      ((![X0 : $i]:
% 4.14/4.32          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.32           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 4.14/4.32           | ~ (r1_tarski @ sk_C @ X0)
% 4.14/4.32           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 4.14/4.32         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('demod', [status(thm)], ['60', '61'])).
% 4.14/4.32  thf('63', plain,
% 4.14/4.32      ((![X0 : $i]:
% 4.14/4.32          (~ (r1_tarski @ sk_C @ X0)
% 4.14/4.32           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 4.14/4.32           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 4.14/4.32         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.14/4.32             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('sup-', [status(thm)], ['57', '62'])).
% 4.14/4.32  thf('64', plain,
% 4.14/4.32      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C))
% 4.14/4.32         | ~ (r1_tarski @ sk_C @ sk_C)))
% 4.14/4.32         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.14/4.32             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('sup-', [status(thm)], ['56', '63'])).
% 4.14/4.32  thf(d10_xboole_0, axiom,
% 4.14/4.32    (![A:$i,B:$i]:
% 4.14/4.32     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.14/4.32  thf('65', plain,
% 4.14/4.32      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.14/4.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.14/4.32  thf('66', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.14/4.32      inference('simplify', [status(thm)], ['65'])).
% 4.14/4.32  thf('67', plain,
% 4.14/4.32      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C)))
% 4.14/4.32         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.14/4.32             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('demod', [status(thm)], ['64', '66'])).
% 4.14/4.32  thf('68', plain,
% 4.14/4.32      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.14/4.32         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('split', [status(esa)], ['54'])).
% 4.14/4.32  thf('69', plain,
% 4.14/4.32      (![X27 : $i, X28 : $i]:
% 4.14/4.32         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 4.14/4.32          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ X27)
% 4.14/4.32          | ~ (l1_pre_topc @ X28))),
% 4.14/4.32      inference('cnf', [status(esa)], [t44_tops_1])).
% 4.14/4.32  thf('70', plain,
% 4.14/4.32      (((~ (l1_pre_topc @ sk_A)
% 4.14/4.32         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 4.14/4.32         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('sup-', [status(thm)], ['68', '69'])).
% 4.14/4.32  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('72', plain,
% 4.14/4.32      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 4.14/4.32         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('demod', [status(thm)], ['70', '71'])).
% 4.14/4.32  thf('73', plain,
% 4.14/4.32      (![X0 : $i, X2 : $i]:
% 4.14/4.32         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.14/4.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.14/4.32  thf('74', plain,
% 4.14/4.32      (((~ (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C))
% 4.14/4.32         | ((sk_C) = (k1_tops_1 @ sk_A @ sk_C))))
% 4.14/4.32         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('sup-', [status(thm)], ['72', '73'])).
% 4.14/4.32  thf('75', plain,
% 4.14/4.32      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C)))
% 4.14/4.32         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.14/4.32             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.32      inference('sup-', [status(thm)], ['67', '74'])).
% 4.14/4.32  thf('76', plain,
% 4.14/4.32      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 4.14/4.32      inference('split', [status(esa)], ['0'])).
% 4.14/4.32  thf('77', plain,
% 4.14/4.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('78', plain,
% 4.14/4.32      (![X32 : $i, X33 : $i]:
% 4.14/4.32         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 4.14/4.32          | ~ (v2_tops_1 @ X32 @ X33)
% 4.14/4.32          | ((k1_tops_1 @ X33 @ X32) = (k1_xboole_0))
% 4.14/4.32          | ~ (l1_pre_topc @ X33))),
% 4.14/4.32      inference('cnf', [status(esa)], [t84_tops_1])).
% 4.14/4.32  thf('79', plain,
% 4.14/4.32      ((~ (l1_pre_topc @ sk_A)
% 4.14/4.32        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 4.14/4.32        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('sup-', [status(thm)], ['77', '78'])).
% 4.14/4.32  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('81', plain,
% 4.14/4.32      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 4.14/4.32        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.14/4.32      inference('demod', [status(thm)], ['79', '80'])).
% 4.14/4.32  thf('82', plain,
% 4.14/4.32      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 4.14/4.32         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 4.14/4.32      inference('sup-', [status(thm)], ['76', '81'])).
% 4.14/4.32  thf('83', plain,
% 4.14/4.32      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('split', [status(esa)], ['46'])).
% 4.14/4.32  thf('84', plain,
% 4.14/4.32      (![X7 : $i, X8 : $i]:
% 4.14/4.32         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.14/4.32      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.14/4.32  thf('85', plain,
% 4.14/4.32      ((((k3_xboole_0 @ sk_C @ sk_B) = (sk_C)))
% 4.14/4.32         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('sup-', [status(thm)], ['83', '84'])).
% 4.14/4.32  thf('86', plain,
% 4.14/4.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.14/4.32      inference('sup+', [status(thm)], ['11', '12'])).
% 4.14/4.32  thf(t100_xboole_1, axiom,
% 4.14/4.32    (![A:$i,B:$i]:
% 4.14/4.32     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.14/4.32  thf('87', plain,
% 4.14/4.32      (![X3 : $i, X4 : $i]:
% 4.14/4.32         ((k4_xboole_0 @ X3 @ X4)
% 4.14/4.32           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 4.14/4.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.14/4.32  thf('88', plain,
% 4.14/4.32      (![X0 : $i, X1 : $i]:
% 4.14/4.32         ((k4_xboole_0 @ X0 @ X1)
% 4.14/4.32           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.14/4.32      inference('sup+', [status(thm)], ['86', '87'])).
% 4.14/4.32  thf('89', plain,
% 4.14/4.32      ((((k4_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ sk_C)))
% 4.14/4.32         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('sup+', [status(thm)], ['85', '88'])).
% 4.14/4.32  thf('90', plain,
% 4.14/4.32      (![X10 : $i, X11 : $i]:
% 4.14/4.32         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 4.14/4.32           = (k3_xboole_0 @ X10 @ X11))),
% 4.14/4.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.14/4.32  thf('91', plain,
% 4.14/4.32      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C))
% 4.14/4.32          = (k3_xboole_0 @ sk_B @ sk_C)))
% 4.14/4.32         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('sup+', [status(thm)], ['89', '90'])).
% 4.14/4.32  thf('92', plain,
% 4.14/4.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.14/4.32      inference('sup+', [status(thm)], ['11', '12'])).
% 4.14/4.32  thf('93', plain,
% 4.14/4.32      ((((k3_xboole_0 @ sk_C @ sk_B) = (sk_C)))
% 4.14/4.32         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('sup-', [status(thm)], ['83', '84'])).
% 4.14/4.32  thf('94', plain,
% 4.14/4.32      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C)) = (sk_C)))
% 4.14/4.32         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('demod', [status(thm)], ['91', '92', '93'])).
% 4.14/4.32  thf('95', plain,
% 4.14/4.32      (![X0 : $i]:
% 4.14/4.32         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 4.14/4.32          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.32      inference('demod', [status(thm)], ['18', '21'])).
% 4.14/4.32  thf('96', plain,
% 4.14/4.32      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.14/4.32         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('sup+', [status(thm)], ['94', '95'])).
% 4.14/4.32  thf('97', plain,
% 4.14/4.32      (![X27 : $i, X28 : $i]:
% 4.14/4.32         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 4.14/4.32          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ X27)
% 4.14/4.32          | ~ (l1_pre_topc @ X28))),
% 4.14/4.32      inference('cnf', [status(esa)], [t44_tops_1])).
% 4.14/4.32  thf('98', plain,
% 4.14/4.32      (((~ (l1_pre_topc @ sk_A)
% 4.14/4.32         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 4.14/4.32         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('sup-', [status(thm)], ['96', '97'])).
% 4.14/4.32  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 4.14/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.32  thf('100', plain,
% 4.14/4.32      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 4.14/4.32         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('demod', [status(thm)], ['98', '99'])).
% 4.14/4.32  thf('101', plain,
% 4.14/4.32      (![X7 : $i, X8 : $i]:
% 4.14/4.32         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.14/4.32      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.14/4.32  thf('102', plain,
% 4.14/4.32      ((((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 4.14/4.32          = (k1_tops_1 @ sk_A @ sk_C)))
% 4.14/4.32         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.32      inference('sup-', [status(thm)], ['100', '101'])).
% 4.14/4.33  thf('103', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.14/4.33      inference('sup+', [status(thm)], ['11', '12'])).
% 4.14/4.33  thf('104', plain,
% 4.14/4.33      ((((k3_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ sk_C))
% 4.14/4.33          = (k1_tops_1 @ sk_A @ sk_C)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['102', '103'])).
% 4.14/4.33  thf('105', plain,
% 4.14/4.33      (![X10 : $i, X11 : $i]:
% 4.14/4.33         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 4.14/4.33           = (k3_xboole_0 @ X10 @ X11))),
% 4.14/4.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.14/4.33  thf('106', plain,
% 4.14/4.33      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('split', [status(esa)], ['46'])).
% 4.14/4.33  thf('107', plain,
% 4.14/4.33      (![X22 : $i, X24 : $i]:
% 4.14/4.33         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 4.14/4.33      inference('cnf', [status(esa)], [t3_subset])).
% 4.14/4.33  thf('108', plain,
% 4.14/4.33      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['106', '107'])).
% 4.14/4.33  thf('109', plain,
% 4.14/4.33      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 4.14/4.33          | (m1_subset_1 @ (k7_subset_1 @ X15 @ X14 @ X16) @ 
% 4.14/4.33             (k1_zfmisc_1 @ X15)))),
% 4.14/4.33      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 4.14/4.33  thf('110', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          (m1_subset_1 @ (k7_subset_1 @ sk_B @ sk_C @ X0) @ 
% 4.14/4.33           (k1_zfmisc_1 @ sk_B)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['108', '109'])).
% 4.14/4.33  thf('111', plain,
% 4.14/4.33      (![X22 : $i, X23 : $i]:
% 4.14/4.33         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 4.14/4.33      inference('cnf', [status(esa)], [t3_subset])).
% 4.14/4.33  thf('112', plain,
% 4.14/4.33      ((![X0 : $i]: (r1_tarski @ (k7_subset_1 @ sk_B @ sk_C @ X0) @ sk_B))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['110', '111'])).
% 4.14/4.33  thf('113', plain,
% 4.14/4.33      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['106', '107'])).
% 4.14/4.33  thf('114', plain,
% 4.14/4.33      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 4.14/4.33          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 4.14/4.33      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.14/4.33  thf('115', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          ((k7_subset_1 @ sk_B @ sk_C @ X0) = (k4_xboole_0 @ sk_C @ X0)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['113', '114'])).
% 4.14/4.33  thf('116', plain,
% 4.14/4.33      ((![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ sk_B))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['112', '115'])).
% 4.14/4.33  thf('117', plain,
% 4.14/4.33      ((![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_B))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup+', [status(thm)], ['105', '116'])).
% 4.14/4.33  thf('118', plain,
% 4.14/4.33      (![X7 : $i, X8 : $i]:
% 4.14/4.33         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.14/4.33      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.14/4.33  thf('119', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          ((k3_xboole_0 @ (k3_xboole_0 @ sk_C @ X0) @ sk_B)
% 4.14/4.33            = (k3_xboole_0 @ sk_C @ X0)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['117', '118'])).
% 4.14/4.33  thf('120', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.14/4.33      inference('sup+', [status(thm)], ['11', '12'])).
% 4.14/4.33  thf('121', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0))
% 4.14/4.33            = (k3_xboole_0 @ sk_C @ X0)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['119', '120'])).
% 4.14/4.33  thf('122', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 4.14/4.33      inference('sup+', [status(thm)], ['15', '24'])).
% 4.14/4.33  thf('123', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup+', [status(thm)], ['121', '122'])).
% 4.14/4.33  thf('124', plain,
% 4.14/4.33      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup+', [status(thm)], ['104', '123'])).
% 4.14/4.33  thf('125', plain,
% 4.14/4.33      (![X7 : $i, X8 : $i]:
% 4.14/4.33         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.14/4.33      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.14/4.33  thf('126', plain,
% 4.14/4.33      ((((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 4.14/4.33          = (k1_tops_1 @ sk_A @ sk_C)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['124', '125'])).
% 4.14/4.33  thf('127', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.14/4.33      inference('sup+', [status(thm)], ['11', '12'])).
% 4.14/4.33  thf('128', plain,
% 4.14/4.33      ((((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C))
% 4.14/4.33          = (k1_tops_1 @ sk_A @ sk_C)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['126', '127'])).
% 4.14/4.33  thf('129', plain,
% 4.14/4.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf(t17_xboole_1, axiom,
% 4.14/4.33    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 4.14/4.33  thf('130', plain,
% 4.14/4.33      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 4.14/4.33      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.14/4.33  thf('131', plain,
% 4.14/4.33      (![X22 : $i, X24 : $i]:
% 4.14/4.33         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 4.14/4.33      inference('cnf', [status(esa)], [t3_subset])).
% 4.14/4.33  thf('132', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.14/4.33      inference('sup-', [status(thm)], ['130', '131'])).
% 4.14/4.33  thf('133', plain,
% 4.14/4.33      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 4.14/4.33          | ~ (v3_pre_topc @ X29 @ X30)
% 4.14/4.33          | ~ (r1_tarski @ X29 @ X31)
% 4.14/4.33          | (r1_tarski @ X29 @ (k1_tops_1 @ X30 @ X31))
% 4.14/4.33          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 4.14/4.33          | ~ (l1_pre_topc @ X30))),
% 4.14/4.33      inference('cnf', [status(esa)], [t56_tops_1])).
% 4.14/4.33  thf('134', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.14/4.33         (~ (l1_pre_topc @ X0)
% 4.14/4.33          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.14/4.33          | (r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 4.14/4.33             (k1_tops_1 @ X0 @ X2))
% 4.14/4.33          | ~ (r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X2)
% 4.14/4.33          | ~ (v3_pre_topc @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 4.14/4.33      inference('sup-', [status(thm)], ['132', '133'])).
% 4.14/4.33  thf('135', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         (~ (v3_pre_topc @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ sk_A)
% 4.14/4.33          | ~ (r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ sk_B)
% 4.14/4.33          | (r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 4.14/4.33             (k1_tops_1 @ sk_A @ sk_B))
% 4.14/4.33          | ~ (l1_pre_topc @ sk_A))),
% 4.14/4.33      inference('sup-', [status(thm)], ['129', '134'])).
% 4.14/4.33  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('137', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         (~ (v3_pre_topc @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ sk_A)
% 4.14/4.33          | ~ (r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ sk_B)
% 4.14/4.33          | (r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 4.14/4.33             (k1_tops_1 @ sk_A @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['135', '136'])).
% 4.14/4.33  thf('138', plain,
% 4.14/4.33      (((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 4.14/4.33         | (r1_tarski @ 
% 4.14/4.33            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 4.14/4.33            (k1_tops_1 @ sk_A @ sk_B))
% 4.14/4.33         | ~ (r1_tarski @ 
% 4.14/4.33              (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 4.14/4.33              sk_B)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['128', '137'])).
% 4.14/4.33  thf('139', plain,
% 4.14/4.33      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup+', [status(thm)], ['94', '95'])).
% 4.14/4.33  thf('140', plain,
% 4.14/4.33      (![X25 : $i, X26 : $i]:
% 4.14/4.33         (~ (l1_pre_topc @ X25)
% 4.14/4.33          | ~ (v2_pre_topc @ X25)
% 4.14/4.33          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 4.14/4.33          | (v3_pre_topc @ (k1_tops_1 @ X25 @ X26) @ X25))),
% 4.14/4.33      inference('cnf', [status(esa)], [fc9_tops_1])).
% 4.14/4.33  thf('141', plain,
% 4.14/4.33      ((((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 4.14/4.33         | ~ (v2_pre_topc @ sk_A)
% 4.14/4.33         | ~ (l1_pre_topc @ sk_A))) <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['139', '140'])).
% 4.14/4.33  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('144', plain,
% 4.14/4.33      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['141', '142', '143'])).
% 4.14/4.33  thf('145', plain,
% 4.14/4.33      ((((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C))
% 4.14/4.33          = (k1_tops_1 @ sk_A @ sk_C)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['126', '127'])).
% 4.14/4.33  thf('146', plain,
% 4.14/4.33      ((((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C))
% 4.14/4.33          = (k1_tops_1 @ sk_A @ sk_C)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['126', '127'])).
% 4.14/4.33  thf('147', plain,
% 4.14/4.33      ((((k3_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ sk_C))
% 4.14/4.33          = (k1_tops_1 @ sk_A @ sk_C)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['102', '103'])).
% 4.14/4.33  thf('148', plain,
% 4.14/4.33      ((![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_B))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup+', [status(thm)], ['105', '116'])).
% 4.14/4.33  thf('149', plain,
% 4.14/4.33      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_B))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup+', [status(thm)], ['147', '148'])).
% 4.14/4.33  thf('150', plain,
% 4.14/4.33      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.14/4.33         <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('demod', [status(thm)], ['138', '144', '145', '146', '149'])).
% 4.14/4.33  thf('151', plain,
% 4.14/4.33      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ k1_xboole_0))
% 4.14/4.33         <= (((v2_tops_1 @ sk_B @ sk_A)) & ((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup+', [status(thm)], ['82', '150'])).
% 4.14/4.33  thf(t2_boole, axiom,
% 4.14/4.33    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 4.14/4.33  thf('152', plain,
% 4.14/4.33      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 4.14/4.33      inference('cnf', [status(esa)], [t2_boole])).
% 4.14/4.33  thf('153', plain,
% 4.14/4.33      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 4.14/4.33      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.14/4.33  thf('154', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.14/4.33      inference('sup+', [status(thm)], ['152', '153'])).
% 4.14/4.33  thf('155', plain,
% 4.14/4.33      (![X0 : $i, X2 : $i]:
% 4.14/4.33         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.14/4.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.14/4.33  thf('156', plain,
% 4.14/4.33      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['154', '155'])).
% 4.14/4.33  thf('157', plain,
% 4.14/4.33      ((((k1_tops_1 @ sk_A @ sk_C) = (k1_xboole_0)))
% 4.14/4.33         <= (((v2_tops_1 @ sk_B @ sk_A)) & ((r1_tarski @ sk_C @ sk_B)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['151', '156'])).
% 4.14/4.33  thf('158', plain,
% 4.14/4.33      ((((sk_C) = (k1_xboole_0)))
% 4.14/4.33         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 4.14/4.33             ((r1_tarski @ sk_C @ sk_B)) & 
% 4.14/4.33             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.14/4.33             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.33      inference('sup+', [status(thm)], ['75', '157'])).
% 4.14/4.33  thf('159', plain,
% 4.14/4.33      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 4.14/4.33      inference('split', [status(esa)], ['52'])).
% 4.14/4.33  thf('160', plain,
% 4.14/4.33      ((((sk_C) != (sk_C)))
% 4.14/4.33         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 4.14/4.33             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 4.14/4.33             ((r1_tarski @ sk_C @ sk_B)) & 
% 4.14/4.33             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.14/4.33             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.14/4.33      inference('sup-', [status(thm)], ['158', '159'])).
% 4.14/4.33  thf('161', plain,
% 4.14/4.33      (~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 4.14/4.33       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 4.14/4.33       ~ ((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 4.14/4.33       (((sk_C) = (k1_xboole_0)))),
% 4.14/4.33      inference('simplify', [status(thm)], ['160'])).
% 4.14/4.33  thf('162', plain, ($false),
% 4.14/4.33      inference('sat_resolution*', [status(thm)],
% 4.14/4.33                ['1', '48', '49', '51', '53', '55', '161'])).
% 4.14/4.33  
% 4.14/4.33  % SZS output end Refutation
% 4.14/4.33  
% 4.14/4.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
