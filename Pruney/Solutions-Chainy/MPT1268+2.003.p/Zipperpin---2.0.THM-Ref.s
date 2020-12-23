%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TCA37k0y5v

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 183 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  967 (2500 expanded)
%              Number of equality atoms :   51 ( 115 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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

thf('0',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X32 @ sk_A )
      | ~ ( r1_tarski @ X32 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tops_1 @ X30 @ X31 )
      | ( ( k1_tops_1 @ X31 @ X30 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

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

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X27 @ X28 )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r1_tarski @ X27 @ ( k1_tops_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('33',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ X25 ) @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf('59',plain,
    ( ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_B ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('60',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X23 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('64',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k1_tops_1 @ X31 @ X30 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ~ ! [X32: $i] :
          ( ( X32 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X32 @ sk_A )
          | ~ ( r1_tarski @ X32 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','34','35','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TCA37k0y5v
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 417 iterations in 0.083s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.53  thf(t86_tops_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.53             ( ![C:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.53                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53              ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.53                ( ![C:$i]:
% 0.20/0.53                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.53                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.20/0.53  thf('0', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('4', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.53       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X32 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ((X32) = (k1_xboole_0))
% 0.20/0.53          | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.20/0.53          | ~ (r1_tarski @ X32 @ sk_B)
% 0.20/0.53          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t84_tops_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.53             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.20/0.53          | ~ (v2_tops_1 @ X30 @ X31)
% 0.20/0.53          | ((k1_tops_1 @ X31 @ X30) = (k1_xboole_0))
% 0.20/0.53          | ~ (l1_pre_topc @ X31))),
% 0.20/0.53      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('split', [status(esa)], ['6'])).
% 0.20/0.53  thf(t56_tops_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.53                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.53          | ~ (v3_pre_topc @ X27 @ X28)
% 0.20/0.53          | ~ (r1_tarski @ X27 @ X29)
% 0.20/0.53          | (r1_tarski @ X27 @ (k1_tops_1 @ X28 @ X29))
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.53          | ~ (l1_pre_topc @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (l1_pre_topc @ sk_A)
% 0.20/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.53           | ~ (r1_tarski @ sk_C @ X0)
% 0.20/0.53           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.20/0.53         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.53           | ~ (r1_tarski @ sk_C @ X0)
% 0.20/0.53           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.20/0.53         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r1_tarski @ sk_C @ X0)
% 0.20/0.53           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.53         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.53         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.20/0.53         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.53             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '25'])).
% 0.20/0.53  thf(l32_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X2 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.53             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.53         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.53             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.53             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '28'])).
% 0.20/0.53  thf(t3_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('30', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.53         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.53             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.53             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['4'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((sk_C) != (sk_C)))
% 0.20/0.53         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.20/0.53             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.53             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.53             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.20/0.53       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.53       ~ ((r1_tarski @ sk_C @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.20/0.53       (((sk_C) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((![X32 : $i]:
% 0.20/0.53          (((X32) = (k1_xboole_0))
% 0.20/0.53           | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53           | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.20/0.53           | ~ (r1_tarski @ X32 @ sk_B))) | 
% 0.20/0.53       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['8'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t44_tops_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.53          | (r1_tarski @ (k1_tops_1 @ X26 @ X25) @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf(t28_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.53         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf(commutativity_k2_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.53  thf(t12_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i]:
% 0.20/0.53         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 0.20/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i]:
% 0.20/0.53         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 0.20/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.53         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k9_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k9_subset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X15))
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.53           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['52', '55'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['49', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['48', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((![X32 : $i]:
% 0.20/0.53          (((X32) = (k1_xboole_0))
% 0.20/0.53           | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53           | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.20/0.53           | ~ (r1_tarski @ X32 @ sk_B)))
% 0.20/0.53         <= ((![X32 : $i]:
% 0.20/0.53                (((X32) = (k1_xboole_0))
% 0.20/0.53                 | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53                 | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.20/0.53                 | ~ (r1_tarski @ X32 @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['8'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.53         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.53         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.20/0.53         <= ((![X32 : $i]:
% 0.20/0.53                (((X32) = (k1_xboole_0))
% 0.20/0.53                 | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53                 | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.20/0.53                 | ~ (r1_tarski @ X32 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('61', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(fc9_tops_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X23)
% 0.20/0.53          | ~ (v2_pre_topc @ X23)
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.53          | (v3_pre_topc @ (k1_tops_1 @ X23 @ X24) @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('67', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((![X32 : $i]:
% 0.20/0.53                (((X32) = (k1_xboole_0))
% 0.20/0.53                 | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53                 | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.20/0.53                 | ~ (r1_tarski @ X32 @ sk_B))))),
% 0.20/0.53      inference('demod', [status(thm)], ['60', '61', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.20/0.53          | ((k1_tops_1 @ X31 @ X30) != (k1_xboole_0))
% 0.20/0.53          | (v2_tops_1 @ X30 @ X31)
% 0.20/0.53          | ~ (l1_pre_topc @ X31))),
% 0.20/0.53      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.53        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (((v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.53        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.20/0.53         <= ((![X32 : $i]:
% 0.20/0.53                (((X32) = (k1_xboole_0))
% 0.20/0.53                 | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53                 | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.20/0.53                 | ~ (r1_tarski @ X32 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '73'])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (((v2_tops_1 @ sk_B @ sk_A))
% 0.20/0.53         <= ((![X32 : $i]:
% 0.20/0.53                (((X32) = (k1_xboole_0))
% 0.20/0.53                 | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53                 | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.20/0.53                 | ~ (r1_tarski @ X32 @ sk_B))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['74'])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      (~
% 0.20/0.53       (![X32 : $i]:
% 0.20/0.53          (((X32) = (k1_xboole_0))
% 0.20/0.53           | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53           | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.20/0.53           | ~ (r1_tarski @ X32 @ sk_B))) | 
% 0.20/0.53       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.53  thf('78', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)],
% 0.20/0.53                ['1', '3', '5', '7', '34', '35', '77'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
