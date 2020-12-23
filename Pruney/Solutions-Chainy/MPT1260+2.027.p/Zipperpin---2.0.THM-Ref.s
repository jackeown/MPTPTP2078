%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.acKyJxA60V

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:26 EST 2020

% Result     : Theorem 17.16s
% Output     : Refutation 17.16s
% Verified   : 
% Statistics : Number of formulae       :  335 (2599 expanded)
%              Number of leaves         :   49 ( 842 expanded)
%              Depth                    :   25
%              Number of atoms          : 3134 (24771 expanded)
%              Number of equality atoms :  224 (2043 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X30 @ X29 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k4_subset_1 @ X41 @ X40 @ X42 )
        = ( k2_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

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

thf('16',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ~ ( v3_pre_topc @ X62 @ X63 )
      | ~ ( r1_tarski @ X62 @ X64 )
      | ( r1_tarski @ X62 @ ( k1_tops_1 @ X63 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X53: $i,X55: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('25',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k4_subset_1 @ X41 @ X40 @ X42 )
        = ( k2_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_subset_1 @ X0 @ X0 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X30 @ X29 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_subset_1 @ X0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','46','47','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','49'])).

thf('51',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('53',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('55',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X70 ) ) )
      | ( ( k1_tops_1 @ X70 @ X69 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X70 ) @ X69 @ ( k2_tops_1 @ X70 @ X69 ) ) )
      | ~ ( l1_pre_topc @ X70 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('59',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k7_subset_1 @ X46 @ X45 @ X47 )
        = ( k4_xboole_0 @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('60',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('61',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k7_subset_1 @ X46 @ X45 @ X47 )
        = ( k6_subset_1 @ X45 @ X47 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k6_subset_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57','62'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('65',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57','62'])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('74',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k2_tops_1 @ X61 @ X60 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X61 ) @ ( k2_pre_topc @ X61 @ X60 ) @ ( k1_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('84',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( l1_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X56 @ X57 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('85',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('89',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('91',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X68 ) ) )
      | ( ( k2_pre_topc @ X68 @ X67 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X68 ) @ X67 @ ( k2_tops_1 @ X68 @ X67 ) ) )
      | ~ ( l1_pre_topc @ X68 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k7_subset_1 @ X46 @ X45 @ X47 )
        = ( k6_subset_1 @ X45 @ X47 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('99',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('100',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('101',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('102',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k6_subset_1 @ X21 @ X22 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('104',plain,(
    ! [X53: $i,X55: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('107',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('110',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('111',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('112',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k6_subset_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('114',plain,(
    ! [X32: $i,X33: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('115',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k6_subset_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['108','113','116'])).

thf('118',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k6_subset_1 @ X21 @ X22 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('119',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k6_subset_1 @ X21 @ X22 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('123',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('125',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('126',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['124','129'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('131',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('132',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('133',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['117','136'])).

thf('138',plain,
    ( ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['99','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('140',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('141',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('142',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('144',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('145',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k6_subset_1 @ X21 @ X22 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('148',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('150',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('152',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['152','155'])).

thf('157',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('158',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('159',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('161',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k6_subset_1 @ X21 @ X22 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['159','164'])).

thf('166',plain,
    ( ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['138','139','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('168',plain,(
    ! [X32: $i,X33: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('169',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k4_subset_1 @ X41 @ X40 @ X42 )
        = ( k2_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['167','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('173',plain,(
    ! [X32: $i,X33: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('174',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X30 @ X29 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['171','176'])).

thf('178',plain,
    ( ( m1_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['166','177'])).

thf('179',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('180',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('182',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('183',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('184',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['181','184'])).

thf('186',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
      = ( k2_pre_topc @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['180','187'])).

thf('189',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57','62'])).

thf('190',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('191',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( k6_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['189','192'])).

thf('194',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('197',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('200',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['195','200'])).

thf('202',plain,(
    ! [X53: $i,X55: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('203',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('207',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k6_subset_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k6_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['117','136'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['205','208','211'])).

thf('213',plain,
    ( ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['188','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('215',plain,
    ( ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['117','136'])).

thf('218',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k6_subset_1 @ X21 @ X22 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('221',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k6_subset_1 @ X21 @ X22 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X1 ) @ k1_xboole_0 )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['219','226'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['216','227'])).

thf('229',plain,
    ( ( ( k2_xboole_0 @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_pre_topc @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['215','228'])).

thf('230',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('232',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_pre_topc @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['229','232'])).

thf('234',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('235',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('236',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('237',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['234','237'])).

thf('239',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('242',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 )
      | ( ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( ( k2_xboole_0 @ X1 @ ( k6_subset_1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['240','245'])).

thf('247',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('249',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( X1
        = ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['246','247','248','249'])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('253',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['251','254'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['251','254'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( X1
        = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['250','255','256'])).

thf('258',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['233','257'])).

thf('259',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('261',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['117','136'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['262','263'])).

thf('265',plain,
    ( ( ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['259','264'])).

thf('266',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('267',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['159','164'])).

thf('268',plain,
    ( ( ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57','62'])).

thf('270',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('271',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['269','270'])).

thf('272',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_pre_topc @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['229','232'])).

thf('273',plain,
    ( ( ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('274',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['258','268','271','272','273'])).

thf('275',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('276',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( l1_pre_topc @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X58 @ X59 ) @ X58 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('277',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['277','278','279'])).

thf('281',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['274','280'])).

thf('282',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('283',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','81','82','283'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.acKyJxA60V
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:08:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.16/17.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 17.16/17.41  % Solved by: fo/fo7.sh
% 17.16/17.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.16/17.41  % done 29395 iterations in 16.946s
% 17.16/17.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 17.16/17.41  % SZS output start Refutation
% 17.16/17.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 17.16/17.41  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 17.16/17.41  thf(sk_A_type, type, sk_A: $i).
% 17.16/17.41  thf(sk_B_1_type, type, sk_B_1: $i).
% 17.16/17.41  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 17.16/17.41  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 17.16/17.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.16/17.41  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 17.16/17.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.16/17.41  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 17.16/17.41  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 17.16/17.41  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 17.16/17.41  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 17.16/17.41  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 17.16/17.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.16/17.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.16/17.41  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 17.16/17.41  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 17.16/17.41  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 17.16/17.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.16/17.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.16/17.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 17.16/17.41  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 17.16/17.41  thf(t76_tops_1, conjecture,
% 17.16/17.41    (![A:$i]:
% 17.16/17.41     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.16/17.41       ( ![B:$i]:
% 17.16/17.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.16/17.41           ( ( v3_pre_topc @ B @ A ) <=>
% 17.16/17.41             ( ( k2_tops_1 @ A @ B ) =
% 17.16/17.41               ( k7_subset_1 @
% 17.16/17.41                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 17.16/17.41  thf(zf_stmt_0, negated_conjecture,
% 17.16/17.41    (~( ![A:$i]:
% 17.16/17.41        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.16/17.41          ( ![B:$i]:
% 17.16/17.41            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.16/17.41              ( ( v3_pre_topc @ B @ A ) <=>
% 17.16/17.41                ( ( k2_tops_1 @ A @ B ) =
% 17.16/17.41                  ( k7_subset_1 @
% 17.16/17.41                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 17.16/17.41    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 17.16/17.41  thf('0', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 17.16/17.41        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('1', plain,
% 17.16/17.41      (~
% 17.16/17.41       (((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 17.16/17.41       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 17.16/17.41      inference('split', [status(esa)], ['0'])).
% 17.16/17.41  thf('2', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('3', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 17.16/17.41        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('4', plain,
% 17.16/17.41      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 17.16/17.41      inference('split', [status(esa)], ['3'])).
% 17.16/17.41  thf('5', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('6', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf(dt_k4_subset_1, axiom,
% 17.16/17.41    (![A:$i,B:$i,C:$i]:
% 17.16/17.41     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 17.16/17.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 17.16/17.41       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 17.16/17.41  thf('7', plain,
% 17.16/17.41      (![X29 : $i, X30 : $i, X31 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 17.16/17.41          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 17.16/17.41          | (m1_subset_1 @ (k4_subset_1 @ X30 @ X29 @ X31) @ 
% 17.16/17.41             (k1_zfmisc_1 @ X30)))),
% 17.16/17.41      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 17.16/17.41  thf('8', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 17.16/17.41           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.16/17.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['6', '7'])).
% 17.16/17.41  thf('9', plain,
% 17.16/17.41      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_B_1) @ 
% 17.16/17.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['5', '8'])).
% 17.16/17.41  thf('10', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('11', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf(redefinition_k4_subset_1, axiom,
% 17.16/17.41    (![A:$i,B:$i,C:$i]:
% 17.16/17.41     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 17.16/17.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 17.16/17.41       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 17.16/17.41  thf('12', plain,
% 17.16/17.41      (![X40 : $i, X41 : $i, X42 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 17.16/17.41          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41))
% 17.16/17.41          | ((k4_subset_1 @ X41 @ X40 @ X42) = (k2_xboole_0 @ X40 @ X42)))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 17.16/17.41  thf('13', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 17.16/17.41            = (k2_xboole_0 @ sk_B_1 @ X0))
% 17.16/17.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['11', '12'])).
% 17.16/17.41  thf('14', plain,
% 17.16/17.41      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_B_1)
% 17.16/17.41         = (k2_xboole_0 @ sk_B_1 @ sk_B_1))),
% 17.16/17.41      inference('sup-', [status(thm)], ['10', '13'])).
% 17.16/17.41  thf('15', plain,
% 17.16/17.41      ((m1_subset_1 @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ 
% 17.16/17.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('demod', [status(thm)], ['9', '14'])).
% 17.16/17.41  thf(t56_tops_1, axiom,
% 17.16/17.41    (![A:$i]:
% 17.16/17.41     ( ( l1_pre_topc @ A ) =>
% 17.16/17.41       ( ![B:$i]:
% 17.16/17.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.16/17.41           ( ![C:$i]:
% 17.16/17.41             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.16/17.41               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 17.16/17.41                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 17.16/17.41  thf('16', plain,
% 17.16/17.41      (![X62 : $i, X63 : $i, X64 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 17.16/17.41          | ~ (v3_pre_topc @ X62 @ X63)
% 17.16/17.41          | ~ (r1_tarski @ X62 @ X64)
% 17.16/17.41          | (r1_tarski @ X62 @ (k1_tops_1 @ X63 @ X64))
% 17.16/17.41          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 17.16/17.41          | ~ (l1_pre_topc @ X63))),
% 17.16/17.41      inference('cnf', [status(esa)], [t56_tops_1])).
% 17.16/17.41  thf('17', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (~ (l1_pre_topc @ sk_A)
% 17.16/17.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.16/17.41          | (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ 
% 17.16/17.41             (k1_tops_1 @ sk_A @ X0))
% 17.16/17.41          | ~ (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ X0)
% 17.16/17.41          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ sk_A))),
% 17.16/17.41      inference('sup-', [status(thm)], ['15', '16'])).
% 17.16/17.41  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('19', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.16/17.41          | (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ 
% 17.16/17.41             (k1_tops_1 @ sk_A @ X0))
% 17.16/17.41          | ~ (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ X0)
% 17.16/17.41          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ sk_A))),
% 17.16/17.41      inference('demod', [status(thm)], ['17', '18'])).
% 17.16/17.41  thf(d10_xboole_0, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 17.16/17.41  thf('20', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 17.16/17.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.16/17.41  thf('21', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 17.16/17.41      inference('simplify', [status(thm)], ['20'])).
% 17.16/17.41  thf(t3_subset, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.16/17.41  thf('22', plain,
% 17.16/17.41      (![X53 : $i, X55 : $i]:
% 17.16/17.41         ((m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X53 @ X55))),
% 17.16/17.41      inference('cnf', [status(esa)], [t3_subset])).
% 17.16/17.41  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['21', '22'])).
% 17.16/17.41  thf('24', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['21', '22'])).
% 17.16/17.41  thf('25', plain,
% 17.16/17.41      (![X40 : $i, X41 : $i, X42 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 17.16/17.41          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41))
% 17.16/17.41          | ((k4_subset_1 @ X41 @ X40 @ X42) = (k2_xboole_0 @ X40 @ X42)))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 17.16/17.41  thf('26', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 17.16/17.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['24', '25'])).
% 17.16/17.41  thf('27', plain,
% 17.16/17.41      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['23', '26'])).
% 17.16/17.41  thf(t46_xboole_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 17.16/17.41  thf('28', plain,
% 17.16/17.41      (![X19 : $i, X20 : $i]:
% 17.16/17.41         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 17.16/17.41      inference('cnf', [status(esa)], [t46_xboole_1])).
% 17.16/17.41  thf(redefinition_k6_subset_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 17.16/17.41  thf('29', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('30', plain,
% 17.16/17.41      (![X19 : $i, X20 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 17.16/17.41      inference('demod', [status(thm)], ['28', '29'])).
% 17.16/17.41  thf(l32_xboole_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.16/17.41  thf('31', plain,
% 17.16/17.41      (![X3 : $i, X4 : $i]:
% 17.16/17.41         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 17.16/17.41      inference('cnf', [status(esa)], [l32_xboole_1])).
% 17.16/17.41  thf('32', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('33', plain,
% 17.16/17.41      (![X3 : $i, X4 : $i]:
% 17.16/17.41         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 17.16/17.41      inference('demod', [status(thm)], ['31', '32'])).
% 17.16/17.41  thf('34', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (((k1_xboole_0) != (k1_xboole_0))
% 17.16/17.41          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['30', '33'])).
% 17.16/17.41  thf('35', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 17.16/17.41      inference('simplify', [status(thm)], ['34'])).
% 17.16/17.41  thf('36', plain,
% 17.16/17.41      (![X0 : $i, X2 : $i]:
% 17.16/17.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 17.16/17.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.16/17.41  thf('37', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 17.16/17.41          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['35', '36'])).
% 17.16/17.41  thf('38', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (~ (r1_tarski @ (k4_subset_1 @ X0 @ X0 @ X0) @ X0)
% 17.16/17.41          | ((k2_xboole_0 @ X0 @ X0) = (X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['27', '37'])).
% 17.16/17.41  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['21', '22'])).
% 17.16/17.41  thf('40', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['21', '22'])).
% 17.16/17.41  thf('41', plain,
% 17.16/17.41      (![X29 : $i, X30 : $i, X31 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 17.16/17.41          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 17.16/17.41          | (m1_subset_1 @ (k4_subset_1 @ X30 @ X29 @ X31) @ 
% 17.16/17.41             (k1_zfmisc_1 @ X30)))),
% 17.16/17.41      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 17.16/17.41  thf('42', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 17.16/17.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['40', '41'])).
% 17.16/17.41  thf('43', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['39', '42'])).
% 17.16/17.41  thf('44', plain,
% 17.16/17.41      (![X53 : $i, X54 : $i]:
% 17.16/17.41         ((r1_tarski @ X53 @ X54) | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54)))),
% 17.16/17.41      inference('cnf', [status(esa)], [t3_subset])).
% 17.16/17.41  thf('45', plain,
% 17.16/17.41      (![X0 : $i]: (r1_tarski @ (k4_subset_1 @ X0 @ X0 @ X0) @ X0)),
% 17.16/17.41      inference('sup-', [status(thm)], ['43', '44'])).
% 17.16/17.41  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['38', '45'])).
% 17.16/17.41  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['38', '45'])).
% 17.16/17.41  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['38', '45'])).
% 17.16/17.41  thf('49', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.16/17.41          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 17.16/17.41          | ~ (r1_tarski @ sk_B_1 @ X0)
% 17.16/17.41          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 17.16/17.41      inference('demod', [status(thm)], ['19', '46', '47', '48'])).
% 17.16/17.41  thf('50', plain,
% 17.16/17.41      ((![X0 : $i]:
% 17.16/17.41          (~ (r1_tarski @ sk_B_1 @ X0)
% 17.16/17.41           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 17.16/17.41           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 17.16/17.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['4', '49'])).
% 17.16/17.41  thf('51', plain,
% 17.16/17.41      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 17.16/17.41         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 17.16/17.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['2', '50'])).
% 17.16/17.41  thf('52', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 17.16/17.41      inference('simplify', [status(thm)], ['20'])).
% 17.16/17.41  thf('53', plain,
% 17.16/17.41      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 17.16/17.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 17.16/17.41      inference('demod', [status(thm)], ['51', '52'])).
% 17.16/17.41  thf('54', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf(t74_tops_1, axiom,
% 17.16/17.41    (![A:$i]:
% 17.16/17.41     ( ( l1_pre_topc @ A ) =>
% 17.16/17.41       ( ![B:$i]:
% 17.16/17.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.16/17.41           ( ( k1_tops_1 @ A @ B ) =
% 17.16/17.41             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 17.16/17.41  thf('55', plain,
% 17.16/17.41      (![X69 : $i, X70 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ X70)))
% 17.16/17.41          | ((k1_tops_1 @ X70 @ X69)
% 17.16/17.41              = (k7_subset_1 @ (u1_struct_0 @ X70) @ X69 @ 
% 17.16/17.41                 (k2_tops_1 @ X70 @ X69)))
% 17.16/17.41          | ~ (l1_pre_topc @ X70))),
% 17.16/17.41      inference('cnf', [status(esa)], [t74_tops_1])).
% 17.16/17.41  thf('56', plain,
% 17.16/17.41      ((~ (l1_pre_topc @ sk_A)
% 17.16/17.41        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 17.16/17.41               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['54', '55'])).
% 17.16/17.41  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('58', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf(redefinition_k7_subset_1, axiom,
% 17.16/17.41    (![A:$i,B:$i,C:$i]:
% 17.16/17.41     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 17.16/17.41       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 17.16/17.41  thf('59', plain,
% 17.16/17.41      (![X45 : $i, X46 : $i, X47 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 17.16/17.41          | ((k7_subset_1 @ X46 @ X45 @ X47) = (k4_xboole_0 @ X45 @ X47)))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 17.16/17.41  thf('60', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('61', plain,
% 17.16/17.41      (![X45 : $i, X46 : $i, X47 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 17.16/17.41          | ((k7_subset_1 @ X46 @ X45 @ X47) = (k6_subset_1 @ X45 @ X47)))),
% 17.16/17.41      inference('demod', [status(thm)], ['59', '60'])).
% 17.16/17.41  thf('62', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 17.16/17.41           = (k6_subset_1 @ sk_B_1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['58', '61'])).
% 17.16/17.41  thf('63', plain,
% 17.16/17.41      (((k1_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['56', '57', '62'])).
% 17.16/17.41  thf(t36_xboole_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 17.16/17.41  thf('64', plain,
% 17.16/17.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 17.16/17.41      inference('cnf', [status(esa)], [t36_xboole_1])).
% 17.16/17.41  thf('65', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('66', plain,
% 17.16/17.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 17.16/17.41      inference('demod', [status(thm)], ['64', '65'])).
% 17.16/17.41  thf('67', plain,
% 17.16/17.41      (![X0 : $i, X2 : $i]:
% 17.16/17.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 17.16/17.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.16/17.41  thf('68', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 17.16/17.41          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['66', '67'])).
% 17.16/17.41  thf('69', plain,
% 17.16/17.41      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 17.16/17.41        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['63', '68'])).
% 17.16/17.41  thf('70', plain,
% 17.16/17.41      (((k1_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['56', '57', '62'])).
% 17.16/17.41  thf('71', plain,
% 17.16/17.41      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 17.16/17.41        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['69', '70'])).
% 17.16/17.41  thf('72', plain,
% 17.16/17.41      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 17.16/17.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['53', '71'])).
% 17.16/17.41  thf('73', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf(l78_tops_1, axiom,
% 17.16/17.41    (![A:$i]:
% 17.16/17.41     ( ( l1_pre_topc @ A ) =>
% 17.16/17.41       ( ![B:$i]:
% 17.16/17.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.16/17.41           ( ( k2_tops_1 @ A @ B ) =
% 17.16/17.41             ( k7_subset_1 @
% 17.16/17.41               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 17.16/17.41               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 17.16/17.41  thf('74', plain,
% 17.16/17.41      (![X60 : $i, X61 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 17.16/17.41          | ((k2_tops_1 @ X61 @ X60)
% 17.16/17.41              = (k7_subset_1 @ (u1_struct_0 @ X61) @ 
% 17.16/17.41                 (k2_pre_topc @ X61 @ X60) @ (k1_tops_1 @ X61 @ X60)))
% 17.16/17.41          | ~ (l1_pre_topc @ X61))),
% 17.16/17.41      inference('cnf', [status(esa)], [l78_tops_1])).
% 17.16/17.41  thf('75', plain,
% 17.16/17.41      ((~ (l1_pre_topc @ sk_A)
% 17.16/17.41        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['73', '74'])).
% 17.16/17.41  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('77', plain,
% 17.16/17.41      (((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['75', '76'])).
% 17.16/17.41  thf('78', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 17.16/17.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 17.16/17.41      inference('sup+', [status(thm)], ['72', '77'])).
% 17.16/17.41  thf('79', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 17.16/17.41         <= (~
% 17.16/17.41             (((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('split', [status(esa)], ['0'])).
% 17.16/17.41  thf('80', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 17.16/17.41         <= (~
% 17.16/17.41             (((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 17.16/17.41             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['78', '79'])).
% 17.16/17.41  thf('81', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 17.16/17.41       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 17.16/17.41      inference('simplify', [status(thm)], ['80'])).
% 17.16/17.41  thf('82', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 17.16/17.41       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 17.16/17.41      inference('split', [status(esa)], ['3'])).
% 17.16/17.41  thf('83', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf(dt_k2_tops_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( ( l1_pre_topc @ A ) & 
% 17.16/17.41         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.16/17.41       ( m1_subset_1 @
% 17.16/17.41         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 17.16/17.41  thf('84', plain,
% 17.16/17.41      (![X56 : $i, X57 : $i]:
% 17.16/17.41         (~ (l1_pre_topc @ X56)
% 17.16/17.41          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 17.16/17.41          | (m1_subset_1 @ (k2_tops_1 @ X56 @ X57) @ 
% 17.16/17.41             (k1_zfmisc_1 @ (u1_struct_0 @ X56))))),
% 17.16/17.41      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 17.16/17.41  thf('85', plain,
% 17.16/17.41      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.16/17.41        | ~ (l1_pre_topc @ sk_A))),
% 17.16/17.41      inference('sup-', [status(thm)], ['83', '84'])).
% 17.16/17.41  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('87', plain,
% 17.16/17.41      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('demod', [status(thm)], ['85', '86'])).
% 17.16/17.41  thf('88', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 17.16/17.41           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.16/17.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['6', '7'])).
% 17.16/17.41  thf('89', plain,
% 17.16/17.41      ((m1_subset_1 @ 
% 17.16/17.41        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 17.16/17.41         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 17.16/17.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['87', '88'])).
% 17.16/17.41  thf('90', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf(t65_tops_1, axiom,
% 17.16/17.41    (![A:$i]:
% 17.16/17.41     ( ( l1_pre_topc @ A ) =>
% 17.16/17.41       ( ![B:$i]:
% 17.16/17.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.16/17.41           ( ( k2_pre_topc @ A @ B ) =
% 17.16/17.41             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 17.16/17.41  thf('91', plain,
% 17.16/17.41      (![X67 : $i, X68 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ X68)))
% 17.16/17.41          | ((k2_pre_topc @ X68 @ X67)
% 17.16/17.41              = (k4_subset_1 @ (u1_struct_0 @ X68) @ X67 @ 
% 17.16/17.41                 (k2_tops_1 @ X68 @ X67)))
% 17.16/17.41          | ~ (l1_pre_topc @ X68))),
% 17.16/17.41      inference('cnf', [status(esa)], [t65_tops_1])).
% 17.16/17.41  thf('92', plain,
% 17.16/17.41      ((~ (l1_pre_topc @ sk_A)
% 17.16/17.41        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 17.16/17.41            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 17.16/17.41               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['90', '91'])).
% 17.16/17.41  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('94', plain,
% 17.16/17.41      (((k2_pre_topc @ sk_A @ sk_B_1)
% 17.16/17.41         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 17.16/17.41            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['92', '93'])).
% 17.16/17.41  thf('95', plain,
% 17.16/17.41      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('demod', [status(thm)], ['89', '94'])).
% 17.16/17.41  thf('96', plain,
% 17.16/17.41      (![X45 : $i, X46 : $i, X47 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 17.16/17.41          | ((k7_subset_1 @ X46 @ X45 @ X47) = (k6_subset_1 @ X45 @ X47)))),
% 17.16/17.41      inference('demod', [status(thm)], ['59', '60'])).
% 17.16/17.41  thf('97', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 17.16/17.41           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['95', '96'])).
% 17.16/17.41  thf('98', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('split', [status(esa)], ['3'])).
% 17.16/17.41  thf('99', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup+', [status(thm)], ['97', '98'])).
% 17.16/17.41  thf(t51_xboole_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 17.16/17.41       ( A ) ))).
% 17.16/17.41  thf('100', plain,
% 17.16/17.41      (![X21 : $i, X22 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 17.16/17.41           = (X21))),
% 17.16/17.41      inference('cnf', [status(esa)], [t51_xboole_1])).
% 17.16/17.41  thf('101', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('102', plain,
% 17.16/17.41      (![X21 : $i, X22 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k6_subset_1 @ X21 @ X22))
% 17.16/17.41           = (X21))),
% 17.16/17.41      inference('demod', [status(thm)], ['100', '101'])).
% 17.16/17.41  thf('103', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 17.16/17.41      inference('simplify', [status(thm)], ['34'])).
% 17.16/17.41  thf('104', plain,
% 17.16/17.41      (![X53 : $i, X55 : $i]:
% 17.16/17.41         ((m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X53 @ X55))),
% 17.16/17.41      inference('cnf', [status(esa)], [t3_subset])).
% 17.16/17.41  thf('105', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['103', '104'])).
% 17.16/17.41  thf('106', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['102', '105'])).
% 17.16/17.41  thf(involutiveness_k3_subset_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 17.16/17.41       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 17.16/17.41  thf('107', plain,
% 17.16/17.41      (![X37 : $i, X38 : $i]:
% 17.16/17.41         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 17.16/17.41          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 17.16/17.41      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 17.16/17.41  thf('108', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 17.16/17.41           = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup-', [status(thm)], ['106', '107'])).
% 17.16/17.41  thf('109', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['102', '105'])).
% 17.16/17.41  thf(d5_subset_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 17.16/17.41       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 17.16/17.41  thf('110', plain,
% 17.16/17.41      (![X25 : $i, X26 : $i]:
% 17.16/17.41         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 17.16/17.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 17.16/17.41      inference('cnf', [status(esa)], [d5_subset_1])).
% 17.16/17.41  thf('111', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('112', plain,
% 17.16/17.41      (![X25 : $i, X26 : $i]:
% 17.16/17.41         (((k3_subset_1 @ X25 @ X26) = (k6_subset_1 @ X25 @ X26))
% 17.16/17.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 17.16/17.41      inference('demod', [status(thm)], ['110', '111'])).
% 17.16/17.41  thf('113', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 17.16/17.41           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['109', '112'])).
% 17.16/17.41  thf(dt_k6_subset_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 17.16/17.41  thf('114', plain,
% 17.16/17.41      (![X32 : $i, X33 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k6_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))),
% 17.16/17.41      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 17.16/17.41  thf('115', plain,
% 17.16/17.41      (![X25 : $i, X26 : $i]:
% 17.16/17.41         (((k3_subset_1 @ X25 @ X26) = (k6_subset_1 @ X25 @ X26))
% 17.16/17.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 17.16/17.41      inference('demod', [status(thm)], ['110', '111'])).
% 17.16/17.41  thf('116', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 17.16/17.41           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['114', '115'])).
% 17.16/17.41  thf('117', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 17.16/17.41           = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('demod', [status(thm)], ['108', '113', '116'])).
% 17.16/17.41  thf('118', plain,
% 17.16/17.41      (![X21 : $i, X22 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k6_subset_1 @ X21 @ X22))
% 17.16/17.41           = (X21))),
% 17.16/17.41      inference('demod', [status(thm)], ['100', '101'])).
% 17.16/17.41  thf('119', plain,
% 17.16/17.41      (![X19 : $i, X20 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 17.16/17.41      inference('demod', [status(thm)], ['28', '29'])).
% 17.16/17.41  thf('120', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['118', '119'])).
% 17.16/17.41  thf('121', plain,
% 17.16/17.41      (![X21 : $i, X22 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k6_subset_1 @ X21 @ X22))
% 17.16/17.41           = (X21))),
% 17.16/17.41      inference('demod', [status(thm)], ['100', '101'])).
% 17.16/17.41  thf('122', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 17.16/17.41           k1_xboole_0) = (k3_xboole_0 @ X1 @ X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['120', '121'])).
% 17.16/17.41  thf(t1_boole, axiom,
% 17.16/17.41    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 17.16/17.41  thf('123', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 17.16/17.41      inference('cnf', [status(esa)], [t1_boole])).
% 17.16/17.41  thf('124', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 17.16/17.41           = (k3_xboole_0 @ X1 @ X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['122', '123'])).
% 17.16/17.41  thf(commutativity_k2_tarski, axiom,
% 17.16/17.41    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 17.16/17.41  thf('125', plain,
% 17.16/17.41      (![X23 : $i, X24 : $i]:
% 17.16/17.41         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 17.16/17.41      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 17.16/17.41  thf(t12_setfam_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 17.16/17.41  thf('126', plain,
% 17.16/17.41      (![X51 : $i, X52 : $i]:
% 17.16/17.41         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 17.16/17.41      inference('cnf', [status(esa)], [t12_setfam_1])).
% 17.16/17.41  thf('127', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['125', '126'])).
% 17.16/17.41  thf('128', plain,
% 17.16/17.41      (![X51 : $i, X52 : $i]:
% 17.16/17.41         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 17.16/17.41      inference('cnf', [status(esa)], [t12_setfam_1])).
% 17.16/17.41  thf('129', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['127', '128'])).
% 17.16/17.41  thf('130', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 17.16/17.41           = (k3_xboole_0 @ X1 @ X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['124', '129'])).
% 17.16/17.41  thf(t100_xboole_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 17.16/17.41  thf('131', plain,
% 17.16/17.41      (![X6 : $i, X7 : $i]:
% 17.16/17.41         ((k4_xboole_0 @ X6 @ X7)
% 17.16/17.41           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 17.16/17.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 17.16/17.41  thf('132', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('133', plain,
% 17.16/17.41      (![X6 : $i, X7 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X6 @ X7)
% 17.16/17.41           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 17.16/17.41      inference('demod', [status(thm)], ['131', '132'])).
% 17.16/17.41  thf('134', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 17.16/17.41           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 17.16/17.41      inference('sup+', [status(thm)], ['130', '133'])).
% 17.16/17.41  thf('135', plain,
% 17.16/17.41      (![X6 : $i, X7 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X6 @ X7)
% 17.16/17.41           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 17.16/17.41      inference('demod', [status(thm)], ['131', '132'])).
% 17.16/17.41  thf('136', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 17.16/17.41           = (k6_subset_1 @ X1 @ X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['134', '135'])).
% 17.16/17.41  thf('137', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 17.16/17.41           = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('demod', [status(thm)], ['117', '136'])).
% 17.16/17.41  thf('138', plain,
% 17.16/17.41      ((((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k2_tops_1 @ sk_A @ sk_B_1))
% 17.16/17.41          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup+', [status(thm)], ['99', '137'])).
% 17.16/17.41  thf('139', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['127', '128'])).
% 17.16/17.41  thf('140', plain,
% 17.16/17.41      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('demod', [status(thm)], ['85', '86'])).
% 17.16/17.41  thf('141', plain,
% 17.16/17.41      (![X53 : $i, X54 : $i]:
% 17.16/17.41         ((r1_tarski @ X53 @ X54) | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54)))),
% 17.16/17.41      inference('cnf', [status(esa)], [t3_subset])).
% 17.16/17.41  thf('142', plain,
% 17.16/17.41      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 17.16/17.41      inference('sup-', [status(thm)], ['140', '141'])).
% 17.16/17.41  thf('143', plain,
% 17.16/17.41      (![X3 : $i, X5 : $i]:
% 17.16/17.41         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 17.16/17.41      inference('cnf', [status(esa)], [l32_xboole_1])).
% 17.16/17.41  thf('144', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('145', plain,
% 17.16/17.41      (![X3 : $i, X5 : $i]:
% 17.16/17.41         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 17.16/17.41      inference('demod', [status(thm)], ['143', '144'])).
% 17.16/17.41  thf('146', plain,
% 17.16/17.41      (((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 17.16/17.41         = (k1_xboole_0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['142', '145'])).
% 17.16/17.41  thf('147', plain,
% 17.16/17.41      (![X21 : $i, X22 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k6_subset_1 @ X21 @ X22))
% 17.16/17.41           = (X21))),
% 17.16/17.41      inference('demod', [status(thm)], ['100', '101'])).
% 17.16/17.41  thf('148', plain,
% 17.16/17.41      (((k2_xboole_0 @ 
% 17.16/17.41         (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)) @ 
% 17.16/17.41         k1_xboole_0) = (k2_tops_1 @ sk_A @ sk_B_1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['146', '147'])).
% 17.16/17.41  thf('149', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 17.16/17.41      inference('cnf', [status(esa)], [t1_boole])).
% 17.16/17.41  thf('150', plain,
% 17.16/17.41      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 17.16/17.41         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 17.16/17.41      inference('demod', [status(thm)], ['148', '149'])).
% 17.16/17.41  thf('151', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['127', '128'])).
% 17.16/17.41  thf('152', plain,
% 17.16/17.41      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))
% 17.16/17.41         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 17.16/17.41      inference('demod', [status(thm)], ['150', '151'])).
% 17.16/17.41  thf('153', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['102', '105'])).
% 17.16/17.41  thf('154', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 17.16/17.41            = (k2_xboole_0 @ sk_B_1 @ X0))
% 17.16/17.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['11', '12'])).
% 17.16/17.41  thf('155', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 17.16/17.41           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 17.16/17.41           = (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['153', '154'])).
% 17.16/17.41  thf('156', plain,
% 17.16/17.41      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 17.16/17.41         (k2_tops_1 @ sk_A @ sk_B_1))
% 17.16/17.41         = (k2_xboole_0 @ sk_B_1 @ 
% 17.16/17.41            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 17.16/17.41      inference('sup+', [status(thm)], ['152', '155'])).
% 17.16/17.41  thf('157', plain,
% 17.16/17.41      (((k2_pre_topc @ sk_A @ sk_B_1)
% 17.16/17.41         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 17.16/17.41            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['92', '93'])).
% 17.16/17.41  thf('158', plain,
% 17.16/17.41      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))
% 17.16/17.41         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 17.16/17.41      inference('demod', [status(thm)], ['150', '151'])).
% 17.16/17.41  thf('159', plain,
% 17.16/17.41      (((k2_pre_topc @ sk_A @ sk_B_1)
% 17.16/17.41         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['156', '157', '158'])).
% 17.16/17.41  thf('160', plain,
% 17.16/17.41      (![X19 : $i, X20 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 17.16/17.41      inference('demod', [status(thm)], ['28', '29'])).
% 17.16/17.41  thf('161', plain,
% 17.16/17.41      (![X21 : $i, X22 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k6_subset_1 @ X21 @ X22))
% 17.16/17.41           = (X21))),
% 17.16/17.41      inference('demod', [status(thm)], ['100', '101'])).
% 17.16/17.41  thf('162', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 17.16/17.41           k1_xboole_0) = (X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['160', '161'])).
% 17.16/17.41  thf('163', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 17.16/17.41      inference('cnf', [status(esa)], [t1_boole])).
% 17.16/17.41  thf('164', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['162', '163'])).
% 17.16/17.41  thf('165', plain,
% 17.16/17.41      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['159', '164'])).
% 17.16/17.41  thf('166', plain,
% 17.16/17.41      ((((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('demod', [status(thm)], ['138', '139', '165'])).
% 17.16/17.41  thf('167', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['21', '22'])).
% 17.16/17.41  thf('168', plain,
% 17.16/17.41      (![X32 : $i, X33 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k6_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))),
% 17.16/17.41      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 17.16/17.41  thf('169', plain,
% 17.16/17.41      (![X40 : $i, X41 : $i, X42 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 17.16/17.41          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41))
% 17.16/17.41          | ((k4_subset_1 @ X41 @ X40 @ X42) = (k2_xboole_0 @ X40 @ X42)))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 17.16/17.41  thf('170', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.16/17.41         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 17.16/17.41            = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X2))
% 17.16/17.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['168', '169'])).
% 17.16/17.41  thf('171', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X0)
% 17.16/17.41           = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['167', '170'])).
% 17.16/17.41  thf('172', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['21', '22'])).
% 17.16/17.41  thf('173', plain,
% 17.16/17.41      (![X32 : $i, X33 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k6_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))),
% 17.16/17.41      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 17.16/17.41  thf('174', plain,
% 17.16/17.41      (![X29 : $i, X30 : $i, X31 : $i]:
% 17.16/17.41         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 17.16/17.41          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 17.16/17.41          | (m1_subset_1 @ (k4_subset_1 @ X30 @ X29 @ X31) @ 
% 17.16/17.41             (k1_zfmisc_1 @ X30)))),
% 17.16/17.41      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 17.16/17.41  thf('175', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.16/17.41         ((m1_subset_1 @ (k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2) @ 
% 17.16/17.41           (k1_zfmisc_1 @ X0))
% 17.16/17.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['173', '174'])).
% 17.16/17.41  thf('176', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X0) @ 
% 17.16/17.41          (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['172', '175'])).
% 17.16/17.41  thf('177', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0) @ 
% 17.16/17.41          (k1_zfmisc_1 @ X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['171', '176'])).
% 17.16/17.41  thf('178', plain,
% 17.16/17.41      (((m1_subset_1 @ 
% 17.16/17.41         (k2_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 17.16/17.41         (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1))))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup+', [status(thm)], ['166', '177'])).
% 17.16/17.41  thf('179', plain,
% 17.16/17.41      (![X53 : $i, X54 : $i]:
% 17.16/17.41         ((r1_tarski @ X53 @ X54) | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54)))),
% 17.16/17.41      inference('cnf', [status(esa)], [t3_subset])).
% 17.16/17.41  thf('180', plain,
% 17.16/17.41      (((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 17.16/17.41         (k2_pre_topc @ sk_A @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['178', '179'])).
% 17.16/17.41  thf('181', plain,
% 17.16/17.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 17.16/17.41      inference('demod', [status(thm)], ['64', '65'])).
% 17.16/17.41  thf(t44_xboole_1, axiom,
% 17.16/17.41    (![A:$i,B:$i,C:$i]:
% 17.16/17.41     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 17.16/17.41       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 17.16/17.41  thf('182', plain,
% 17.16/17.41      (![X16 : $i, X17 : $i, X18 : $i]:
% 17.16/17.41         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 17.16/17.41          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 17.16/17.41      inference('cnf', [status(esa)], [t44_xboole_1])).
% 17.16/17.41  thf('183', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('184', plain,
% 17.16/17.41      (![X16 : $i, X17 : $i, X18 : $i]:
% 17.16/17.41         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 17.16/17.41          | ~ (r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18))),
% 17.16/17.41      inference('demod', [status(thm)], ['182', '183'])).
% 17.16/17.41  thf('185', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['181', '184'])).
% 17.16/17.41  thf('186', plain,
% 17.16/17.41      (![X0 : $i, X2 : $i]:
% 17.16/17.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 17.16/17.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.16/17.41  thf('187', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 17.16/17.41          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['185', '186'])).
% 17.16/17.41  thf('188', plain,
% 17.16/17.41      ((((k2_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))
% 17.16/17.41          = (k2_pre_topc @ sk_A @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['180', '187'])).
% 17.16/17.41  thf('189', plain,
% 17.16/17.41      (((k1_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['56', '57', '62'])).
% 17.16/17.41  thf('190', plain,
% 17.16/17.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 17.16/17.41      inference('demod', [status(thm)], ['64', '65'])).
% 17.16/17.41  thf('191', plain,
% 17.16/17.41      (![X3 : $i, X5 : $i]:
% 17.16/17.41         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 17.16/17.41      inference('demod', [status(thm)], ['143', '144'])).
% 17.16/17.41  thf('192', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['190', '191'])).
% 17.16/17.41  thf('193', plain,
% 17.16/17.41      (((k6_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1) = (k1_xboole_0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['189', '192'])).
% 17.16/17.41  thf('194', plain,
% 17.16/17.41      (![X16 : $i, X17 : $i, X18 : $i]:
% 17.16/17.41         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 17.16/17.41          | ~ (r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18))),
% 17.16/17.41      inference('demod', [status(thm)], ['182', '183'])).
% 17.16/17.41  thf('195', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 17.16/17.41          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41             (k2_xboole_0 @ sk_B_1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['193', '194'])).
% 17.16/17.41  thf('196', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 17.16/17.41      inference('cnf', [status(esa)], [t1_boole])).
% 17.16/17.41  thf('197', plain,
% 17.16/17.41      (![X19 : $i, X20 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 17.16/17.41      inference('demod', [status(thm)], ['28', '29'])).
% 17.16/17.41  thf('198', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['196', '197'])).
% 17.16/17.41  thf('199', plain,
% 17.16/17.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 17.16/17.41      inference('demod', [status(thm)], ['64', '65'])).
% 17.16/17.41  thf('200', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 17.16/17.41      inference('sup+', [status(thm)], ['198', '199'])).
% 17.16/17.41  thf('201', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k2_xboole_0 @ sk_B_1 @ X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['195', '200'])).
% 17.16/17.41  thf('202', plain,
% 17.16/17.41      (![X53 : $i, X55 : $i]:
% 17.16/17.41         ((m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X53 @ X55))),
% 17.16/17.41      inference('cnf', [status(esa)], [t3_subset])).
% 17.16/17.41  thf('203', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['201', '202'])).
% 17.16/17.41  thf('204', plain,
% 17.16/17.41      (![X37 : $i, X38 : $i]:
% 17.16/17.41         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 17.16/17.41          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 17.16/17.41      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 17.16/17.41  thf('205', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         ((k3_subset_1 @ (k2_xboole_0 @ sk_B_1 @ X0) @ 
% 17.16/17.41           (k3_subset_1 @ (k2_xboole_0 @ sk_B_1 @ X0) @ 
% 17.16/17.41            (k1_tops_1 @ sk_A @ sk_B_1)))
% 17.16/17.41           = (k1_tops_1 @ sk_A @ sk_B_1))),
% 17.16/17.41      inference('sup-', [status(thm)], ['203', '204'])).
% 17.16/17.41  thf('206', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['201', '202'])).
% 17.16/17.41  thf('207', plain,
% 17.16/17.41      (![X25 : $i, X26 : $i]:
% 17.16/17.41         (((k3_subset_1 @ X25 @ X26) = (k6_subset_1 @ X25 @ X26))
% 17.16/17.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 17.16/17.41      inference('demod', [status(thm)], ['110', '111'])).
% 17.16/17.41  thf('208', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         ((k3_subset_1 @ (k2_xboole_0 @ sk_B_1 @ X0) @ 
% 17.16/17.41           (k1_tops_1 @ sk_A @ sk_B_1))
% 17.16/17.41           = (k6_subset_1 @ (k2_xboole_0 @ sk_B_1 @ X0) @ 
% 17.16/17.41              (k1_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['206', '207'])).
% 17.16/17.41  thf('209', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 17.16/17.41           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['114', '115'])).
% 17.16/17.41  thf('210', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 17.16/17.41           = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('demod', [status(thm)], ['117', '136'])).
% 17.16/17.41  thf('211', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 17.16/17.41           = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('demod', [status(thm)], ['209', '210'])).
% 17.16/17.41  thf('212', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         ((k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ X0) @ 
% 17.16/17.41           (k1_tops_1 @ sk_A @ sk_B_1)) = (k1_tops_1 @ sk_A @ sk_B_1))),
% 17.16/17.41      inference('demod', [status(thm)], ['205', '208', '211'])).
% 17.16/17.41  thf('213', plain,
% 17.16/17.41      ((((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k1_tops_1 @ sk_A @ sk_B_1)) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup+', [status(thm)], ['188', '212'])).
% 17.16/17.41  thf('214', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['127', '128'])).
% 17.16/17.41  thf('215', plain,
% 17.16/17.41      ((((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k2_pre_topc @ sk_A @ sk_B_1)) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('demod', [status(thm)], ['213', '214'])).
% 17.16/17.41  thf('216', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['127', '128'])).
% 17.16/17.41  thf('217', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 17.16/17.41           = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('demod', [status(thm)], ['117', '136'])).
% 17.16/17.41  thf('218', plain,
% 17.16/17.41      (![X21 : $i, X22 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k6_subset_1 @ X21 @ X22))
% 17.16/17.41           = (X21))),
% 17.16/17.41      inference('demod', [status(thm)], ['100', '101'])).
% 17.16/17.41  thf('219', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)) @ 
% 17.16/17.41           (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['217', '218'])).
% 17.16/17.41  thf('220', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['190', '191'])).
% 17.16/17.41  thf('221', plain,
% 17.16/17.41      (![X21 : $i, X22 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k6_subset_1 @ X21 @ X22))
% 17.16/17.41           = (X21))),
% 17.16/17.41      inference('demod', [status(thm)], ['100', '101'])).
% 17.16/17.41  thf('222', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X1) @ 
% 17.16/17.41           k1_xboole_0) = (k6_subset_1 @ X1 @ X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['220', '221'])).
% 17.16/17.41  thf('223', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 17.16/17.41      inference('cnf', [status(esa)], [t1_boole])).
% 17.16/17.41  thf('224', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X1)
% 17.16/17.41           = (k6_subset_1 @ X1 @ X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['222', '223'])).
% 17.16/17.41  thf('225', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['127', '128'])).
% 17.16/17.41  thf('226', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 17.16/17.41           = (k6_subset_1 @ X1 @ X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['224', '225'])).
% 17.16/17.41  thf('227', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 17.16/17.41           = (X1))),
% 17.16/17.41      inference('demod', [status(thm)], ['219', '226'])).
% 17.16/17.41  thf('228', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 17.16/17.41           = (X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['216', '227'])).
% 17.16/17.41  thf('229', plain,
% 17.16/17.41      ((((k2_xboole_0 @ 
% 17.16/17.41          (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41           (k1_tops_1 @ sk_A @ sk_B_1)) @ 
% 17.16/17.41          (k1_tops_1 @ sk_A @ sk_B_1)) = (k2_pre_topc @ sk_A @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup+', [status(thm)], ['215', '228'])).
% 17.16/17.41  thf('230', plain,
% 17.16/17.41      (((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['75', '76'])).
% 17.16/17.41  thf('231', plain,
% 17.16/17.41      (![X0 : $i]:
% 17.16/17.41         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 17.16/17.41           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['95', '96'])).
% 17.16/17.41  thf('232', plain,
% 17.16/17.41      (((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['230', '231'])).
% 17.16/17.41  thf('233', plain,
% 17.16/17.41      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k1_tops_1 @ sk_A @ sk_B_1)) = (k2_pre_topc @ sk_A @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('demod', [status(thm)], ['229', '232'])).
% 17.16/17.41  thf('234', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 17.16/17.41      inference('simplify', [status(thm)], ['20'])).
% 17.16/17.41  thf(t43_xboole_1, axiom,
% 17.16/17.41    (![A:$i,B:$i,C:$i]:
% 17.16/17.41     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 17.16/17.41       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 17.16/17.41  thf('235', plain,
% 17.16/17.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 17.16/17.41         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 17.16/17.41          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 17.16/17.41      inference('cnf', [status(esa)], [t43_xboole_1])).
% 17.16/17.41  thf('236', plain,
% 17.16/17.41      (![X43 : $i, X44 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 17.16/17.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 17.16/17.41  thf('237', plain,
% 17.16/17.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 17.16/17.41         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 17.16/17.41          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 17.16/17.41      inference('demod', [status(thm)], ['235', '236'])).
% 17.16/17.41  thf('238', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (r1_tarski @ (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 17.16/17.41      inference('sup-', [status(thm)], ['234', '237'])).
% 17.16/17.41  thf('239', plain,
% 17.16/17.41      (![X3 : $i, X5 : $i]:
% 17.16/17.41         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 17.16/17.41      inference('demod', [status(thm)], ['143', '144'])).
% 17.16/17.41  thf('240', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 17.16/17.41           = (k1_xboole_0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['238', '239'])).
% 17.16/17.41  thf('241', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 17.16/17.41      inference('simplify', [status(thm)], ['20'])).
% 17.16/17.41  thf('242', plain,
% 17.16/17.41      (![X16 : $i, X17 : $i, X18 : $i]:
% 17.16/17.41         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 17.16/17.41          | ~ (r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18))),
% 17.16/17.41      inference('demod', [status(thm)], ['182', '183'])).
% 17.16/17.41  thf('243', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['241', '242'])).
% 17.16/17.41  thf('244', plain,
% 17.16/17.41      (![X0 : $i, X2 : $i]:
% 17.16/17.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 17.16/17.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.16/17.41  thf('245', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)) @ X1)
% 17.16/17.41          | ((k2_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)) = (X1)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['243', '244'])).
% 17.16/17.41  thf('246', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ k1_xboole_0) @ 
% 17.16/17.41             (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 17.16/17.41          | ((k2_xboole_0 @ X1 @ 
% 17.16/17.41              (k6_subset_1 @ (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ X1))
% 17.16/17.41              = (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 17.16/17.41      inference('sup-', [status(thm)], ['240', '245'])).
% 17.16/17.41  thf('247', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 17.16/17.41      inference('cnf', [status(esa)], [t1_boole])).
% 17.16/17.41  thf('248', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 17.16/17.41           = (k1_xboole_0))),
% 17.16/17.41      inference('sup-', [status(thm)], ['238', '239'])).
% 17.16/17.41  thf('249', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 17.16/17.41      inference('cnf', [status(esa)], [t1_boole])).
% 17.16/17.41  thf('250', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (~ (r1_tarski @ X1 @ (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 17.16/17.41          | ((X1) = (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 17.16/17.41      inference('demod', [status(thm)], ['246', '247', '248', '249'])).
% 17.16/17.41  thf('251', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['162', '163'])).
% 17.16/17.41  thf('252', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['127', '128'])).
% 17.16/17.41  thf('253', plain,
% 17.16/17.41      (![X6 : $i, X7 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X6 @ X7)
% 17.16/17.41           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 17.16/17.41      inference('demod', [status(thm)], ['131', '132'])).
% 17.16/17.41  thf('254', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X0 @ X1)
% 17.16/17.41           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 17.16/17.41      inference('sup+', [status(thm)], ['252', '253'])).
% 17.16/17.41  thf('255', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 17.16/17.41           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['251', '254'])).
% 17.16/17.41  thf('256', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 17.16/17.41           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['251', '254'])).
% 17.16/17.41  thf('257', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 17.16/17.41          | ((X1) = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 17.16/17.41      inference('demod', [status(thm)], ['250', '255', '256'])).
% 17.16/17.41  thf('258', plain,
% 17.16/17.41      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41            (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41             (k2_tops_1 @ sk_A @ sk_B_1)))
% 17.16/17.41         | ((k1_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41             = (k5_xboole_0 @ 
% 17.16/17.41                (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41                 (k1_tops_1 @ sk_A @ sk_B_1)) @ 
% 17.16/17.41                (k2_tops_1 @ sk_A @ sk_B_1)))))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup-', [status(thm)], ['233', '257'])).
% 17.16/17.41  thf('259', plain,
% 17.16/17.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup+', [status(thm)], ['97', '98'])).
% 17.16/17.41  thf('260', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 17.16/17.41           = (k6_subset_1 @ X1 @ X0))),
% 17.16/17.41      inference('demod', [status(thm)], ['224', '225'])).
% 17.16/17.41  thf('261', plain,
% 17.16/17.41      (![X6 : $i, X7 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X6 @ X7)
% 17.16/17.41           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 17.16/17.41      inference('demod', [status(thm)], ['131', '132'])).
% 17.16/17.41  thf('262', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 17.16/17.41           = (k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 17.16/17.41      inference('sup+', [status(thm)], ['260', '261'])).
% 17.16/17.41  thf('263', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 17.16/17.41           = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('demod', [status(thm)], ['117', '136'])).
% 17.16/17.41  thf('264', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]:
% 17.16/17.41         ((k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 17.16/17.41           = (k3_xboole_0 @ X1 @ X0))),
% 17.16/17.41      inference('sup+', [status(thm)], ['262', '263'])).
% 17.16/17.41  thf('265', plain,
% 17.16/17.41      ((((k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k2_tops_1 @ sk_A @ sk_B_1))
% 17.16/17.41          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup+', [status(thm)], ['259', '264'])).
% 17.16/17.41  thf('266', plain,
% 17.16/17.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['127', '128'])).
% 17.16/17.41  thf('267', plain,
% 17.16/17.41      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 17.16/17.41      inference('sup+', [status(thm)], ['159', '164'])).
% 17.16/17.41  thf('268', plain,
% 17.16/17.41      ((((k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('demod', [status(thm)], ['265', '266', '267'])).
% 17.16/17.41  thf('269', plain,
% 17.16/17.41      (((k1_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 17.16/17.41      inference('demod', [status(thm)], ['56', '57', '62'])).
% 17.16/17.41  thf('270', plain,
% 17.16/17.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 17.16/17.41      inference('demod', [status(thm)], ['64', '65'])).
% 17.16/17.41  thf('271', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 17.16/17.41      inference('sup+', [status(thm)], ['269', '270'])).
% 17.16/17.41  thf('272', plain,
% 17.16/17.41      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k1_tops_1 @ sk_A @ sk_B_1)) = (k2_pre_topc @ sk_A @ sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('demod', [status(thm)], ['229', '232'])).
% 17.16/17.41  thf('273', plain,
% 17.16/17.41      ((((k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 17.16/17.41          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('demod', [status(thm)], ['265', '266', '267'])).
% 17.16/17.41  thf('274', plain,
% 17.16/17.41      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('demod', [status(thm)], ['258', '268', '271', '272', '273'])).
% 17.16/17.41  thf('275', plain,
% 17.16/17.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf(fc9_tops_1, axiom,
% 17.16/17.41    (![A:$i,B:$i]:
% 17.16/17.41     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 17.16/17.41         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.16/17.41       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 17.16/17.41  thf('276', plain,
% 17.16/17.41      (![X58 : $i, X59 : $i]:
% 17.16/17.41         (~ (l1_pre_topc @ X58)
% 17.16/17.41          | ~ (v2_pre_topc @ X58)
% 17.16/17.41          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 17.16/17.41          | (v3_pre_topc @ (k1_tops_1 @ X58 @ X59) @ X58))),
% 17.16/17.41      inference('cnf', [status(esa)], [fc9_tops_1])).
% 17.16/17.41  thf('277', plain,
% 17.16/17.41      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 17.16/17.41        | ~ (v2_pre_topc @ sk_A)
% 17.16/17.41        | ~ (l1_pre_topc @ sk_A))),
% 17.16/17.41      inference('sup-', [status(thm)], ['275', '276'])).
% 17.16/17.41  thf('278', plain, ((v2_pre_topc @ sk_A)),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('279', plain, ((l1_pre_topc @ sk_A)),
% 17.16/17.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.16/17.41  thf('280', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 17.16/17.41      inference('demod', [status(thm)], ['277', '278', '279'])).
% 17.16/17.41  thf('281', plain,
% 17.16/17.41      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 17.16/17.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 17.16/17.41      inference('sup+', [status(thm)], ['274', '280'])).
% 17.16/17.41  thf('282', plain,
% 17.16/17.41      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 17.16/17.41      inference('split', [status(esa)], ['0'])).
% 17.16/17.41  thf('283', plain,
% 17.16/17.41      (~
% 17.16/17.41       (((k2_tops_1 @ sk_A @ sk_B_1)
% 17.16/17.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.16/17.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 17.16/17.41       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 17.16/17.41      inference('sup-', [status(thm)], ['281', '282'])).
% 17.16/17.41  thf('284', plain, ($false),
% 17.16/17.41      inference('sat_resolution*', [status(thm)], ['1', '81', '82', '283'])).
% 17.16/17.41  
% 17.16/17.41  % SZS output end Refutation
% 17.16/17.41  
% 17.28/17.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
