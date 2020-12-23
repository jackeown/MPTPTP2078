%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aYAHZfnUci

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:23 EST 2020

% Result     : Theorem 3.73s
% Output     : Refutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 261 expanded)
%              Number of leaves         :   43 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          : 1345 (2885 expanded)
%              Number of equality atoms :   93 ( 194 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X70 ) ) )
      | ( ( k1_tops_1 @ X70 @ X69 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X70 ) @ X69 @ ( k2_tops_1 @ X70 @ X69 ) ) )
      | ~ ( l1_pre_topc @ X70 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( ( k7_subset_1 @ X47 @ X46 @ X48 )
        = ( k4_xboole_0 @ X46 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( ( k7_subset_1 @ X47 @ X46 @ X48 )
        = ( k6_subset_1 @ X46 @ X48 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X24 @ X25 ) @ X24 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( v3_pre_topc @ X64 @ X65 )
      | ~ ( r1_tarski @ X64 @ X66 )
      | ( r1_tarski @ X64 @ ( k1_tops_1 @ X65 @ X66 ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( ( k2_tops_1 @ X63 @ X62 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X63 ) @ ( k2_pre_topc @ X63 @ X62 ) @ ( k1_tops_1 @ X63 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('47',plain,(
    ! [X26: $i] :
      ( ( k6_subset_1 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('51',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k6_subset_1 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('56',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('57',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['52'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('61',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( l1_pre_topc @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X58 @ X59 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( ( k7_subset_1 @ X47 @ X46 @ X48 )
        = ( k6_subset_1 @ X46 @ X48 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k6_subset_1 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','70'])).

thf('72',plain,
    ( ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','71'])).

thf('73',plain,
    ( ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('74',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X30 @ X31 ) @ ( k4_xboole_0 @ X30 @ X31 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('75',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('76',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('77',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('78',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X30 @ X31 ) @ ( k1_setfam_1 @ ( k2_tarski @ X30 @ X31 ) ) )
      = X30 ) ),
    inference(demod,[status(thm)],['74','75','76','81'])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['73','82'])).

thf('84',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('85',plain,(
    ! [X26: $i] :
      ( ( k6_subset_1 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('86',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X30 @ X31 ) @ ( k1_setfam_1 @ ( k2_tarski @ X30 @ X31 ) ) )
      = X30 ) ),
    inference(demod,[status(thm)],['74','75','76','81'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('89',plain,(
    ! [X49: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('90',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('92',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['87','96'])).

thf('98',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('100',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X60 @ X61 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('101',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['98','104'])).

thf('106',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aYAHZfnUci
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:40:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 3.73/3.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.73/3.96  % Solved by: fo/fo7.sh
% 3.73/3.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.73/3.96  % done 3138 iterations in 3.481s
% 3.73/3.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.73/3.96  % SZS output start Refutation
% 3.73/3.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.73/3.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.73/3.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.73/3.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.73/3.96  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.73/3.96  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.73/3.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.73/3.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.73/3.96  thf(sk_A_type, type, sk_A: $i).
% 3.73/3.96  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.73/3.96  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.73/3.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.73/3.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.73/3.96  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.73/3.96  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.73/3.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.73/3.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.73/3.96  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.73/3.96  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.73/3.96  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.73/3.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.73/3.96  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.73/3.96  thf(sk_B_type, type, sk_B: $i).
% 3.73/3.96  thf(t76_tops_1, conjecture,
% 3.73/3.96    (![A:$i]:
% 3.73/3.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.73/3.96       ( ![B:$i]:
% 3.73/3.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.73/3.96           ( ( v3_pre_topc @ B @ A ) <=>
% 3.73/3.96             ( ( k2_tops_1 @ A @ B ) =
% 3.73/3.96               ( k7_subset_1 @
% 3.73/3.96                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 3.73/3.96  thf(zf_stmt_0, negated_conjecture,
% 3.73/3.96    (~( ![A:$i]:
% 3.73/3.96        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.73/3.96          ( ![B:$i]:
% 3.73/3.96            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.73/3.96              ( ( v3_pre_topc @ B @ A ) <=>
% 3.73/3.96                ( ( k2_tops_1 @ A @ B ) =
% 3.73/3.96                  ( k7_subset_1 @
% 3.73/3.96                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 3.73/3.96    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 3.73/3.96  thf('0', plain,
% 3.73/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 3.73/3.96        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf('1', plain,
% 3.73/3.96      (~
% 3.73/3.96       (((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.73/3.96       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 3.73/3.96      inference('split', [status(esa)], ['0'])).
% 3.73/3.96  thf('2', plain,
% 3.73/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf(t74_tops_1, axiom,
% 3.73/3.96    (![A:$i]:
% 3.73/3.96     ( ( l1_pre_topc @ A ) =>
% 3.73/3.96       ( ![B:$i]:
% 3.73/3.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.73/3.96           ( ( k1_tops_1 @ A @ B ) =
% 3.73/3.96             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.73/3.96  thf('3', plain,
% 3.73/3.96      (![X69 : $i, X70 : $i]:
% 3.73/3.96         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ X70)))
% 3.73/3.96          | ((k1_tops_1 @ X70 @ X69)
% 3.73/3.96              = (k7_subset_1 @ (u1_struct_0 @ X70) @ X69 @ 
% 3.73/3.96                 (k2_tops_1 @ X70 @ X69)))
% 3.73/3.96          | ~ (l1_pre_topc @ X70))),
% 3.73/3.96      inference('cnf', [status(esa)], [t74_tops_1])).
% 3.73/3.96  thf('4', plain,
% 3.73/3.96      ((~ (l1_pre_topc @ sk_A)
% 3.73/3.96        | ((k1_tops_1 @ sk_A @ sk_B)
% 3.73/3.96            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.73/3.96               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.73/3.96      inference('sup-', [status(thm)], ['2', '3'])).
% 3.73/3.96  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf('6', plain,
% 3.73/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf(redefinition_k7_subset_1, axiom,
% 3.73/3.96    (![A:$i,B:$i,C:$i]:
% 3.73/3.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.73/3.96       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.73/3.96  thf('7', plain,
% 3.73/3.96      (![X46 : $i, X47 : $i, X48 : $i]:
% 3.73/3.96         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 3.73/3.96          | ((k7_subset_1 @ X47 @ X46 @ X48) = (k4_xboole_0 @ X46 @ X48)))),
% 3.73/3.96      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.73/3.96  thf(redefinition_k6_subset_1, axiom,
% 3.73/3.96    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.73/3.96  thf('8', plain,
% 3.73/3.96      (![X44 : $i, X45 : $i]:
% 3.73/3.96         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 3.73/3.96      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.73/3.96  thf('9', plain,
% 3.73/3.96      (![X46 : $i, X47 : $i, X48 : $i]:
% 3.73/3.96         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 3.73/3.96          | ((k7_subset_1 @ X47 @ X46 @ X48) = (k6_subset_1 @ X46 @ X48)))),
% 3.73/3.96      inference('demod', [status(thm)], ['7', '8'])).
% 3.73/3.96  thf('10', plain,
% 3.73/3.96      (![X0 : $i]:
% 3.73/3.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.73/3.96           = (k6_subset_1 @ sk_B @ X0))),
% 3.73/3.96      inference('sup-', [status(thm)], ['6', '9'])).
% 3.73/3.96  thf('11', plain,
% 3.73/3.96      (((k1_tops_1 @ sk_A @ sk_B)
% 3.73/3.96         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.73/3.96      inference('demod', [status(thm)], ['4', '5', '10'])).
% 3.73/3.96  thf(t36_xboole_1, axiom,
% 3.73/3.96    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.73/3.96  thf('12', plain,
% 3.73/3.96      (![X24 : $i, X25 : $i]: (r1_tarski @ (k4_xboole_0 @ X24 @ X25) @ X24)),
% 3.73/3.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.73/3.96  thf('13', plain,
% 3.73/3.96      (![X44 : $i, X45 : $i]:
% 3.73/3.96         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 3.73/3.96      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.73/3.96  thf('14', plain,
% 3.73/3.96      (![X24 : $i, X25 : $i]: (r1_tarski @ (k6_subset_1 @ X24 @ X25) @ X24)),
% 3.73/3.96      inference('demod', [status(thm)], ['12', '13'])).
% 3.73/3.96  thf('15', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 3.73/3.96      inference('sup+', [status(thm)], ['11', '14'])).
% 3.73/3.96  thf('16', plain,
% 3.73/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf('17', plain,
% 3.73/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 3.73/3.96        | (v3_pre_topc @ sk_B @ sk_A))),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf('18', plain,
% 3.73/3.96      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.73/3.96      inference('split', [status(esa)], ['17'])).
% 3.73/3.96  thf('19', plain,
% 3.73/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf(t56_tops_1, axiom,
% 3.73/3.96    (![A:$i]:
% 3.73/3.96     ( ( l1_pre_topc @ A ) =>
% 3.73/3.96       ( ![B:$i]:
% 3.73/3.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.73/3.96           ( ![C:$i]:
% 3.73/3.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.73/3.96               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 3.73/3.96                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.73/3.96  thf('20', plain,
% 3.73/3.96      (![X64 : $i, X65 : $i, X66 : $i]:
% 3.73/3.96         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 3.73/3.96          | ~ (v3_pre_topc @ X64 @ X65)
% 3.73/3.96          | ~ (r1_tarski @ X64 @ X66)
% 3.73/3.96          | (r1_tarski @ X64 @ (k1_tops_1 @ X65 @ X66))
% 3.73/3.96          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 3.73/3.96          | ~ (l1_pre_topc @ X65))),
% 3.73/3.96      inference('cnf', [status(esa)], [t56_tops_1])).
% 3.73/3.96  thf('21', plain,
% 3.73/3.96      (![X0 : $i]:
% 3.73/3.96         (~ (l1_pre_topc @ sk_A)
% 3.73/3.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.73/3.96          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 3.73/3.96          | ~ (r1_tarski @ sk_B @ X0)
% 3.73/3.96          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.73/3.96      inference('sup-', [status(thm)], ['19', '20'])).
% 3.73/3.96  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf('23', plain,
% 3.73/3.96      (![X0 : $i]:
% 3.73/3.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.73/3.96          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 3.73/3.96          | ~ (r1_tarski @ sk_B @ X0)
% 3.73/3.96          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.73/3.96      inference('demod', [status(thm)], ['21', '22'])).
% 3.73/3.96  thf('24', plain,
% 3.73/3.96      ((![X0 : $i]:
% 3.73/3.96          (~ (r1_tarski @ sk_B @ X0)
% 3.73/3.96           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 3.73/3.96           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 3.73/3.96         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.73/3.96      inference('sup-', [status(thm)], ['18', '23'])).
% 3.73/3.96  thf('25', plain,
% 3.73/3.96      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 3.73/3.96         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.73/3.96      inference('sup-', [status(thm)], ['16', '24'])).
% 3.73/3.96  thf(d10_xboole_0, axiom,
% 3.73/3.96    (![A:$i,B:$i]:
% 3.73/3.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.73/3.96  thf('26', plain,
% 3.73/3.96      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 3.73/3.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.73/3.96  thf('27', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 3.73/3.96      inference('simplify', [status(thm)], ['26'])).
% 3.73/3.96  thf('28', plain,
% 3.73/3.96      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 3.73/3.96         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.73/3.96      inference('demod', [status(thm)], ['25', '27'])).
% 3.73/3.96  thf('29', plain,
% 3.73/3.96      (![X17 : $i, X19 : $i]:
% 3.73/3.96         (((X17) = (X19))
% 3.73/3.96          | ~ (r1_tarski @ X19 @ X17)
% 3.73/3.96          | ~ (r1_tarski @ X17 @ X19))),
% 3.73/3.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.73/3.96  thf('30', plain,
% 3.73/3.96      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 3.73/3.96         | ((k1_tops_1 @ sk_A @ sk_B) = (sk_B))))
% 3.73/3.96         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.73/3.96      inference('sup-', [status(thm)], ['28', '29'])).
% 3.73/3.96  thf('31', plain,
% 3.73/3.96      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 3.73/3.96         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.73/3.96      inference('sup-', [status(thm)], ['15', '30'])).
% 3.73/3.96  thf('32', plain,
% 3.73/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf(l78_tops_1, axiom,
% 3.73/3.96    (![A:$i]:
% 3.73/3.96     ( ( l1_pre_topc @ A ) =>
% 3.73/3.96       ( ![B:$i]:
% 3.73/3.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.73/3.96           ( ( k2_tops_1 @ A @ B ) =
% 3.73/3.96             ( k7_subset_1 @
% 3.73/3.96               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 3.73/3.96               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.73/3.96  thf('33', plain,
% 3.73/3.96      (![X62 : $i, X63 : $i]:
% 3.73/3.96         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 3.73/3.96          | ((k2_tops_1 @ X63 @ X62)
% 3.73/3.96              = (k7_subset_1 @ (u1_struct_0 @ X63) @ 
% 3.73/3.96                 (k2_pre_topc @ X63 @ X62) @ (k1_tops_1 @ X63 @ X62)))
% 3.73/3.96          | ~ (l1_pre_topc @ X63))),
% 3.73/3.96      inference('cnf', [status(esa)], [l78_tops_1])).
% 3.73/3.96  thf('34', plain,
% 3.73/3.96      ((~ (l1_pre_topc @ sk_A)
% 3.73/3.96        | ((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 3.73/3.96      inference('sup-', [status(thm)], ['32', '33'])).
% 3.73/3.96  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf('36', plain,
% 3.73/3.96      (((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.73/3.96            (k1_tops_1 @ sk_A @ sk_B)))),
% 3.73/3.96      inference('demod', [status(thm)], ['34', '35'])).
% 3.73/3.96  thf('37', plain,
% 3.73/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.73/3.96         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.73/3.96      inference('sup+', [status(thm)], ['31', '36'])).
% 3.73/3.96  thf('38', plain,
% 3.73/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.73/3.96         <= (~
% 3.73/3.96             (((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('split', [status(esa)], ['0'])).
% 3.73/3.96  thf('39', plain,
% 3.73/3.96      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 3.73/3.96         <= (~
% 3.73/3.96             (((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 3.73/3.96             ((v3_pre_topc @ sk_B @ sk_A)))),
% 3.73/3.96      inference('sup-', [status(thm)], ['37', '38'])).
% 3.73/3.96  thf('40', plain,
% 3.73/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.73/3.96       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 3.73/3.96      inference('simplify', [status(thm)], ['39'])).
% 3.73/3.96  thf('41', plain,
% 3.73/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.73/3.96       ((v3_pre_topc @ sk_B @ sk_A))),
% 3.73/3.96      inference('split', [status(esa)], ['17'])).
% 3.73/3.96  thf(d4_xboole_0, axiom,
% 3.73/3.96    (![A:$i,B:$i,C:$i]:
% 3.73/3.96     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.73/3.96       ( ![D:$i]:
% 3.73/3.96         ( ( r2_hidden @ D @ C ) <=>
% 3.73/3.96           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.73/3.96  thf('42', plain,
% 3.73/3.96      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.73/3.96         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 3.73/3.96          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 3.73/3.96          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.73/3.96      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.73/3.96  thf(t12_setfam_1, axiom,
% 3.73/3.96    (![A:$i,B:$i]:
% 3.73/3.96     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.73/3.96  thf('43', plain,
% 3.73/3.96      (![X50 : $i, X51 : $i]:
% 3.73/3.96         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 3.73/3.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.73/3.96  thf('44', plain,
% 3.73/3.96      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.73/3.96         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 3.73/3.96          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 3.73/3.96          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.73/3.96      inference('demod', [status(thm)], ['42', '43'])).
% 3.73/3.96  thf(t3_boole, axiom,
% 3.73/3.96    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.73/3.96  thf('45', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 3.73/3.96      inference('cnf', [status(esa)], [t3_boole])).
% 3.73/3.96  thf('46', plain,
% 3.73/3.96      (![X44 : $i, X45 : $i]:
% 3.73/3.96         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 3.73/3.96      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.73/3.96  thf('47', plain, (![X26 : $i]: ((k6_subset_1 @ X26 @ k1_xboole_0) = (X26))),
% 3.73/3.96      inference('demod', [status(thm)], ['45', '46'])).
% 3.73/3.96  thf(d5_xboole_0, axiom,
% 3.73/3.96    (![A:$i,B:$i,C:$i]:
% 3.73/3.96     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.73/3.96       ( ![D:$i]:
% 3.73/3.96         ( ( r2_hidden @ D @ C ) <=>
% 3.73/3.96           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.73/3.96  thf('48', plain,
% 3.73/3.96      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.73/3.96         (~ (r2_hidden @ X14 @ X13)
% 3.73/3.96          | ~ (r2_hidden @ X14 @ X12)
% 3.73/3.96          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 3.73/3.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.73/3.96  thf('49', plain,
% 3.73/3.96      (![X11 : $i, X12 : $i, X14 : $i]:
% 3.73/3.96         (~ (r2_hidden @ X14 @ X12)
% 3.73/3.96          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 3.73/3.96      inference('simplify', [status(thm)], ['48'])).
% 3.73/3.96  thf('50', plain,
% 3.73/3.96      (![X44 : $i, X45 : $i]:
% 3.73/3.96         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 3.73/3.96      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.73/3.96  thf('51', plain,
% 3.73/3.96      (![X11 : $i, X12 : $i, X14 : $i]:
% 3.73/3.96         (~ (r2_hidden @ X14 @ X12)
% 3.73/3.96          | ~ (r2_hidden @ X14 @ (k6_subset_1 @ X11 @ X12)))),
% 3.73/3.96      inference('demod', [status(thm)], ['49', '50'])).
% 3.73/3.96  thf('52', plain,
% 3.73/3.96      (![X0 : $i, X1 : $i]:
% 3.73/3.96         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.73/3.96      inference('sup-', [status(thm)], ['47', '51'])).
% 3.73/3.96  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.73/3.96      inference('condensation', [status(thm)], ['52'])).
% 3.73/3.96  thf('54', plain,
% 3.73/3.96      (![X0 : $i, X1 : $i]:
% 3.73/3.96         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 3.73/3.96          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 3.73/3.96      inference('sup-', [status(thm)], ['44', '53'])).
% 3.73/3.96  thf('55', plain,
% 3.73/3.96      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.73/3.96         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 3.73/3.96          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 3.73/3.96          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.73/3.96      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.73/3.96  thf('56', plain,
% 3.73/3.96      (![X50 : $i, X51 : $i]:
% 3.73/3.96         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 3.73/3.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.73/3.96  thf('57', plain,
% 3.73/3.96      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.73/3.96         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 3.73/3.96          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 3.73/3.96          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.73/3.96      inference('demod', [status(thm)], ['55', '56'])).
% 3.73/3.96  thf('58', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.73/3.96      inference('condensation', [status(thm)], ['52'])).
% 3.73/3.96  thf('59', plain,
% 3.73/3.96      (![X0 : $i, X1 : $i]:
% 3.73/3.96         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 3.73/3.96          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 3.73/3.96      inference('sup-', [status(thm)], ['57', '58'])).
% 3.73/3.96  thf('60', plain,
% 3.73/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf(dt_k2_pre_topc, axiom,
% 3.73/3.96    (![A:$i,B:$i]:
% 3.73/3.96     ( ( ( l1_pre_topc @ A ) & 
% 3.73/3.96         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.73/3.96       ( m1_subset_1 @
% 3.73/3.96         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.73/3.96  thf('61', plain,
% 3.73/3.96      (![X58 : $i, X59 : $i]:
% 3.73/3.96         (~ (l1_pre_topc @ X58)
% 3.73/3.96          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 3.73/3.96          | (m1_subset_1 @ (k2_pre_topc @ X58 @ X59) @ 
% 3.73/3.96             (k1_zfmisc_1 @ (u1_struct_0 @ X58))))),
% 3.73/3.96      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.73/3.96  thf('62', plain,
% 3.73/3.96      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.73/3.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.73/3.96        | ~ (l1_pre_topc @ sk_A))),
% 3.73/3.96      inference('sup-', [status(thm)], ['60', '61'])).
% 3.73/3.96  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf('64', plain,
% 3.73/3.96      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.73/3.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.73/3.96      inference('demod', [status(thm)], ['62', '63'])).
% 3.73/3.96  thf('65', plain,
% 3.73/3.96      (![X46 : $i, X47 : $i, X48 : $i]:
% 3.73/3.96         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 3.73/3.96          | ((k7_subset_1 @ X47 @ X46 @ X48) = (k6_subset_1 @ X46 @ X48)))),
% 3.73/3.96      inference('demod', [status(thm)], ['7', '8'])).
% 3.73/3.96  thf('66', plain,
% 3.73/3.96      (![X0 : $i]:
% 3.73/3.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.73/3.96           X0) = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 3.73/3.96      inference('sup-', [status(thm)], ['64', '65'])).
% 3.73/3.96  thf('67', plain,
% 3.73/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.73/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('split', [status(esa)], ['17'])).
% 3.73/3.96  thf('68', plain,
% 3.73/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.73/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('sup+', [status(thm)], ['66', '67'])).
% 3.73/3.96  thf('69', plain,
% 3.73/3.96      (![X11 : $i, X12 : $i, X14 : $i]:
% 3.73/3.96         (~ (r2_hidden @ X14 @ X12)
% 3.73/3.96          | ~ (r2_hidden @ X14 @ (k6_subset_1 @ X11 @ X12)))),
% 3.73/3.96      inference('demod', [status(thm)], ['49', '50'])).
% 3.73/3.96  thf('70', plain,
% 3.73/3.96      ((![X0 : $i]:
% 3.73/3.96          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 3.73/3.96           | ~ (r2_hidden @ X0 @ sk_B)))
% 3.73/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('sup-', [status(thm)], ['68', '69'])).
% 3.73/3.96  thf('71', plain,
% 3.73/3.96      ((![X0 : $i]:
% 3.73/3.96          (((k1_xboole_0)
% 3.73/3.96             = (k1_setfam_1 @ (k2_tarski @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.73/3.96           | ~ (r2_hidden @ 
% 3.73/3.96                (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 3.73/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('sup-', [status(thm)], ['59', '70'])).
% 3.73/3.96  thf('72', plain,
% 3.73/3.96      (((((k1_xboole_0)
% 3.73/3.96           = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.73/3.96         | ((k1_xboole_0)
% 3.73/3.96             = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))))
% 3.73/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('sup-', [status(thm)], ['54', '71'])).
% 3.73/3.96  thf('73', plain,
% 3.73/3.96      ((((k1_xboole_0)
% 3.73/3.96          = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 3.73/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('simplify', [status(thm)], ['72'])).
% 3.73/3.96  thf(t51_xboole_1, axiom,
% 3.73/3.96    (![A:$i,B:$i]:
% 3.73/3.96     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 3.73/3.96       ( A ) ))).
% 3.73/3.96  thf('74', plain,
% 3.73/3.96      (![X30 : $i, X31 : $i]:
% 3.73/3.96         ((k2_xboole_0 @ (k3_xboole_0 @ X30 @ X31) @ (k4_xboole_0 @ X30 @ X31))
% 3.73/3.96           = (X30))),
% 3.73/3.96      inference('cnf', [status(esa)], [t51_xboole_1])).
% 3.73/3.96  thf('75', plain,
% 3.73/3.96      (![X50 : $i, X51 : $i]:
% 3.73/3.96         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 3.73/3.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.73/3.96  thf('76', plain,
% 3.73/3.96      (![X44 : $i, X45 : $i]:
% 3.73/3.96         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 3.73/3.96      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.73/3.96  thf(commutativity_k2_tarski, axiom,
% 3.73/3.96    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.73/3.96  thf('77', plain,
% 3.73/3.96      (![X32 : $i, X33 : $i]:
% 3.73/3.96         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 3.73/3.96      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.73/3.96  thf(l51_zfmisc_1, axiom,
% 3.73/3.96    (![A:$i,B:$i]:
% 3.73/3.96     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.73/3.96  thf('78', plain,
% 3.73/3.96      (![X34 : $i, X35 : $i]:
% 3.73/3.96         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 3.73/3.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.73/3.96  thf('79', plain,
% 3.73/3.96      (![X0 : $i, X1 : $i]:
% 3.73/3.96         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 3.73/3.96      inference('sup+', [status(thm)], ['77', '78'])).
% 3.73/3.96  thf('80', plain,
% 3.73/3.96      (![X34 : $i, X35 : $i]:
% 3.73/3.96         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 3.73/3.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.73/3.96  thf('81', plain,
% 3.73/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.73/3.96      inference('sup+', [status(thm)], ['79', '80'])).
% 3.73/3.96  thf('82', plain,
% 3.73/3.96      (![X30 : $i, X31 : $i]:
% 3.73/3.96         ((k2_xboole_0 @ (k6_subset_1 @ X30 @ X31) @ 
% 3.73/3.96           (k1_setfam_1 @ (k2_tarski @ X30 @ X31))) = (X30))),
% 3.73/3.96      inference('demod', [status(thm)], ['74', '75', '76', '81'])).
% 3.73/3.96  thf('83', plain,
% 3.73/3.96      ((((k2_xboole_0 @ (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.73/3.96          k1_xboole_0) = (sk_B)))
% 3.73/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('sup+', [status(thm)], ['73', '82'])).
% 3.73/3.96  thf('84', plain,
% 3.73/3.96      (((k1_tops_1 @ sk_A @ sk_B)
% 3.73/3.96         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.73/3.96      inference('demod', [status(thm)], ['4', '5', '10'])).
% 3.73/3.96  thf('85', plain, (![X26 : $i]: ((k6_subset_1 @ X26 @ k1_xboole_0) = (X26))),
% 3.73/3.96      inference('demod', [status(thm)], ['45', '46'])).
% 3.73/3.96  thf('86', plain,
% 3.73/3.96      (![X30 : $i, X31 : $i]:
% 3.73/3.96         ((k2_xboole_0 @ (k6_subset_1 @ X30 @ X31) @ 
% 3.73/3.96           (k1_setfam_1 @ (k2_tarski @ X30 @ X31))) = (X30))),
% 3.73/3.96      inference('demod', [status(thm)], ['74', '75', '76', '81'])).
% 3.73/3.96  thf('87', plain,
% 3.73/3.96      (![X0 : $i]:
% 3.73/3.96         ((k2_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))
% 3.73/3.96           = (X0))),
% 3.73/3.96      inference('sup+', [status(thm)], ['85', '86'])).
% 3.73/3.96  thf('88', plain,
% 3.73/3.96      (![X32 : $i, X33 : $i]:
% 3.73/3.96         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 3.73/3.96      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.73/3.96  thf(t4_subset_1, axiom,
% 3.73/3.96    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.73/3.96  thf('89', plain,
% 3.73/3.96      (![X49 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X49))),
% 3.73/3.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.73/3.96  thf(t3_subset, axiom,
% 3.73/3.96    (![A:$i,B:$i]:
% 3.73/3.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.73/3.96  thf('90', plain,
% 3.73/3.96      (![X52 : $i, X53 : $i]:
% 3.73/3.96         ((r1_tarski @ X52 @ X53) | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53)))),
% 3.73/3.96      inference('cnf', [status(esa)], [t3_subset])).
% 3.73/3.96  thf('91', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.73/3.96      inference('sup-', [status(thm)], ['89', '90'])).
% 3.73/3.96  thf(t28_xboole_1, axiom,
% 3.73/3.96    (![A:$i,B:$i]:
% 3.73/3.96     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.73/3.96  thf('92', plain,
% 3.73/3.96      (![X22 : $i, X23 : $i]:
% 3.73/3.96         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 3.73/3.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.73/3.96  thf('93', plain,
% 3.73/3.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.73/3.96      inference('sup-', [status(thm)], ['91', '92'])).
% 3.73/3.96  thf('94', plain,
% 3.73/3.96      (![X50 : $i, X51 : $i]:
% 3.73/3.96         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 3.73/3.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.73/3.96  thf('95', plain,
% 3.73/3.96      (![X0 : $i]:
% 3.73/3.96         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 3.73/3.96      inference('demod', [status(thm)], ['93', '94'])).
% 3.73/3.96  thf('96', plain,
% 3.73/3.96      (![X0 : $i]:
% 3.73/3.96         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 3.73/3.96      inference('sup+', [status(thm)], ['88', '95'])).
% 3.73/3.96  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.73/3.96      inference('demod', [status(thm)], ['87', '96'])).
% 3.73/3.96  thf('98', plain,
% 3.73/3.96      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 3.73/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('demod', [status(thm)], ['83', '84', '97'])).
% 3.73/3.96  thf('99', plain,
% 3.73/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf(fc9_tops_1, axiom,
% 3.73/3.96    (![A:$i,B:$i]:
% 3.73/3.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 3.73/3.96         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.73/3.96       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 3.73/3.96  thf('100', plain,
% 3.73/3.96      (![X60 : $i, X61 : $i]:
% 3.73/3.96         (~ (l1_pre_topc @ X60)
% 3.73/3.96          | ~ (v2_pre_topc @ X60)
% 3.73/3.96          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 3.73/3.96          | (v3_pre_topc @ (k1_tops_1 @ X60 @ X61) @ X60))),
% 3.73/3.96      inference('cnf', [status(esa)], [fc9_tops_1])).
% 3.73/3.96  thf('101', plain,
% 3.73/3.96      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 3.73/3.96        | ~ (v2_pre_topc @ sk_A)
% 3.73/3.96        | ~ (l1_pre_topc @ sk_A))),
% 3.73/3.96      inference('sup-', [status(thm)], ['99', '100'])).
% 3.73/3.96  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 3.73/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.96  thf('104', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 3.73/3.96      inference('demod', [status(thm)], ['101', '102', '103'])).
% 3.73/3.96  thf('105', plain,
% 3.73/3.96      (((v3_pre_topc @ sk_B @ sk_A))
% 3.73/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.73/3.96      inference('sup+', [status(thm)], ['98', '104'])).
% 3.73/3.96  thf('106', plain,
% 3.73/3.96      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 3.73/3.96      inference('split', [status(esa)], ['0'])).
% 3.73/3.96  thf('107', plain,
% 3.73/3.96      (~
% 3.73/3.96       (((k2_tops_1 @ sk_A @ sk_B)
% 3.73/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.73/3.96             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.73/3.96       ((v3_pre_topc @ sk_B @ sk_A))),
% 3.73/3.96      inference('sup-', [status(thm)], ['105', '106'])).
% 3.73/3.96  thf('108', plain, ($false),
% 3.73/3.96      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '107'])).
% 3.73/3.96  
% 3.73/3.96  % SZS output end Refutation
% 3.73/3.96  
% 3.73/3.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
