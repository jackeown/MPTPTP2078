%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VwfuRWivzi

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:30 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 194 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          : 1141 (2385 expanded)
%              Number of equality atoms :   74 ( 137 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k1_tops_1 @ X52 @ X51 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X52 ) @ X51 @ ( k2_tops_1 @ X52 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k7_subset_1 @ X33 @ X32 @ X34 )
        = ( k4_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('11',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v3_pre_topc @ X46 @ X47 )
      | ~ ( r1_tarski @ X46 @ X48 )
      | ( r1_tarski @ X46 @ ( k1_tops_1 @ X47 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_tops_1 @ X45 @ X44 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k2_pre_topc @ X45 @ X44 ) @ ( k1_tops_1 @ X45 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['42'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('49',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X40 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k7_subset_1 @ X33 @ X32 @ X34 )
        = ( k4_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','58'])).

thf('60',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','59'])).

thf('61',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('65',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','74'])).

thf('76',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf('77',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('79',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X42 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('80',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['77','83'])).

thf('85',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VwfuRWivzi
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.66/1.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.66/1.89  % Solved by: fo/fo7.sh
% 1.66/1.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.89  % done 1809 iterations in 1.442s
% 1.66/1.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.66/1.89  % SZS output start Refutation
% 1.66/1.89  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.66/1.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.66/1.89  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.66/1.89  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.66/1.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.66/1.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.66/1.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.66/1.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.66/1.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.66/1.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.66/1.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.66/1.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.66/1.89  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.66/1.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.66/1.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.66/1.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.66/1.89  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.66/1.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.66/1.89  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.89  thf(t76_tops_1, conjecture,
% 1.66/1.89    (![A:$i]:
% 1.66/1.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.66/1.89       ( ![B:$i]:
% 1.66/1.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.89           ( ( v3_pre_topc @ B @ A ) <=>
% 1.66/1.89             ( ( k2_tops_1 @ A @ B ) =
% 1.66/1.89               ( k7_subset_1 @
% 1.66/1.89                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.66/1.89  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.89    (~( ![A:$i]:
% 1.66/1.89        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.66/1.89          ( ![B:$i]:
% 1.66/1.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.89              ( ( v3_pre_topc @ B @ A ) <=>
% 1.66/1.89                ( ( k2_tops_1 @ A @ B ) =
% 1.66/1.89                  ( k7_subset_1 @
% 1.66/1.89                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.66/1.89    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.66/1.89  thf('0', plain,
% 1.66/1.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.66/1.89        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf('1', plain,
% 1.66/1.89      (~
% 1.66/1.89       (((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.66/1.89       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.66/1.89      inference('split', [status(esa)], ['0'])).
% 1.66/1.89  thf('2', plain,
% 1.66/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf(t74_tops_1, axiom,
% 1.66/1.89    (![A:$i]:
% 1.66/1.89     ( ( l1_pre_topc @ A ) =>
% 1.66/1.89       ( ![B:$i]:
% 1.66/1.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.89           ( ( k1_tops_1 @ A @ B ) =
% 1.66/1.89             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.66/1.89  thf('3', plain,
% 1.66/1.89      (![X51 : $i, X52 : $i]:
% 1.66/1.89         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 1.66/1.89          | ((k1_tops_1 @ X52 @ X51)
% 1.66/1.89              = (k7_subset_1 @ (u1_struct_0 @ X52) @ X51 @ 
% 1.66/1.89                 (k2_tops_1 @ X52 @ X51)))
% 1.66/1.89          | ~ (l1_pre_topc @ X52))),
% 1.66/1.89      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.66/1.89  thf('4', plain,
% 1.66/1.89      ((~ (l1_pre_topc @ sk_A)
% 1.66/1.89        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.66/1.89            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.66/1.89               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.66/1.89      inference('sup-', [status(thm)], ['2', '3'])).
% 1.66/1.89  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf('6', plain,
% 1.66/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf(redefinition_k7_subset_1, axiom,
% 1.66/1.89    (![A:$i,B:$i,C:$i]:
% 1.66/1.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.66/1.89       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.66/1.89  thf('7', plain,
% 1.66/1.89      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.66/1.89         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 1.66/1.89          | ((k7_subset_1 @ X33 @ X32 @ X34) = (k4_xboole_0 @ X32 @ X34)))),
% 1.66/1.89      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.66/1.89  thf('8', plain,
% 1.66/1.89      (![X0 : $i]:
% 1.66/1.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.66/1.89           = (k4_xboole_0 @ sk_B @ X0))),
% 1.66/1.89      inference('sup-', [status(thm)], ['6', '7'])).
% 1.66/1.89  thf('9', plain,
% 1.66/1.89      (((k1_tops_1 @ sk_A @ sk_B)
% 1.66/1.89         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.66/1.89      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.66/1.89  thf(t36_xboole_1, axiom,
% 1.66/1.89    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.66/1.89  thf('10', plain,
% 1.66/1.89      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 1.66/1.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.66/1.89  thf('11', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.66/1.89      inference('sup+', [status(thm)], ['9', '10'])).
% 1.66/1.89  thf('12', plain,
% 1.66/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf('13', plain,
% 1.66/1.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.66/1.89        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf('14', plain,
% 1.66/1.89      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.66/1.89      inference('split', [status(esa)], ['13'])).
% 1.66/1.89  thf('15', plain,
% 1.66/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf(t56_tops_1, axiom,
% 1.66/1.89    (![A:$i]:
% 1.66/1.89     ( ( l1_pre_topc @ A ) =>
% 1.66/1.89       ( ![B:$i]:
% 1.66/1.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.89           ( ![C:$i]:
% 1.66/1.89             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.89               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.66/1.89                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.66/1.89  thf('16', plain,
% 1.66/1.89      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.66/1.89         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.66/1.89          | ~ (v3_pre_topc @ X46 @ X47)
% 1.66/1.89          | ~ (r1_tarski @ X46 @ X48)
% 1.66/1.89          | (r1_tarski @ X46 @ (k1_tops_1 @ X47 @ X48))
% 1.66/1.89          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.66/1.89          | ~ (l1_pre_topc @ X47))),
% 1.66/1.89      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.66/1.89  thf('17', plain,
% 1.66/1.89      (![X0 : $i]:
% 1.66/1.89         (~ (l1_pre_topc @ sk_A)
% 1.66/1.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.89          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.66/1.89          | ~ (r1_tarski @ sk_B @ X0)
% 1.66/1.89          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.66/1.89      inference('sup-', [status(thm)], ['15', '16'])).
% 1.66/1.89  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf('19', plain,
% 1.66/1.89      (![X0 : $i]:
% 1.66/1.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.89          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.66/1.89          | ~ (r1_tarski @ sk_B @ X0)
% 1.66/1.89          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.66/1.89      inference('demod', [status(thm)], ['17', '18'])).
% 1.66/1.89  thf('20', plain,
% 1.66/1.89      ((![X0 : $i]:
% 1.66/1.89          (~ (r1_tarski @ sk_B @ X0)
% 1.66/1.89           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.66/1.89           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.66/1.89         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.66/1.89      inference('sup-', [status(thm)], ['14', '19'])).
% 1.66/1.89  thf('21', plain,
% 1.66/1.89      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.66/1.89         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.66/1.89      inference('sup-', [status(thm)], ['12', '20'])).
% 1.66/1.89  thf(d10_xboole_0, axiom,
% 1.66/1.89    (![A:$i,B:$i]:
% 1.66/1.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.66/1.89  thf('22', plain,
% 1.66/1.89      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 1.66/1.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.66/1.89  thf('23', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 1.66/1.89      inference('simplify', [status(thm)], ['22'])).
% 1.66/1.89  thf('24', plain,
% 1.66/1.89      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.66/1.89         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.66/1.89      inference('demod', [status(thm)], ['21', '23'])).
% 1.66/1.89  thf('25', plain,
% 1.66/1.89      (![X14 : $i, X16 : $i]:
% 1.66/1.89         (((X14) = (X16))
% 1.66/1.89          | ~ (r1_tarski @ X16 @ X14)
% 1.66/1.89          | ~ (r1_tarski @ X14 @ X16))),
% 1.66/1.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.66/1.89  thf('26', plain,
% 1.66/1.89      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.66/1.89         | ((k1_tops_1 @ sk_A @ sk_B) = (sk_B))))
% 1.66/1.89         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.66/1.89      inference('sup-', [status(thm)], ['24', '25'])).
% 1.66/1.89  thf('27', plain,
% 1.66/1.89      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.66/1.89         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.66/1.89      inference('sup-', [status(thm)], ['11', '26'])).
% 1.66/1.89  thf('28', plain,
% 1.66/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf(l78_tops_1, axiom,
% 1.66/1.89    (![A:$i]:
% 1.66/1.89     ( ( l1_pre_topc @ A ) =>
% 1.66/1.89       ( ![B:$i]:
% 1.66/1.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.89           ( ( k2_tops_1 @ A @ B ) =
% 1.66/1.89             ( k7_subset_1 @
% 1.66/1.89               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.66/1.89               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.66/1.89  thf('29', plain,
% 1.66/1.89      (![X44 : $i, X45 : $i]:
% 1.66/1.89         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.66/1.89          | ((k2_tops_1 @ X45 @ X44)
% 1.66/1.89              = (k7_subset_1 @ (u1_struct_0 @ X45) @ 
% 1.66/1.89                 (k2_pre_topc @ X45 @ X44) @ (k1_tops_1 @ X45 @ X44)))
% 1.66/1.89          | ~ (l1_pre_topc @ X45))),
% 1.66/1.89      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.66/1.89  thf('30', plain,
% 1.66/1.89      ((~ (l1_pre_topc @ sk_A)
% 1.66/1.89        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.66/1.89      inference('sup-', [status(thm)], ['28', '29'])).
% 1.66/1.89  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf('32', plain,
% 1.66/1.89      (((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.66/1.89            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.66/1.89      inference('demod', [status(thm)], ['30', '31'])).
% 1.66/1.89  thf('33', plain,
% 1.66/1.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.66/1.89         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.66/1.89      inference('sup+', [status(thm)], ['27', '32'])).
% 1.66/1.89  thf('34', plain,
% 1.66/1.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.66/1.89         <= (~
% 1.66/1.89             (((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('split', [status(esa)], ['0'])).
% 1.66/1.89  thf('35', plain,
% 1.66/1.89      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.66/1.89         <= (~
% 1.66/1.89             (((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.66/1.89             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.66/1.89      inference('sup-', [status(thm)], ['33', '34'])).
% 1.66/1.89  thf('36', plain,
% 1.66/1.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.66/1.89       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.66/1.89      inference('simplify', [status(thm)], ['35'])).
% 1.66/1.89  thf('37', plain,
% 1.66/1.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.66/1.89       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.66/1.89      inference('split', [status(esa)], ['13'])).
% 1.66/1.89  thf(d4_xboole_0, axiom,
% 1.66/1.89    (![A:$i,B:$i,C:$i]:
% 1.66/1.89     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.66/1.89       ( ![D:$i]:
% 1.66/1.89         ( ( r2_hidden @ D @ C ) <=>
% 1.66/1.89           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.66/1.89  thf('38', plain,
% 1.66/1.89      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.66/1.89         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.66/1.89          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.66/1.89          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.66/1.89      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.66/1.89  thf(t3_boole, axiom,
% 1.66/1.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.66/1.89  thf('39', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 1.66/1.89      inference('cnf', [status(esa)], [t3_boole])).
% 1.66/1.89  thf(d5_xboole_0, axiom,
% 1.66/1.89    (![A:$i,B:$i,C:$i]:
% 1.66/1.89     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.66/1.89       ( ![D:$i]:
% 1.66/1.89         ( ( r2_hidden @ D @ C ) <=>
% 1.66/1.89           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.66/1.89  thf('40', plain,
% 1.66/1.89      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.66/1.89         (~ (r2_hidden @ X12 @ X11)
% 1.66/1.89          | ~ (r2_hidden @ X12 @ X10)
% 1.66/1.89          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 1.66/1.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.66/1.89  thf('41', plain,
% 1.66/1.89      (![X9 : $i, X10 : $i, X12 : $i]:
% 1.66/1.89         (~ (r2_hidden @ X12 @ X10)
% 1.66/1.89          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.66/1.89      inference('simplify', [status(thm)], ['40'])).
% 1.66/1.89  thf('42', plain,
% 1.66/1.89      (![X0 : $i, X1 : $i]:
% 1.66/1.89         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.66/1.89      inference('sup-', [status(thm)], ['39', '41'])).
% 1.66/1.89  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.66/1.89      inference('condensation', [status(thm)], ['42'])).
% 1.66/1.89  thf('44', plain,
% 1.66/1.89      (![X0 : $i, X1 : $i]:
% 1.66/1.89         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.66/1.89          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.66/1.89      inference('sup-', [status(thm)], ['38', '43'])).
% 1.66/1.89  thf('45', plain,
% 1.66/1.89      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.66/1.89         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.66/1.89          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.66/1.89          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.66/1.89      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.66/1.89  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.66/1.89      inference('condensation', [status(thm)], ['42'])).
% 1.66/1.89  thf('47', plain,
% 1.66/1.89      (![X0 : $i, X1 : $i]:
% 1.66/1.89         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.66/1.89          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.66/1.89      inference('sup-', [status(thm)], ['45', '46'])).
% 1.66/1.89  thf('48', plain,
% 1.66/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf(dt_k2_pre_topc, axiom,
% 1.66/1.89    (![A:$i,B:$i]:
% 1.66/1.89     ( ( ( l1_pre_topc @ A ) & 
% 1.66/1.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.66/1.89       ( m1_subset_1 @
% 1.66/1.89         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.66/1.89  thf('49', plain,
% 1.66/1.89      (![X40 : $i, X41 : $i]:
% 1.66/1.89         (~ (l1_pre_topc @ X40)
% 1.66/1.89          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.66/1.89          | (m1_subset_1 @ (k2_pre_topc @ X40 @ X41) @ 
% 1.66/1.89             (k1_zfmisc_1 @ (u1_struct_0 @ X40))))),
% 1.66/1.89      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.66/1.89  thf('50', plain,
% 1.66/1.89      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.66/1.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.89        | ~ (l1_pre_topc @ sk_A))),
% 1.66/1.89      inference('sup-', [status(thm)], ['48', '49'])).
% 1.66/1.89  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf('52', plain,
% 1.66/1.89      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.66/1.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.89      inference('demod', [status(thm)], ['50', '51'])).
% 1.66/1.89  thf('53', plain,
% 1.66/1.89      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.66/1.89         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 1.66/1.89          | ((k7_subset_1 @ X33 @ X32 @ X34) = (k4_xboole_0 @ X32 @ X34)))),
% 1.66/1.89      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.66/1.89  thf('54', plain,
% 1.66/1.89      (![X0 : $i]:
% 1.66/1.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.66/1.89           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.66/1.89      inference('sup-', [status(thm)], ['52', '53'])).
% 1.66/1.89  thf('55', plain,
% 1.66/1.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('split', [status(esa)], ['13'])).
% 1.66/1.89  thf('56', plain,
% 1.66/1.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('sup+', [status(thm)], ['54', '55'])).
% 1.66/1.89  thf('57', plain,
% 1.66/1.89      (![X9 : $i, X10 : $i, X12 : $i]:
% 1.66/1.89         (~ (r2_hidden @ X12 @ X10)
% 1.66/1.89          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.66/1.89      inference('simplify', [status(thm)], ['40'])).
% 1.66/1.89  thf('58', plain,
% 1.66/1.89      ((![X0 : $i]:
% 1.66/1.89          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.66/1.89           | ~ (r2_hidden @ X0 @ sk_B)))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('sup-', [status(thm)], ['56', '57'])).
% 1.66/1.89  thf('59', plain,
% 1.66/1.89      ((![X0 : $i]:
% 1.66/1.89          (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.66/1.89           | ~ (r2_hidden @ 
% 1.66/1.89                (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('sup-', [status(thm)], ['47', '58'])).
% 1.66/1.89  thf('60', plain,
% 1.66/1.89      (((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.66/1.89         | ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('sup-', [status(thm)], ['44', '59'])).
% 1.66/1.89  thf('61', plain,
% 1.66/1.89      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('simplify', [status(thm)], ['60'])).
% 1.66/1.89  thf(t100_xboole_1, axiom,
% 1.66/1.89    (![A:$i,B:$i]:
% 1.66/1.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.66/1.89  thf('62', plain,
% 1.66/1.89      (![X17 : $i, X18 : $i]:
% 1.66/1.89         ((k4_xboole_0 @ X17 @ X18)
% 1.66/1.89           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.66/1.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.66/1.89  thf('63', plain,
% 1.66/1.89      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.66/1.89          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('sup+', [status(thm)], ['61', '62'])).
% 1.66/1.89  thf(t46_xboole_1, axiom,
% 1.66/1.89    (![A:$i,B:$i]:
% 1.66/1.89     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.66/1.89  thf('64', plain,
% 1.66/1.89      (![X24 : $i, X25 : $i]:
% 1.66/1.89         ((k4_xboole_0 @ X24 @ (k2_xboole_0 @ X24 @ X25)) = (k1_xboole_0))),
% 1.66/1.89      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.66/1.89  thf('65', plain,
% 1.66/1.89      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 1.66/1.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.66/1.89  thf('66', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.66/1.89      inference('sup+', [status(thm)], ['64', '65'])).
% 1.66/1.89  thf(t28_xboole_1, axiom,
% 1.66/1.89    (![A:$i,B:$i]:
% 1.66/1.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.66/1.89  thf('67', plain,
% 1.66/1.89      (![X19 : $i, X20 : $i]:
% 1.66/1.89         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 1.66/1.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.66/1.89  thf('68', plain,
% 1.66/1.89      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.66/1.89      inference('sup-', [status(thm)], ['66', '67'])).
% 1.66/1.89  thf(commutativity_k3_xboole_0, axiom,
% 1.66/1.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.66/1.89  thf('69', plain,
% 1.66/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.66/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.66/1.89  thf('70', plain,
% 1.66/1.89      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.66/1.89      inference('sup+', [status(thm)], ['68', '69'])).
% 1.66/1.89  thf('71', plain,
% 1.66/1.89      (![X17 : $i, X18 : $i]:
% 1.66/1.89         ((k4_xboole_0 @ X17 @ X18)
% 1.66/1.89           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.66/1.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.66/1.89  thf('72', plain,
% 1.66/1.89      (![X0 : $i]:
% 1.66/1.89         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.66/1.89      inference('sup+', [status(thm)], ['70', '71'])).
% 1.66/1.89  thf('73', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 1.66/1.89      inference('cnf', [status(esa)], [t3_boole])).
% 1.66/1.89  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.66/1.89      inference('sup+', [status(thm)], ['72', '73'])).
% 1.66/1.89  thf('75', plain,
% 1.66/1.89      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('demod', [status(thm)], ['63', '74'])).
% 1.66/1.89  thf('76', plain,
% 1.66/1.89      (((k1_tops_1 @ sk_A @ sk_B)
% 1.66/1.89         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.66/1.89      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.66/1.89  thf('77', plain,
% 1.66/1.89      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('sup+', [status(thm)], ['75', '76'])).
% 1.66/1.89  thf('78', plain,
% 1.66/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf(fc9_tops_1, axiom,
% 1.66/1.89    (![A:$i,B:$i]:
% 1.66/1.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.66/1.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.66/1.89       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.66/1.89  thf('79', plain,
% 1.66/1.89      (![X42 : $i, X43 : $i]:
% 1.66/1.89         (~ (l1_pre_topc @ X42)
% 1.66/1.89          | ~ (v2_pre_topc @ X42)
% 1.66/1.89          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.66/1.89          | (v3_pre_topc @ (k1_tops_1 @ X42 @ X43) @ X42))),
% 1.66/1.89      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.66/1.89  thf('80', plain,
% 1.66/1.89      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.66/1.89        | ~ (v2_pre_topc @ sk_A)
% 1.66/1.89        | ~ (l1_pre_topc @ sk_A))),
% 1.66/1.89      inference('sup-', [status(thm)], ['78', '79'])).
% 1.66/1.89  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 1.66/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.89  thf('83', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.66/1.89      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.66/1.89  thf('84', plain,
% 1.66/1.89      (((v3_pre_topc @ sk_B @ sk_A))
% 1.66/1.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.66/1.89      inference('sup+', [status(thm)], ['77', '83'])).
% 1.66/1.89  thf('85', plain,
% 1.66/1.89      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.66/1.89      inference('split', [status(esa)], ['0'])).
% 1.66/1.89  thf('86', plain,
% 1.66/1.89      (~
% 1.66/1.89       (((k2_tops_1 @ sk_A @ sk_B)
% 1.66/1.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.66/1.89       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.66/1.89      inference('sup-', [status(thm)], ['84', '85'])).
% 1.66/1.89  thf('87', plain, ($false),
% 1.66/1.89      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '86'])).
% 1.66/1.89  
% 1.66/1.89  % SZS output end Refutation
% 1.66/1.89  
% 1.66/1.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
