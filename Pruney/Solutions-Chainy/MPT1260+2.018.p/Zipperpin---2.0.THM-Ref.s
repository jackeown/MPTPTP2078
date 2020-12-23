%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cJmdJF3EPH

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:24 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 229 expanded)
%              Number of leaves         :   41 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          : 1369 (2804 expanded)
%              Number of equality atoms :   84 ( 160 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k1_tops_1 @ X46 @ X45 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 @ ( k2_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k7_subset_1 @ X30 @ X29 @ X31 )
        = ( k4_xboole_0 @ X29 @ X31 ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v3_pre_topc @ X40 @ X41 )
      | ~ ( r1_tarski @ X40 @ X42 )
      | ( r1_tarski @ X40 @ ( k1_tops_1 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k2_tops_1 @ X39 @ X38 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_pre_topc @ X39 @ X38 ) @ ( k1_tops_1 @ X39 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
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
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
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

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('48',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['44'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('53',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X27 @ X26 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('62',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k2_pre_topc @ X44 @ X43 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X44 ) @ X43 @ ( k2_tops_1 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k7_subset_1 @ X30 @ X29 @ X31 )
        = ( k4_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','72'])).

thf('74',plain,
    ( ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','73'])).

thf('75',plain,
    ( ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('76',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('78',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('81',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('82',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) ) @ X18 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('84',plain,(
    ! [X20: $i] :
      ( r1_tarski @ k1_xboole_0 @ X20 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('85',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','87'])).

thf('89',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','92'])).

thf('94',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('97',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X36 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('98',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['95','101'])).

thf('103',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cJmdJF3EPH
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:08:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.67/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.87  % Solved by: fo/fo7.sh
% 0.67/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.87  % done 684 iterations in 0.416s
% 0.67/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.87  % SZS output start Refutation
% 0.67/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.67/0.87  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.67/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.87  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.67/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.67/0.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.87  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.67/0.87  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.67/0.87  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.67/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.87  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.67/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.67/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.87  thf(t76_tops_1, conjecture,
% 0.67/0.87    (![A:$i]:
% 0.67/0.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.87       ( ![B:$i]:
% 0.67/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.87           ( ( v3_pre_topc @ B @ A ) <=>
% 0.67/0.87             ( ( k2_tops_1 @ A @ B ) =
% 0.67/0.87               ( k7_subset_1 @
% 0.67/0.87                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.67/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.87    (~( ![A:$i]:
% 0.67/0.87        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.87          ( ![B:$i]:
% 0.67/0.87            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.87              ( ( v3_pre_topc @ B @ A ) <=>
% 0.67/0.87                ( ( k2_tops_1 @ A @ B ) =
% 0.67/0.87                  ( k7_subset_1 @
% 0.67/0.87                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.67/0.87    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.67/0.87  thf('0', plain,
% 0.67/0.87      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.67/0.87        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('1', plain,
% 0.67/0.87      (~
% 0.67/0.87       (((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.67/0.87       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.67/0.87      inference('split', [status(esa)], ['0'])).
% 0.67/0.87  thf('2', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(t74_tops_1, axiom,
% 0.67/0.87    (![A:$i]:
% 0.67/0.87     ( ( l1_pre_topc @ A ) =>
% 0.67/0.87       ( ![B:$i]:
% 0.67/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.87           ( ( k1_tops_1 @ A @ B ) =
% 0.67/0.87             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.67/0.87  thf('3', plain,
% 0.67/0.87      (![X45 : $i, X46 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.67/0.87          | ((k1_tops_1 @ X46 @ X45)
% 0.67/0.87              = (k7_subset_1 @ (u1_struct_0 @ X46) @ X45 @ 
% 0.67/0.87                 (k2_tops_1 @ X46 @ X45)))
% 0.67/0.87          | ~ (l1_pre_topc @ X46))),
% 0.67/0.87      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.67/0.87  thf('4', plain,
% 0.67/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.87        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.67/0.87            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.67/0.87               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.87  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('6', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(redefinition_k7_subset_1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.87       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.67/0.87  thf('7', plain,
% 0.67/0.87      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.67/0.87          | ((k7_subset_1 @ X30 @ X29 @ X31) = (k4_xboole_0 @ X29 @ X31)))),
% 0.67/0.87      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.67/0.87  thf('8', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.67/0.87           = (k4_xboole_0 @ sk_B @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['6', '7'])).
% 0.67/0.87  thf('9', plain,
% 0.67/0.87      (((k1_tops_1 @ sk_A @ sk_B)
% 0.67/0.87         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.67/0.87      inference('demod', [status(thm)], ['4', '5', '8'])).
% 0.67/0.87  thf(t36_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.67/0.87  thf('10', plain,
% 0.67/0.87      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.67/0.87      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.67/0.87  thf('11', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.67/0.87      inference('sup+', [status(thm)], ['9', '10'])).
% 0.67/0.87  thf('12', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('13', plain,
% 0.67/0.87      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.67/0.87        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('14', plain,
% 0.67/0.87      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.87      inference('split', [status(esa)], ['13'])).
% 0.67/0.87  thf('15', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(t56_tops_1, axiom,
% 0.67/0.87    (![A:$i]:
% 0.67/0.87     ( ( l1_pre_topc @ A ) =>
% 0.67/0.87       ( ![B:$i]:
% 0.67/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.87           ( ![C:$i]:
% 0.67/0.87             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.87               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.67/0.87                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.67/0.87  thf('16', plain,
% 0.67/0.87      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.67/0.87          | ~ (v3_pre_topc @ X40 @ X41)
% 0.67/0.87          | ~ (r1_tarski @ X40 @ X42)
% 0.67/0.87          | (r1_tarski @ X40 @ (k1_tops_1 @ X41 @ X42))
% 0.67/0.87          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.67/0.87          | ~ (l1_pre_topc @ X41))),
% 0.67/0.87      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.67/0.87  thf('17', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         (~ (l1_pre_topc @ sk_A)
% 0.67/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.87          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.67/0.87          | ~ (r1_tarski @ sk_B @ X0)
% 0.67/0.87          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.67/0.87      inference('sup-', [status(thm)], ['15', '16'])).
% 0.67/0.87  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('19', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.87          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.67/0.87          | ~ (r1_tarski @ sk_B @ X0)
% 0.67/0.87          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.67/0.87      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.87  thf('20', plain,
% 0.67/0.87      ((![X0 : $i]:
% 0.67/0.87          (~ (r1_tarski @ sk_B @ X0)
% 0.67/0.87           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.67/0.87           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.67/0.87         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['14', '19'])).
% 0.67/0.87  thf('21', plain,
% 0.67/0.87      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.67/0.87         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['12', '20'])).
% 0.67/0.87  thf(d10_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.87  thf('22', plain,
% 0.67/0.87      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.67/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.87  thf('23', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.67/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.67/0.87  thf('24', plain,
% 0.67/0.87      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.67/0.87         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.87      inference('demod', [status(thm)], ['21', '23'])).
% 0.67/0.87  thf('25', plain,
% 0.67/0.87      (![X13 : $i, X15 : $i]:
% 0.67/0.87         (((X13) = (X15))
% 0.67/0.87          | ~ (r1_tarski @ X15 @ X13)
% 0.67/0.87          | ~ (r1_tarski @ X13 @ X15))),
% 0.67/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.87  thf('26', plain,
% 0.67/0.87      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.67/0.87         | ((k1_tops_1 @ sk_A @ sk_B) = (sk_B))))
% 0.67/0.87         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['24', '25'])).
% 0.67/0.87  thf('27', plain,
% 0.67/0.87      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.67/0.87         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['11', '26'])).
% 0.67/0.87  thf('28', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(l78_tops_1, axiom,
% 0.67/0.87    (![A:$i]:
% 0.67/0.87     ( ( l1_pre_topc @ A ) =>
% 0.67/0.87       ( ![B:$i]:
% 0.67/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.87           ( ( k2_tops_1 @ A @ B ) =
% 0.67/0.87             ( k7_subset_1 @
% 0.67/0.87               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.67/0.87               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.67/0.87  thf('29', plain,
% 0.67/0.87      (![X38 : $i, X39 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.67/0.87          | ((k2_tops_1 @ X39 @ X38)
% 0.67/0.87              = (k7_subset_1 @ (u1_struct_0 @ X39) @ 
% 0.67/0.87                 (k2_pre_topc @ X39 @ X38) @ (k1_tops_1 @ X39 @ X38)))
% 0.67/0.87          | ~ (l1_pre_topc @ X39))),
% 0.67/0.87      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.67/0.87  thf('30', plain,
% 0.67/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.87        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.87  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('32', plain,
% 0.67/0.87      (((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.67/0.87            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.67/0.87      inference('demod', [status(thm)], ['30', '31'])).
% 0.67/0.87  thf('33', plain,
% 0.67/0.87      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.67/0.87         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.87      inference('sup+', [status(thm)], ['27', '32'])).
% 0.67/0.87  thf('34', plain,
% 0.67/0.87      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.67/0.87         <= (~
% 0.67/0.87             (((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('split', [status(esa)], ['0'])).
% 0.67/0.87  thf('35', plain,
% 0.67/0.87      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.67/0.87         <= (~
% 0.67/0.87             (((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.67/0.87             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.87  thf('36', plain,
% 0.67/0.87      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.67/0.87       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.67/0.87      inference('simplify', [status(thm)], ['35'])).
% 0.67/0.87  thf('37', plain,
% 0.67/0.87      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.67/0.87       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.67/0.87      inference('split', [status(esa)], ['13'])).
% 0.67/0.87  thf(d4_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.67/0.87       ( ![D:$i]:
% 0.67/0.87         ( ( r2_hidden @ D @ C ) <=>
% 0.67/0.87           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.67/0.87  thf('38', plain,
% 0.67/0.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.67/0.87         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.67/0.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.67/0.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.67/0.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.67/0.87  thf(t12_setfam_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.67/0.87  thf('39', plain,
% 0.67/0.87      (![X32 : $i, X33 : $i]:
% 0.67/0.87         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.67/0.87      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.67/0.87  thf('40', plain,
% 0.67/0.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.67/0.87         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.67/0.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.67/0.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.67/0.87      inference('demod', [status(thm)], ['38', '39'])).
% 0.67/0.87  thf(t3_boole, axiom,
% 0.67/0.87    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.87  thf('41', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.67/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.87  thf(d5_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.67/0.87       ( ![D:$i]:
% 0.67/0.87         ( ( r2_hidden @ D @ C ) <=>
% 0.67/0.87           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.67/0.87  thf('42', plain,
% 0.67/0.87      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X10 @ X9)
% 0.67/0.87          | ~ (r2_hidden @ X10 @ X8)
% 0.67/0.87          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.67/0.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.67/0.87  thf('43', plain,
% 0.67/0.87      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X10 @ X8)
% 0.67/0.87          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['42'])).
% 0.67/0.87  thf('44', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['41', '43'])).
% 0.67/0.87  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.67/0.87      inference('condensation', [status(thm)], ['44'])).
% 0.67/0.87  thf('46', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.67/0.87          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['40', '45'])).
% 0.67/0.87  thf('47', plain,
% 0.67/0.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.67/0.87         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.67/0.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.67/0.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.67/0.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.67/0.87  thf('48', plain,
% 0.67/0.87      (![X32 : $i, X33 : $i]:
% 0.67/0.87         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.67/0.87      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.67/0.87  thf('49', plain,
% 0.67/0.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.67/0.87         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.67/0.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.67/0.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.67/0.87      inference('demod', [status(thm)], ['47', '48'])).
% 0.67/0.87  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.67/0.87      inference('condensation', [status(thm)], ['44'])).
% 0.67/0.87  thf('51', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.67/0.87          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.87  thf('52', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(dt_k2_tops_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( ( l1_pre_topc @ A ) & 
% 0.67/0.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.87       ( m1_subset_1 @
% 0.67/0.87         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.67/0.87  thf('53', plain,
% 0.67/0.87      (![X34 : $i, X35 : $i]:
% 0.67/0.87         (~ (l1_pre_topc @ X34)
% 0.67/0.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.67/0.87          | (m1_subset_1 @ (k2_tops_1 @ X34 @ X35) @ 
% 0.67/0.87             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 0.67/0.87      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.67/0.87  thf('54', plain,
% 0.67/0.87      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.67/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.87      inference('sup-', [status(thm)], ['52', '53'])).
% 0.67/0.87  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('56', plain,
% 0.67/0.87      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.67/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('demod', [status(thm)], ['54', '55'])).
% 0.67/0.87  thf('57', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(dt_k4_subset_1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.67/0.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.67/0.87       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.67/0.87  thf('58', plain,
% 0.67/0.87      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.67/0.87          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27))
% 0.67/0.87          | (m1_subset_1 @ (k4_subset_1 @ X27 @ X26 @ X28) @ 
% 0.67/0.87             (k1_zfmisc_1 @ X27)))),
% 0.67/0.87      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.67/0.87  thf('59', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.67/0.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['57', '58'])).
% 0.67/0.87  thf('60', plain,
% 0.67/0.87      ((m1_subset_1 @ 
% 0.67/0.87        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.67/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['56', '59'])).
% 0.67/0.87  thf('61', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(t65_tops_1, axiom,
% 0.67/0.87    (![A:$i]:
% 0.67/0.87     ( ( l1_pre_topc @ A ) =>
% 0.67/0.87       ( ![B:$i]:
% 0.67/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.87           ( ( k2_pre_topc @ A @ B ) =
% 0.67/0.87             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.67/0.87  thf('62', plain,
% 0.67/0.87      (![X43 : $i, X44 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.67/0.87          | ((k2_pre_topc @ X44 @ X43)
% 0.67/0.87              = (k4_subset_1 @ (u1_struct_0 @ X44) @ X43 @ 
% 0.67/0.87                 (k2_tops_1 @ X44 @ X43)))
% 0.67/0.87          | ~ (l1_pre_topc @ X44))),
% 0.67/0.87      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.67/0.87  thf('63', plain,
% 0.67/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.87        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.67/0.87            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.67/0.87               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['61', '62'])).
% 0.67/0.87  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('65', plain,
% 0.67/0.87      (((k2_pre_topc @ sk_A @ sk_B)
% 0.67/0.87         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.67/0.87            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.67/0.87      inference('demod', [status(thm)], ['63', '64'])).
% 0.67/0.87  thf('66', plain,
% 0.67/0.87      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.67/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('demod', [status(thm)], ['60', '65'])).
% 0.67/0.87  thf('67', plain,
% 0.67/0.87      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.67/0.87          | ((k7_subset_1 @ X30 @ X29 @ X31) = (k4_xboole_0 @ X29 @ X31)))),
% 0.67/0.87      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.67/0.87  thf('68', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.67/0.87           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['66', '67'])).
% 0.67/0.87  thf('69', plain,
% 0.67/0.87      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('split', [status(esa)], ['13'])).
% 0.67/0.87  thf('70', plain,
% 0.67/0.87      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('sup+', [status(thm)], ['68', '69'])).
% 0.67/0.87  thf('71', plain,
% 0.67/0.87      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X10 @ X8)
% 0.67/0.87          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['42'])).
% 0.67/0.87  thf('72', plain,
% 0.67/0.87      ((![X0 : $i]:
% 0.67/0.87          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.67/0.87           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['70', '71'])).
% 0.67/0.87  thf('73', plain,
% 0.67/0.87      ((![X0 : $i]:
% 0.67/0.87          (((k1_xboole_0)
% 0.67/0.87             = (k1_setfam_1 @ (k2_tarski @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.67/0.87           | ~ (r2_hidden @ 
% 0.67/0.87                (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['51', '72'])).
% 0.67/0.87  thf('74', plain,
% 0.67/0.87      (((((k1_xboole_0)
% 0.67/0.87           = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.67/0.87         | ((k1_xboole_0)
% 0.67/0.87             = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['46', '73'])).
% 0.67/0.87  thf('75', plain,
% 0.67/0.87      ((((k1_xboole_0)
% 0.67/0.87          = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('simplify', [status(thm)], ['74'])).
% 0.67/0.87  thf(t100_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.87  thf('76', plain,
% 0.67/0.87      (![X16 : $i, X17 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X16 @ X17)
% 0.67/0.87           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.87  thf('77', plain,
% 0.67/0.87      (![X32 : $i, X33 : $i]:
% 0.67/0.87         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.67/0.87      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.67/0.87  thf('78', plain,
% 0.67/0.87      (![X16 : $i, X17 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X16 @ X17)
% 0.67/0.87           = (k5_xboole_0 @ X16 @ (k1_setfam_1 @ (k2_tarski @ X16 @ X17))))),
% 0.67/0.87      inference('demod', [status(thm)], ['76', '77'])).
% 0.67/0.87  thf('79', plain,
% 0.67/0.87      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.67/0.87          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('sup+', [status(thm)], ['75', '78'])).
% 0.67/0.87  thf(commutativity_k2_tarski, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.67/0.87  thf('80', plain,
% 0.67/0.87      (![X24 : $i, X25 : $i]:
% 0.67/0.87         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 0.67/0.87      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.67/0.87  thf(t17_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.67/0.87  thf('81', plain,
% 0.67/0.87      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 0.67/0.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.67/0.87  thf('82', plain,
% 0.67/0.87      (![X32 : $i, X33 : $i]:
% 0.67/0.87         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.67/0.87      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.67/0.87  thf('83', plain,
% 0.67/0.87      (![X18 : $i, X19 : $i]:
% 0.67/0.87         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X18 @ X19)) @ X18)),
% 0.67/0.87      inference('demod', [status(thm)], ['81', '82'])).
% 0.67/0.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.67/0.87  thf('84', plain, (![X20 : $i]: (r1_tarski @ k1_xboole_0 @ X20)),
% 0.67/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.87  thf('85', plain,
% 0.67/0.87      (![X13 : $i, X15 : $i]:
% 0.67/0.87         (((X13) = (X15))
% 0.67/0.87          | ~ (r1_tarski @ X15 @ X13)
% 0.67/0.87          | ~ (r1_tarski @ X13 @ X15))),
% 0.67/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.87  thf('86', plain,
% 0.67/0.87      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.87  thf('87', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['83', '86'])).
% 0.67/0.87  thf('88', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['80', '87'])).
% 0.67/0.87  thf('89', plain,
% 0.67/0.87      (![X16 : $i, X17 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X16 @ X17)
% 0.67/0.87           = (k5_xboole_0 @ X16 @ (k1_setfam_1 @ (k2_tarski @ X16 @ X17))))),
% 0.67/0.87      inference('demod', [status(thm)], ['76', '77'])).
% 0.67/0.87  thf('90', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['88', '89'])).
% 0.67/0.87  thf('91', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.67/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.87  thf('92', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['90', '91'])).
% 0.67/0.87  thf('93', plain,
% 0.67/0.87      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('demod', [status(thm)], ['79', '92'])).
% 0.67/0.87  thf('94', plain,
% 0.67/0.87      (((k1_tops_1 @ sk_A @ sk_B)
% 0.67/0.87         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.67/0.87      inference('demod', [status(thm)], ['4', '5', '8'])).
% 0.67/0.87  thf('95', plain,
% 0.67/0.87      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('sup+', [status(thm)], ['93', '94'])).
% 0.67/0.87  thf('96', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(fc9_tops_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.67/0.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.87       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.67/0.87  thf('97', plain,
% 0.67/0.87      (![X36 : $i, X37 : $i]:
% 0.67/0.87         (~ (l1_pre_topc @ X36)
% 0.67/0.87          | ~ (v2_pre_topc @ X36)
% 0.67/0.87          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.67/0.87          | (v3_pre_topc @ (k1_tops_1 @ X36 @ X37) @ X36))),
% 0.67/0.87      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.67/0.87  thf('98', plain,
% 0.67/0.87      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.67/0.87        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.87      inference('sup-', [status(thm)], ['96', '97'])).
% 0.67/0.87  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('101', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.67/0.87      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.67/0.87  thf('102', plain,
% 0.67/0.87      (((v3_pre_topc @ sk_B @ sk_A))
% 0.67/0.87         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.67/0.87      inference('sup+', [status(thm)], ['95', '101'])).
% 0.67/0.87  thf('103', plain,
% 0.67/0.87      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.87      inference('split', [status(esa)], ['0'])).
% 0.67/0.87  thf('104', plain,
% 0.67/0.87      (~
% 0.67/0.87       (((k2_tops_1 @ sk_A @ sk_B)
% 0.67/0.87          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.87             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.67/0.87       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.67/0.87      inference('sup-', [status(thm)], ['102', '103'])).
% 0.67/0.87  thf('105', plain, ($false),
% 0.67/0.87      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '104'])).
% 0.67/0.87  
% 0.67/0.87  % SZS output end Refutation
% 0.67/0.87  
% 0.67/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
