%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ygt0ZuJmHw

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:24 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 196 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          : 1182 (2428 expanded)
%              Number of equality atoms :   76 ( 140 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k1_tops_1 @ X53 @ X52 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X53 ) @ X52 @ ( k2_tops_1 @ X53 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k7_subset_1 @ X34 @ X33 @ X35 )
        = ( k4_xboole_0 @ X33 @ X35 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v3_pre_topc @ X47 @ X48 )
      | ~ ( r1_tarski @ X47 @ X49 )
      | ( r1_tarski @ X47 @ ( k1_tops_1 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
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
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_tops_1 @ X46 @ X45 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X46 ) @ ( k2_pre_topc @ X46 @ X45 ) @ ( k1_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

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
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
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

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('53',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k7_subset_1 @ X34 @ X33 @ X35 )
        = ( k4_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,
    ( ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','63'])).

thf('65',plain,
    ( ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('68',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('73',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

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
    inference(demod,[status(thm)],['69','74'])).

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
    ! [X43: $i,X44: $i] :
      ( ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X43 @ X44 ) @ X43 ) ) ),
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
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ygt0ZuJmHw
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.88  % Solved by: fo/fo7.sh
% 1.65/1.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.88  % done 1981 iterations in 1.423s
% 1.65/1.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.88  % SZS output start Refutation
% 1.65/1.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.65/1.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.65/1.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.65/1.88  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.65/1.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.65/1.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.88  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.65/1.88  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.65/1.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.65/1.88  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.65/1.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.65/1.88  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.65/1.88  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.65/1.88  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.88  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.65/1.88  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.65/1.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.88  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.65/1.88  thf(t76_tops_1, conjecture,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88           ( ( v3_pre_topc @ B @ A ) <=>
% 1.65/1.88             ( ( k2_tops_1 @ A @ B ) =
% 1.65/1.88               ( k7_subset_1 @
% 1.65/1.88                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.65/1.88  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.88    (~( ![A:$i]:
% 1.65/1.88        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.65/1.88          ( ![B:$i]:
% 1.65/1.88            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88              ( ( v3_pre_topc @ B @ A ) <=>
% 1.65/1.88                ( ( k2_tops_1 @ A @ B ) =
% 1.65/1.88                  ( k7_subset_1 @
% 1.65/1.88                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.65/1.88    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.65/1.88  thf('0', plain,
% 1.65/1.88      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.65/1.88        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('1', plain,
% 1.65/1.88      (~
% 1.65/1.88       (((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.65/1.88       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.65/1.88      inference('split', [status(esa)], ['0'])).
% 1.65/1.88  thf('2', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(t74_tops_1, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( l1_pre_topc @ A ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88           ( ( k1_tops_1 @ A @ B ) =
% 1.65/1.88             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.65/1.88  thf('3', plain,
% 1.65/1.88      (![X52 : $i, X53 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 1.65/1.88          | ((k1_tops_1 @ X53 @ X52)
% 1.65/1.88              = (k7_subset_1 @ (u1_struct_0 @ X53) @ X52 @ 
% 1.65/1.88                 (k2_tops_1 @ X53 @ X52)))
% 1.65/1.88          | ~ (l1_pre_topc @ X53))),
% 1.65/1.88      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.65/1.88  thf('4', plain,
% 1.65/1.88      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.88        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.65/1.88            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.65/1.88               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['2', '3'])).
% 1.65/1.88  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('6', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(redefinition_k7_subset_1, axiom,
% 1.65/1.88    (![A:$i,B:$i,C:$i]:
% 1.65/1.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.88       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.65/1.88  thf('7', plain,
% 1.65/1.88      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 1.65/1.88          | ((k7_subset_1 @ X34 @ X33 @ X35) = (k4_xboole_0 @ X33 @ X35)))),
% 1.65/1.88      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.65/1.88  thf('8', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.65/1.88           = (k4_xboole_0 @ sk_B @ X0))),
% 1.65/1.88      inference('sup-', [status(thm)], ['6', '7'])).
% 1.65/1.88  thf('9', plain,
% 1.65/1.88      (((k1_tops_1 @ sk_A @ sk_B)
% 1.65/1.88         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.88      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.65/1.88  thf(t36_xboole_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.65/1.88  thf('10', plain,
% 1.65/1.88      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 1.65/1.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.65/1.88  thf('11', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.65/1.88      inference('sup+', [status(thm)], ['9', '10'])).
% 1.65/1.88  thf('12', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('13', plain,
% 1.65/1.88      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.65/1.88        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('14', plain,
% 1.65/1.88      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.65/1.88      inference('split', [status(esa)], ['13'])).
% 1.65/1.88  thf('15', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(t56_tops_1, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( l1_pre_topc @ A ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88           ( ![C:$i]:
% 1.65/1.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.65/1.88                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.65/1.88  thf('16', plain,
% 1.65/1.88      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 1.65/1.88          | ~ (v3_pre_topc @ X47 @ X48)
% 1.65/1.88          | ~ (r1_tarski @ X47 @ X49)
% 1.65/1.88          | (r1_tarski @ X47 @ (k1_tops_1 @ X48 @ X49))
% 1.65/1.88          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 1.65/1.88          | ~ (l1_pre_topc @ X48))),
% 1.65/1.88      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.65/1.88  thf('17', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (l1_pre_topc @ sk_A)
% 1.65/1.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.88          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.65/1.88          | ~ (r1_tarski @ sk_B @ X0)
% 1.65/1.88          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.65/1.88      inference('sup-', [status(thm)], ['15', '16'])).
% 1.65/1.88  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('19', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.88          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.65/1.88          | ~ (r1_tarski @ sk_B @ X0)
% 1.65/1.88          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.65/1.88      inference('demod', [status(thm)], ['17', '18'])).
% 1.65/1.88  thf('20', plain,
% 1.65/1.88      ((![X0 : $i]:
% 1.65/1.88          (~ (r1_tarski @ sk_B @ X0)
% 1.65/1.88           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.65/1.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.65/1.88         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['14', '19'])).
% 1.65/1.88  thf('21', plain,
% 1.65/1.88      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.65/1.88         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['12', '20'])).
% 1.65/1.88  thf(d10_xboole_0, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.65/1.88  thf('22', plain,
% 1.65/1.88      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 1.65/1.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.88  thf('23', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.65/1.88      inference('simplify', [status(thm)], ['22'])).
% 1.65/1.88  thf('24', plain,
% 1.65/1.88      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.65/1.88         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.65/1.88      inference('demod', [status(thm)], ['21', '23'])).
% 1.65/1.88  thf('25', plain,
% 1.65/1.88      (![X12 : $i, X14 : $i]:
% 1.65/1.88         (((X12) = (X14))
% 1.65/1.88          | ~ (r1_tarski @ X14 @ X12)
% 1.65/1.88          | ~ (r1_tarski @ X12 @ X14))),
% 1.65/1.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.88  thf('26', plain,
% 1.65/1.88      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.65/1.88         | ((k1_tops_1 @ sk_A @ sk_B) = (sk_B))))
% 1.65/1.88         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['24', '25'])).
% 1.65/1.88  thf('27', plain,
% 1.65/1.88      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.65/1.88         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['11', '26'])).
% 1.65/1.88  thf('28', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(l78_tops_1, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( l1_pre_topc @ A ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88           ( ( k2_tops_1 @ A @ B ) =
% 1.65/1.88             ( k7_subset_1 @
% 1.65/1.88               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.65/1.88               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.65/1.88  thf('29', plain,
% 1.65/1.88      (![X45 : $i, X46 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.65/1.88          | ((k2_tops_1 @ X46 @ X45)
% 1.65/1.88              = (k7_subset_1 @ (u1_struct_0 @ X46) @ 
% 1.65/1.88                 (k2_pre_topc @ X46 @ X45) @ (k1_tops_1 @ X46 @ X45)))
% 1.65/1.88          | ~ (l1_pre_topc @ X46))),
% 1.65/1.88      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.65/1.88  thf('30', plain,
% 1.65/1.88      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.88        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['28', '29'])).
% 1.65/1.88  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('32', plain,
% 1.65/1.88      (((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.65/1.88            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.88      inference('demod', [status(thm)], ['30', '31'])).
% 1.65/1.88  thf('33', plain,
% 1.65/1.88      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.65/1.88         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.65/1.88      inference('sup+', [status(thm)], ['27', '32'])).
% 1.65/1.88  thf('34', plain,
% 1.65/1.88      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.65/1.88         <= (~
% 1.65/1.88             (((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('split', [status(esa)], ['0'])).
% 1.65/1.88  thf('35', plain,
% 1.65/1.88      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.65/1.88         <= (~
% 1.65/1.88             (((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.65/1.88             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['33', '34'])).
% 1.65/1.88  thf('36', plain,
% 1.65/1.88      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.65/1.88       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.65/1.88      inference('simplify', [status(thm)], ['35'])).
% 1.65/1.88  thf('37', plain,
% 1.65/1.88      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.65/1.88       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.65/1.88      inference('split', [status(esa)], ['13'])).
% 1.65/1.88  thf(d4_xboole_0, axiom,
% 1.65/1.88    (![A:$i,B:$i,C:$i]:
% 1.65/1.88     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.65/1.88       ( ![D:$i]:
% 1.65/1.88         ( ( r2_hidden @ D @ C ) <=>
% 1.65/1.88           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.65/1.88  thf('38', plain,
% 1.65/1.88      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.65/1.88         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.65/1.88          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.65/1.88          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.65/1.88      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.65/1.88  thf(t12_setfam_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.65/1.88  thf('39', plain,
% 1.65/1.88      (![X36 : $i, X37 : $i]:
% 1.65/1.88         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 1.65/1.88      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.65/1.88  thf('40', plain,
% 1.65/1.88      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.65/1.88         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 1.65/1.88          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.65/1.88          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.65/1.88      inference('demod', [status(thm)], ['38', '39'])).
% 1.65/1.88  thf(t4_boole, axiom,
% 1.65/1.88    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.65/1.88  thf('41', plain,
% 1.65/1.88      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 1.65/1.88      inference('cnf', [status(esa)], [t4_boole])).
% 1.65/1.88  thf(d5_xboole_0, axiom,
% 1.65/1.88    (![A:$i,B:$i,C:$i]:
% 1.65/1.88     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.65/1.88       ( ![D:$i]:
% 1.65/1.88         ( ( r2_hidden @ D @ C ) <=>
% 1.65/1.88           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.65/1.88  thf('42', plain,
% 1.65/1.88      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.65/1.88         (~ (r2_hidden @ X10 @ X9)
% 1.65/1.88          | ~ (r2_hidden @ X10 @ X8)
% 1.65/1.88          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.65/1.88      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.65/1.88  thf('43', plain,
% 1.65/1.88      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.65/1.88         (~ (r2_hidden @ X10 @ X8)
% 1.65/1.88          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.65/1.88      inference('simplify', [status(thm)], ['42'])).
% 1.65/1.88  thf('44', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 1.65/1.88      inference('sup-', [status(thm)], ['41', '43'])).
% 1.65/1.88  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.65/1.88      inference('condensation', [status(thm)], ['44'])).
% 1.65/1.88  thf('46', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.65/1.88          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['40', '45'])).
% 1.65/1.88  thf('47', plain,
% 1.65/1.88      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.65/1.88         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.65/1.88          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.65/1.88          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.65/1.88      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.65/1.88  thf('48', plain,
% 1.65/1.88      (![X36 : $i, X37 : $i]:
% 1.65/1.88         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 1.65/1.88      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.65/1.88  thf('49', plain,
% 1.65/1.88      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.65/1.88         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 1.65/1.88          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.65/1.88          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.65/1.88      inference('demod', [status(thm)], ['47', '48'])).
% 1.65/1.88  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.65/1.88      inference('condensation', [status(thm)], ['44'])).
% 1.65/1.88  thf('51', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.65/1.88          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['49', '50'])).
% 1.65/1.88  thf('52', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(dt_k2_pre_topc, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( ( l1_pre_topc @ A ) & 
% 1.65/1.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.65/1.88       ( m1_subset_1 @
% 1.65/1.88         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.65/1.88  thf('53', plain,
% 1.65/1.88      (![X41 : $i, X42 : $i]:
% 1.65/1.88         (~ (l1_pre_topc @ X41)
% 1.65/1.88          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 1.65/1.88          | (m1_subset_1 @ (k2_pre_topc @ X41 @ X42) @ 
% 1.65/1.88             (k1_zfmisc_1 @ (u1_struct_0 @ X41))))),
% 1.65/1.88      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.65/1.88  thf('54', plain,
% 1.65/1.88      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.65/1.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.88        | ~ (l1_pre_topc @ sk_A))),
% 1.65/1.88      inference('sup-', [status(thm)], ['52', '53'])).
% 1.65/1.88  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('56', plain,
% 1.65/1.88      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.65/1.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('demod', [status(thm)], ['54', '55'])).
% 1.65/1.88  thf('57', plain,
% 1.65/1.88      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 1.65/1.88          | ((k7_subset_1 @ X34 @ X33 @ X35) = (k4_xboole_0 @ X33 @ X35)))),
% 1.65/1.88      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.65/1.88  thf('58', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.65/1.88           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.65/1.88      inference('sup-', [status(thm)], ['56', '57'])).
% 1.65/1.88  thf('59', plain,
% 1.65/1.88      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('split', [status(esa)], ['13'])).
% 1.65/1.88  thf('60', plain,
% 1.65/1.88      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('sup+', [status(thm)], ['58', '59'])).
% 1.65/1.88  thf('61', plain,
% 1.65/1.88      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.65/1.88         (~ (r2_hidden @ X10 @ X8)
% 1.65/1.88          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.65/1.88      inference('simplify', [status(thm)], ['42'])).
% 1.65/1.88  thf('62', plain,
% 1.65/1.88      ((![X0 : $i]:
% 1.65/1.88          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.65/1.88           | ~ (r2_hidden @ X0 @ sk_B)))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['60', '61'])).
% 1.65/1.88  thf('63', plain,
% 1.65/1.88      ((![X0 : $i]:
% 1.65/1.88          (((k1_xboole_0)
% 1.65/1.88             = (k1_setfam_1 @ (k2_tarski @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.65/1.88           | ~ (r2_hidden @ 
% 1.65/1.88                (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['51', '62'])).
% 1.65/1.88  thf('64', plain,
% 1.65/1.88      (((((k1_xboole_0)
% 1.65/1.88           = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.65/1.88         | ((k1_xboole_0)
% 1.65/1.88             = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['46', '63'])).
% 1.65/1.88  thf('65', plain,
% 1.65/1.88      ((((k1_xboole_0)
% 1.65/1.88          = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('simplify', [status(thm)], ['64'])).
% 1.65/1.88  thf(t100_xboole_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.65/1.88  thf('66', plain,
% 1.65/1.88      (![X15 : $i, X16 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X15 @ X16)
% 1.65/1.88           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.65/1.88      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.65/1.88  thf('67', plain,
% 1.65/1.88      (![X36 : $i, X37 : $i]:
% 1.65/1.88         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 1.65/1.88      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.65/1.88  thf('68', plain,
% 1.65/1.88      (![X15 : $i, X16 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X15 @ X16)
% 1.65/1.88           = (k5_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))),
% 1.65/1.88      inference('demod', [status(thm)], ['66', '67'])).
% 1.65/1.88  thf('69', plain,
% 1.65/1.88      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.65/1.88          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('sup+', [status(thm)], ['65', '68'])).
% 1.65/1.88  thf('70', plain,
% 1.65/1.88      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 1.65/1.88      inference('cnf', [status(esa)], [t4_boole])).
% 1.65/1.88  thf(t98_xboole_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.65/1.88  thf('71', plain,
% 1.65/1.88      (![X23 : $i, X24 : $i]:
% 1.65/1.88         ((k2_xboole_0 @ X23 @ X24)
% 1.65/1.88           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 1.65/1.88      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.65/1.88  thf('72', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['70', '71'])).
% 1.65/1.88  thf(t1_boole, axiom,
% 1.65/1.88    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.65/1.88  thf('73', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.65/1.88      inference('cnf', [status(esa)], [t1_boole])).
% 1.65/1.88  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['72', '73'])).
% 1.65/1.88  thf('75', plain,
% 1.65/1.88      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('demod', [status(thm)], ['69', '74'])).
% 1.65/1.88  thf('76', plain,
% 1.65/1.88      (((k1_tops_1 @ sk_A @ sk_B)
% 1.65/1.88         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.88      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.65/1.88  thf('77', plain,
% 1.65/1.88      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('sup+', [status(thm)], ['75', '76'])).
% 1.65/1.88  thf('78', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(fc9_tops_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.65/1.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.65/1.88       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.65/1.88  thf('79', plain,
% 1.65/1.88      (![X43 : $i, X44 : $i]:
% 1.65/1.88         (~ (l1_pre_topc @ X43)
% 1.65/1.88          | ~ (v2_pre_topc @ X43)
% 1.65/1.88          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.65/1.88          | (v3_pre_topc @ (k1_tops_1 @ X43 @ X44) @ X43))),
% 1.65/1.88      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.65/1.88  thf('80', plain,
% 1.65/1.88      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.65/1.88        | ~ (v2_pre_topc @ sk_A)
% 1.65/1.88        | ~ (l1_pre_topc @ sk_A))),
% 1.65/1.88      inference('sup-', [status(thm)], ['78', '79'])).
% 1.65/1.88  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('83', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.65/1.88      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.65/1.88  thf('84', plain,
% 1.65/1.88      (((v3_pre_topc @ sk_B @ sk_A))
% 1.65/1.88         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.65/1.88      inference('sup+', [status(thm)], ['77', '83'])).
% 1.65/1.88  thf('85', plain,
% 1.65/1.88      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.65/1.88      inference('split', [status(esa)], ['0'])).
% 1.65/1.88  thf('86', plain,
% 1.65/1.88      (~
% 1.65/1.88       (((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.65/1.88       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.65/1.88      inference('sup-', [status(thm)], ['84', '85'])).
% 1.65/1.88  thf('87', plain, ($false),
% 1.65/1.88      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '86'])).
% 1.65/1.88  
% 1.65/1.88  % SZS output end Refutation
% 1.65/1.88  
% 1.65/1.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
