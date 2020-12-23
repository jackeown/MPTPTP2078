%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZIM6nfqMQ2

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:44 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 245 expanded)
%              Number of leaves         :   43 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          : 1372 (2736 expanded)
%              Number of equality atoms :  105 ( 192 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
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
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( ( k1_tops_1 @ X55 @ X54 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 @ ( k2_tops_1 @ X55 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('15',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X53 @ X52 ) @ X52 )
      | ~ ( v4_pre_topc @ X52 @ X53 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k2_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_pre_topc @ X51 @ X50 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 @ ( k2_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('50',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('51',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('62',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('73',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('75',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('77',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('85',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['83','85'])).

thf('87',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','86'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('89',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('91',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('96',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['89','94','97'])).

thf('99',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v2_pre_topc @ X45 )
      | ( ( k2_pre_topc @ X45 @ X44 )
       != X44 )
      | ( v4_pre_topc @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','34','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZIM6nfqMQ2
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.44/3.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.44/3.65  % Solved by: fo/fo7.sh
% 3.44/3.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.44/3.65  % done 5265 iterations in 3.192s
% 3.44/3.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.44/3.65  % SZS output start Refutation
% 3.44/3.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.44/3.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.44/3.65  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.44/3.65  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.44/3.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.44/3.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.44/3.65  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.44/3.65  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.44/3.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.44/3.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.44/3.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.44/3.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.44/3.65  thf(sk_B_type, type, sk_B: $i).
% 3.44/3.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.44/3.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.44/3.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.44/3.65  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.44/3.65  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.44/3.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.44/3.65  thf(sk_A_type, type, sk_A: $i).
% 3.44/3.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.44/3.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.44/3.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.44/3.65  thf(t77_tops_1, conjecture,
% 3.44/3.65    (![A:$i]:
% 3.44/3.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.44/3.65       ( ![B:$i]:
% 3.44/3.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.65           ( ( v4_pre_topc @ B @ A ) <=>
% 3.44/3.65             ( ( k2_tops_1 @ A @ B ) =
% 3.44/3.65               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 3.44/3.65  thf(zf_stmt_0, negated_conjecture,
% 3.44/3.65    (~( ![A:$i]:
% 3.44/3.65        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.44/3.65          ( ![B:$i]:
% 3.44/3.65            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.65              ( ( v4_pre_topc @ B @ A ) <=>
% 3.44/3.65                ( ( k2_tops_1 @ A @ B ) =
% 3.44/3.65                  ( k7_subset_1 @
% 3.44/3.65                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 3.44/3.65    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 3.44/3.65  thf('0', plain,
% 3.44/3.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65              (k1_tops_1 @ sk_A @ sk_B)))
% 3.44/3.65        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('1', plain,
% 3.44/3.65      (~
% 3.44/3.65       (((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.44/3.65       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 3.44/3.65      inference('split', [status(esa)], ['0'])).
% 3.44/3.65  thf('2', plain,
% 3.44/3.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf(t74_tops_1, axiom,
% 3.44/3.65    (![A:$i]:
% 3.44/3.65     ( ( l1_pre_topc @ A ) =>
% 3.44/3.65       ( ![B:$i]:
% 3.44/3.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.65           ( ( k1_tops_1 @ A @ B ) =
% 3.44/3.65             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.44/3.65  thf('3', plain,
% 3.44/3.65      (![X54 : $i, X55 : $i]:
% 3.44/3.65         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 3.44/3.65          | ((k1_tops_1 @ X55 @ X54)
% 3.44/3.65              = (k7_subset_1 @ (u1_struct_0 @ X55) @ X54 @ 
% 3.44/3.65                 (k2_tops_1 @ X55 @ X54)))
% 3.44/3.65          | ~ (l1_pre_topc @ X55))),
% 3.44/3.65      inference('cnf', [status(esa)], [t74_tops_1])).
% 3.44/3.65  thf('4', plain,
% 3.44/3.65      ((~ (l1_pre_topc @ sk_A)
% 3.44/3.65        | ((k1_tops_1 @ sk_A @ sk_B)
% 3.44/3.65            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.44/3.65      inference('sup-', [status(thm)], ['2', '3'])).
% 3.44/3.65  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('6', plain,
% 3.44/3.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf(redefinition_k7_subset_1, axiom,
% 3.44/3.65    (![A:$i,B:$i,C:$i]:
% 3.44/3.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.44/3.65       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.44/3.65  thf('7', plain,
% 3.44/3.65      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.44/3.65         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 3.44/3.65          | ((k7_subset_1 @ X33 @ X32 @ X34) = (k4_xboole_0 @ X32 @ X34)))),
% 3.44/3.65      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.44/3.65  thf('8', plain,
% 3.44/3.65      (![X0 : $i]:
% 3.44/3.65         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.44/3.65           = (k4_xboole_0 @ sk_B @ X0))),
% 3.44/3.65      inference('sup-', [status(thm)], ['6', '7'])).
% 3.44/3.65  thf('9', plain,
% 3.44/3.65      (((k1_tops_1 @ sk_A @ sk_B)
% 3.44/3.65         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.44/3.65      inference('demod', [status(thm)], ['4', '5', '8'])).
% 3.44/3.65  thf(t48_xboole_1, axiom,
% 3.44/3.65    (![A:$i,B:$i]:
% 3.44/3.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.44/3.65  thf('10', plain,
% 3.44/3.65      (![X17 : $i, X18 : $i]:
% 3.44/3.65         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 3.44/3.65           = (k3_xboole_0 @ X17 @ X18))),
% 3.44/3.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.44/3.65  thf('11', plain,
% 3.44/3.65      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 3.44/3.65         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.44/3.65      inference('sup+', [status(thm)], ['9', '10'])).
% 3.44/3.65  thf('12', plain,
% 3.44/3.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65             (k1_tops_1 @ sk_A @ sk_B)))
% 3.44/3.65        | (v4_pre_topc @ sk_B @ sk_A))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('13', plain,
% 3.44/3.65      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.44/3.65      inference('split', [status(esa)], ['12'])).
% 3.44/3.65  thf('14', plain,
% 3.44/3.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf(t69_tops_1, axiom,
% 3.44/3.65    (![A:$i]:
% 3.44/3.65     ( ( l1_pre_topc @ A ) =>
% 3.44/3.65       ( ![B:$i]:
% 3.44/3.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.65           ( ( v4_pre_topc @ B @ A ) =>
% 3.44/3.65             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 3.44/3.65  thf('15', plain,
% 3.44/3.65      (![X52 : $i, X53 : $i]:
% 3.44/3.65         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 3.44/3.65          | (r1_tarski @ (k2_tops_1 @ X53 @ X52) @ X52)
% 3.44/3.65          | ~ (v4_pre_topc @ X52 @ X53)
% 3.44/3.65          | ~ (l1_pre_topc @ X53))),
% 3.44/3.65      inference('cnf', [status(esa)], [t69_tops_1])).
% 3.44/3.65  thf('16', plain,
% 3.44/3.65      ((~ (l1_pre_topc @ sk_A)
% 3.44/3.65        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 3.44/3.65        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 3.44/3.65      inference('sup-', [status(thm)], ['14', '15'])).
% 3.44/3.65  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('18', plain,
% 3.44/3.65      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 3.44/3.65        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 3.44/3.65      inference('demod', [status(thm)], ['16', '17'])).
% 3.44/3.65  thf('19', plain,
% 3.44/3.65      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 3.44/3.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['13', '18'])).
% 3.44/3.65  thf(t28_xboole_1, axiom,
% 3.44/3.65    (![A:$i,B:$i]:
% 3.44/3.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.44/3.65  thf('20', plain,
% 3.44/3.65      (![X10 : $i, X11 : $i]:
% 3.44/3.65         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 3.44/3.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.44/3.65  thf('21', plain,
% 3.44/3.65      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 3.44/3.65          = (k2_tops_1 @ sk_A @ sk_B)))
% 3.44/3.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['19', '20'])).
% 3.44/3.65  thf(commutativity_k2_tarski, axiom,
% 3.44/3.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.44/3.65  thf('22', plain,
% 3.44/3.65      (![X19 : $i, X20 : $i]:
% 3.44/3.65         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 3.44/3.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.44/3.65  thf(t12_setfam_1, axiom,
% 3.44/3.65    (![A:$i,B:$i]:
% 3.44/3.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.44/3.65  thf('23', plain,
% 3.44/3.65      (![X36 : $i, X37 : $i]:
% 3.44/3.65         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 3.44/3.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.44/3.65  thf('24', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]:
% 3.44/3.65         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('sup+', [status(thm)], ['22', '23'])).
% 3.44/3.65  thf('25', plain,
% 3.44/3.65      (![X36 : $i, X37 : $i]:
% 3.44/3.65         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 3.44/3.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.44/3.65  thf('26', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('sup+', [status(thm)], ['24', '25'])).
% 3.44/3.65  thf('27', plain,
% 3.44/3.65      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.44/3.65          = (k2_tops_1 @ sk_A @ sk_B)))
% 3.44/3.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.44/3.65      inference('demod', [status(thm)], ['21', '26'])).
% 3.44/3.65  thf('28', plain,
% 3.44/3.65      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 3.44/3.65          = (k2_tops_1 @ sk_A @ sk_B)))
% 3.44/3.65         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.44/3.65      inference('sup+', [status(thm)], ['11', '27'])).
% 3.44/3.65  thf('29', plain,
% 3.44/3.65      (![X0 : $i]:
% 3.44/3.65         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.44/3.65           = (k4_xboole_0 @ sk_B @ X0))),
% 3.44/3.65      inference('sup-', [status(thm)], ['6', '7'])).
% 3.44/3.65  thf('30', plain,
% 3.44/3.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65              (k1_tops_1 @ sk_A @ sk_B))))
% 3.44/3.65         <= (~
% 3.44/3.65             (((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('split', [status(esa)], ['0'])).
% 3.44/3.65  thf('31', plain,
% 3.44/3.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.44/3.65         <= (~
% 3.44/3.65             (((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('sup-', [status(thm)], ['29', '30'])).
% 3.44/3.65  thf('32', plain,
% 3.44/3.65      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 3.44/3.65         <= (~
% 3.44/3.65             (((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 3.44/3.65             ((v4_pre_topc @ sk_B @ sk_A)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['28', '31'])).
% 3.44/3.65  thf('33', plain,
% 3.44/3.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.44/3.65       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 3.44/3.65      inference('simplify', [status(thm)], ['32'])).
% 3.44/3.65  thf('34', plain,
% 3.44/3.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.44/3.65       ((v4_pre_topc @ sk_B @ sk_A))),
% 3.44/3.65      inference('split', [status(esa)], ['12'])).
% 3.44/3.65  thf('35', plain,
% 3.44/3.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf(dt_k2_tops_1, axiom,
% 3.44/3.65    (![A:$i,B:$i]:
% 3.44/3.65     ( ( ( l1_pre_topc @ A ) & 
% 3.44/3.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.44/3.65       ( m1_subset_1 @
% 3.44/3.65         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.44/3.65  thf('36', plain,
% 3.44/3.65      (![X46 : $i, X47 : $i]:
% 3.44/3.65         (~ (l1_pre_topc @ X46)
% 3.44/3.65          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 3.44/3.65          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 3.44/3.65             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 3.44/3.65      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.44/3.65  thf('37', plain,
% 3.44/3.65      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.44/3.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.44/3.65        | ~ (l1_pre_topc @ sk_A))),
% 3.44/3.65      inference('sup-', [status(thm)], ['35', '36'])).
% 3.44/3.65  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('39', plain,
% 3.44/3.65      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.44/3.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.65      inference('demod', [status(thm)], ['37', '38'])).
% 3.44/3.65  thf('40', plain,
% 3.44/3.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf(redefinition_k4_subset_1, axiom,
% 3.44/3.65    (![A:$i,B:$i,C:$i]:
% 3.44/3.65     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.44/3.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.44/3.65       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.44/3.65  thf('41', plain,
% 3.44/3.65      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.44/3.65         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 3.44/3.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 3.44/3.65          | ((k4_subset_1 @ X30 @ X29 @ X31) = (k2_xboole_0 @ X29 @ X31)))),
% 3.44/3.65      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.44/3.65  thf('42', plain,
% 3.44/3.65      (![X0 : $i]:
% 3.44/3.65         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.44/3.65            = (k2_xboole_0 @ sk_B @ X0))
% 3.44/3.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.44/3.65      inference('sup-', [status(thm)], ['40', '41'])).
% 3.44/3.65  thf('43', plain,
% 3.44/3.65      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.44/3.65         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['39', '42'])).
% 3.44/3.65  thf('44', plain,
% 3.44/3.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf(t65_tops_1, axiom,
% 3.44/3.65    (![A:$i]:
% 3.44/3.65     ( ( l1_pre_topc @ A ) =>
% 3.44/3.65       ( ![B:$i]:
% 3.44/3.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.65           ( ( k2_pre_topc @ A @ B ) =
% 3.44/3.65             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.44/3.65  thf('45', plain,
% 3.44/3.65      (![X50 : $i, X51 : $i]:
% 3.44/3.65         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 3.44/3.65          | ((k2_pre_topc @ X51 @ X50)
% 3.44/3.65              = (k4_subset_1 @ (u1_struct_0 @ X51) @ X50 @ 
% 3.44/3.65                 (k2_tops_1 @ X51 @ X50)))
% 3.44/3.65          | ~ (l1_pre_topc @ X51))),
% 3.44/3.65      inference('cnf', [status(esa)], [t65_tops_1])).
% 3.44/3.65  thf('46', plain,
% 3.44/3.65      ((~ (l1_pre_topc @ sk_A)
% 3.44/3.65        | ((k2_pre_topc @ sk_A @ sk_B)
% 3.44/3.65            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.44/3.65      inference('sup-', [status(thm)], ['44', '45'])).
% 3.44/3.65  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('48', plain,
% 3.44/3.65      (((k2_pre_topc @ sk_A @ sk_B)
% 3.44/3.65         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65            (k2_tops_1 @ sk_A @ sk_B)))),
% 3.44/3.65      inference('demod', [status(thm)], ['46', '47'])).
% 3.44/3.65  thf('49', plain,
% 3.44/3.65      (((k2_pre_topc @ sk_A @ sk_B)
% 3.44/3.65         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.44/3.65      inference('sup+', [status(thm)], ['43', '48'])).
% 3.44/3.65  thf(d5_xboole_0, axiom,
% 3.44/3.65    (![A:$i,B:$i,C:$i]:
% 3.44/3.65     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.44/3.65       ( ![D:$i]:
% 3.44/3.65         ( ( r2_hidden @ D @ C ) <=>
% 3.44/3.65           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.44/3.65  thf('50', plain,
% 3.44/3.65      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.44/3.65         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 3.44/3.65          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 3.44/3.65          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.44/3.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.44/3.65  thf(t3_boole, axiom,
% 3.44/3.65    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.44/3.65  thf('51', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 3.44/3.65      inference('cnf', [status(esa)], [t3_boole])).
% 3.44/3.65  thf('52', plain,
% 3.44/3.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.44/3.65         (~ (r2_hidden @ X4 @ X3)
% 3.44/3.65          | ~ (r2_hidden @ X4 @ X2)
% 3.44/3.65          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 3.44/3.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.44/3.65  thf('53', plain,
% 3.44/3.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.44/3.65         (~ (r2_hidden @ X4 @ X2)
% 3.44/3.65          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.44/3.65      inference('simplify', [status(thm)], ['52'])).
% 3.44/3.65  thf('54', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]:
% 3.44/3.65         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.44/3.65      inference('sup-', [status(thm)], ['51', '53'])).
% 3.44/3.65  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.44/3.65      inference('condensation', [status(thm)], ['54'])).
% 3.44/3.65  thf('56', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]:
% 3.44/3.65         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 3.44/3.65          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['50', '55'])).
% 3.44/3.65  thf(t36_xboole_1, axiom,
% 3.44/3.65    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.44/3.65  thf('57', plain,
% 3.44/3.65      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 3.44/3.65      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.44/3.65  thf('58', plain,
% 3.44/3.65      (![X10 : $i, X11 : $i]:
% 3.44/3.65         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 3.44/3.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.44/3.65  thf('59', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]:
% 3.44/3.65         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 3.44/3.65           = (k4_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('sup-', [status(thm)], ['57', '58'])).
% 3.44/3.65  thf('60', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('sup+', [status(thm)], ['24', '25'])).
% 3.44/3.65  thf('61', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]:
% 3.44/3.65         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.44/3.65           = (k4_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('demod', [status(thm)], ['59', '60'])).
% 3.44/3.65  thf(t4_subset_1, axiom,
% 3.44/3.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.44/3.65  thf('62', plain,
% 3.44/3.65      (![X35 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 3.44/3.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.44/3.65  thf(t3_subset, axiom,
% 3.44/3.65    (![A:$i,B:$i]:
% 3.44/3.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.44/3.65  thf('63', plain,
% 3.44/3.65      (![X38 : $i, X39 : $i]:
% 3.44/3.65         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 3.44/3.65      inference('cnf', [status(esa)], [t3_subset])).
% 3.44/3.65  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.44/3.65      inference('sup-', [status(thm)], ['62', '63'])).
% 3.44/3.65  thf('65', plain,
% 3.44/3.65      (![X10 : $i, X11 : $i]:
% 3.44/3.65         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 3.44/3.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.44/3.65  thf('66', plain,
% 3.44/3.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.44/3.65      inference('sup-', [status(thm)], ['64', '65'])).
% 3.44/3.65  thf('67', plain,
% 3.44/3.65      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.44/3.65      inference('sup+', [status(thm)], ['61', '66'])).
% 3.44/3.65  thf('68', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]:
% 3.44/3.65         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 3.44/3.65          | ((X1) = (k1_xboole_0)))),
% 3.44/3.65      inference('demod', [status(thm)], ['56', '67'])).
% 3.44/3.65  thf('69', plain,
% 3.44/3.65      (![X0 : $i]:
% 3.44/3.65         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.44/3.65           = (k4_xboole_0 @ sk_B @ X0))),
% 3.44/3.65      inference('sup-', [status(thm)], ['6', '7'])).
% 3.44/3.65  thf('70', plain,
% 3.44/3.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65             (k1_tops_1 @ sk_A @ sk_B))))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('split', [status(esa)], ['12'])).
% 3.44/3.65  thf('71', plain,
% 3.44/3.65      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('sup+', [status(thm)], ['69', '70'])).
% 3.44/3.65  thf('72', plain,
% 3.44/3.65      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 3.44/3.65      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.44/3.65  thf('73', plain,
% 3.44/3.65      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('sup+', [status(thm)], ['71', '72'])).
% 3.44/3.65  thf('74', plain,
% 3.44/3.65      (![X10 : $i, X11 : $i]:
% 3.44/3.65         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 3.44/3.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.44/3.65  thf('75', plain,
% 3.44/3.65      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 3.44/3.65          = (k2_tops_1 @ sk_A @ sk_B)))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('sup-', [status(thm)], ['73', '74'])).
% 3.44/3.65  thf('76', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('sup+', [status(thm)], ['24', '25'])).
% 3.44/3.65  thf('77', plain,
% 3.44/3.65      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.44/3.65          = (k2_tops_1 @ sk_A @ sk_B)))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('demod', [status(thm)], ['75', '76'])).
% 3.44/3.65  thf('78', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('sup+', [status(thm)], ['24', '25'])).
% 3.44/3.65  thf('79', plain,
% 3.44/3.65      (![X17 : $i, X18 : $i]:
% 3.44/3.65         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 3.44/3.65           = (k3_xboole_0 @ X17 @ X18))),
% 3.44/3.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.44/3.65  thf('80', plain,
% 3.44/3.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.44/3.65         (~ (r2_hidden @ X4 @ X2)
% 3.44/3.65          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.44/3.65      inference('simplify', [status(thm)], ['52'])).
% 3.44/3.65  thf('81', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.44/3.65          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['79', '80'])).
% 3.44/3.65  thf('82', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.44/3.65          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['78', '81'])).
% 3.44/3.65  thf('83', plain,
% 3.44/3.65      ((![X0 : $i]:
% 3.44/3.65          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 3.44/3.65           | ~ (r2_hidden @ X0 @ 
% 3.44/3.65                (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('sup-', [status(thm)], ['77', '82'])).
% 3.44/3.65  thf('84', plain,
% 3.44/3.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.44/3.65         (~ (r2_hidden @ X4 @ X3)
% 3.44/3.65          | (r2_hidden @ X4 @ X1)
% 3.44/3.65          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 3.44/3.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.44/3.65  thf('85', plain,
% 3.44/3.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.44/3.65         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.44/3.65      inference('simplify', [status(thm)], ['84'])).
% 3.44/3.65  thf('86', plain,
% 3.44/3.65      ((![X0 : $i]:
% 3.44/3.65          ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('clc', [status(thm)], ['83', '85'])).
% 3.44/3.65  thf('87', plain,
% 3.44/3.65      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('sup-', [status(thm)], ['68', '86'])).
% 3.44/3.65  thf(t39_xboole_1, axiom,
% 3.44/3.65    (![A:$i,B:$i]:
% 3.44/3.65     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.44/3.65  thf('88', plain,
% 3.44/3.65      (![X14 : $i, X15 : $i]:
% 3.44/3.65         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 3.44/3.65           = (k2_xboole_0 @ X14 @ X15))),
% 3.44/3.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.44/3.65  thf('89', plain,
% 3.44/3.65      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 3.44/3.65          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('sup+', [status(thm)], ['87', '88'])).
% 3.44/3.65  thf('90', plain,
% 3.44/3.65      (![X19 : $i, X20 : $i]:
% 3.44/3.65         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 3.44/3.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.44/3.65  thf(l51_zfmisc_1, axiom,
% 3.44/3.65    (![A:$i,B:$i]:
% 3.44/3.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.44/3.65  thf('91', plain,
% 3.44/3.65      (![X21 : $i, X22 : $i]:
% 3.44/3.65         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 3.44/3.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.44/3.65  thf('92', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]:
% 3.44/3.65         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('sup+', [status(thm)], ['90', '91'])).
% 3.44/3.65  thf('93', plain,
% 3.44/3.65      (![X21 : $i, X22 : $i]:
% 3.44/3.65         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 3.44/3.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.44/3.65  thf('94', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('sup+', [status(thm)], ['92', '93'])).
% 3.44/3.65  thf('95', plain,
% 3.44/3.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.44/3.65      inference('sup+', [status(thm)], ['92', '93'])).
% 3.44/3.65  thf(t1_boole, axiom,
% 3.44/3.65    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.44/3.65  thf('96', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 3.44/3.65      inference('cnf', [status(esa)], [t1_boole])).
% 3.44/3.65  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.44/3.65      inference('sup+', [status(thm)], ['95', '96'])).
% 3.44/3.65  thf('98', plain,
% 3.44/3.65      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('demod', [status(thm)], ['89', '94', '97'])).
% 3.44/3.65  thf('99', plain,
% 3.44/3.65      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('sup+', [status(thm)], ['49', '98'])).
% 3.44/3.65  thf('100', plain,
% 3.44/3.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf(t52_pre_topc, axiom,
% 3.44/3.65    (![A:$i]:
% 3.44/3.65     ( ( l1_pre_topc @ A ) =>
% 3.44/3.65       ( ![B:$i]:
% 3.44/3.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.65           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 3.44/3.65             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 3.44/3.65               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 3.44/3.65  thf('101', plain,
% 3.44/3.65      (![X44 : $i, X45 : $i]:
% 3.44/3.65         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 3.44/3.65          | ~ (v2_pre_topc @ X45)
% 3.44/3.65          | ((k2_pre_topc @ X45 @ X44) != (X44))
% 3.44/3.65          | (v4_pre_topc @ X44 @ X45)
% 3.44/3.65          | ~ (l1_pre_topc @ X45))),
% 3.44/3.65      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.44/3.65  thf('102', plain,
% 3.44/3.65      ((~ (l1_pre_topc @ sk_A)
% 3.44/3.65        | (v4_pre_topc @ sk_B @ sk_A)
% 3.44/3.65        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 3.44/3.65        | ~ (v2_pre_topc @ sk_A))),
% 3.44/3.65      inference('sup-', [status(thm)], ['100', '101'])).
% 3.44/3.65  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('105', plain,
% 3.44/3.65      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 3.44/3.65      inference('demod', [status(thm)], ['102', '103', '104'])).
% 3.44/3.65  thf('106', plain,
% 3.44/3.65      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('sup-', [status(thm)], ['99', '105'])).
% 3.44/3.65  thf('107', plain,
% 3.44/3.65      (((v4_pre_topc @ sk_B @ sk_A))
% 3.44/3.65         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.44/3.65      inference('simplify', [status(thm)], ['106'])).
% 3.44/3.65  thf('108', plain,
% 3.44/3.65      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 3.44/3.65      inference('split', [status(esa)], ['0'])).
% 3.44/3.65  thf('109', plain,
% 3.44/3.65      (~
% 3.44/3.65       (((k2_tops_1 @ sk_A @ sk_B)
% 3.44/3.65          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.44/3.65             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.44/3.65       ((v4_pre_topc @ sk_B @ sk_A))),
% 3.44/3.65      inference('sup-', [status(thm)], ['107', '108'])).
% 3.44/3.65  thf('110', plain, ($false),
% 3.44/3.65      inference('sat_resolution*', [status(thm)], ['1', '33', '34', '109'])).
% 3.44/3.65  
% 3.44/3.65  % SZS output end Refutation
% 3.44/3.65  
% 3.44/3.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
