%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LdsGjeIM4j

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:24 EST 2020

% Result     : Theorem 8.23s
% Output     : Refutation 8.23s
% Verified   : 
% Statistics : Number of formulae       :  269 (1448 expanded)
%              Number of leaves         :   50 ( 494 expanded)
%              Depth                    :   35
%              Number of atoms          : 2326 (12138 expanded)
%              Number of equality atoms :  168 (1192 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v3_pre_topc @ X51 @ X52 )
      | ~ ( r1_tarski @ X51 @ X53 )
      | ( r1_tarski @ X51 @ ( k1_tops_1 @ X52 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k1_tops_1 @ X59 @ X58 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 @ ( k2_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k4_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k6_subset_1 @ X37 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k2_tops_1 @ X50 @ X49 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X50 ) @ ( k2_pre_topc @ X50 @ X49 ) @ ( k1_tops_1 @ X50 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k6_subset_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k6_subset_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k6_subset_1 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k6_subset_1 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('54',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( l1_pre_topc @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X45 @ X46 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X29 @ X28 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('63',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( ( k2_pre_topc @ X57 @ X56 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X57 ) @ X56 @ ( k2_tops_1 @ X57 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k6_subset_1 @ X37 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('73',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('74',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('76',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k6_subset_1 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
      | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','80'])).

thf('82',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('85',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('86',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('87',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('88',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('94',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('95',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','97'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('99',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X34 @ ( k3_subset_1 @ X34 @ X33 ) )
        = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','97'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('102',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('103',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('104',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X31: $i,X32: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('107',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['100','105','108'])).

thf('110',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('112',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('125',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('128',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X34 @ ( k3_subset_1 @ X34 @ X33 ) )
        = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('132',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('136',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('137',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','141'])).

thf('143',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('148',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['146','151'])).

thf('153',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['133','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','158'])).

thf('160',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('161',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('162',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['159','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['159','164'])).

thf('169',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['170','171'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('173',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('174',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('175',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['172','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['167','176'])).

thf('178',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ X2 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('180',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['178','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['111','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['110','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','193'])).

thf('195',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['84','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['172','175'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['159','164'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['172','175'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('201',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['195','196','199','200'])).

thf('202',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('203',plain,
    ( ( ( k2_xboole_0 @ ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('207',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['203','204','205','206'])).

thf('208',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('209',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X47 @ X48 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('210',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['207','213'])).

thf('215',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('216',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','216'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LdsGjeIM4j
% 0.13/0.36  % Computer   : n006.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:37:23 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 8.23/8.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.23/8.43  % Solved by: fo/fo7.sh
% 8.23/8.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.23/8.43  % done 8322 iterations in 7.949s
% 8.23/8.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.23/8.43  % SZS output start Refutation
% 8.23/8.43  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.23/8.43  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.23/8.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.23/8.43  thf(sk_B_type, type, sk_B: $i).
% 8.23/8.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.23/8.43  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 8.23/8.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.23/8.43  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.23/8.43  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 8.23/8.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.23/8.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.23/8.43  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 8.23/8.43  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.23/8.43  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.23/8.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.23/8.43  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 8.23/8.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.23/8.43  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 8.23/8.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.23/8.43  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 8.23/8.43  thf(sk_A_type, type, sk_A: $i).
% 8.23/8.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.23/8.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.23/8.43  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.23/8.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.23/8.43  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.23/8.43  thf(t76_tops_1, conjecture,
% 8.23/8.43    (![A:$i]:
% 8.23/8.43     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.23/8.43       ( ![B:$i]:
% 8.23/8.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.43           ( ( v3_pre_topc @ B @ A ) <=>
% 8.23/8.43             ( ( k2_tops_1 @ A @ B ) =
% 8.23/8.43               ( k7_subset_1 @
% 8.23/8.43                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 8.23/8.43  thf(zf_stmt_0, negated_conjecture,
% 8.23/8.43    (~( ![A:$i]:
% 8.23/8.43        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.23/8.43          ( ![B:$i]:
% 8.23/8.43            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.43              ( ( v3_pre_topc @ B @ A ) <=>
% 8.23/8.43                ( ( k2_tops_1 @ A @ B ) =
% 8.23/8.43                  ( k7_subset_1 @
% 8.23/8.43                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 8.23/8.43    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 8.23/8.43  thf('0', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 8.23/8.43        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf('1', plain,
% 8.23/8.43      (~
% 8.23/8.43       (((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 8.23/8.43       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 8.23/8.43      inference('split', [status(esa)], ['0'])).
% 8.23/8.43  thf('2', plain,
% 8.23/8.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf('3', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 8.23/8.43        | (v3_pre_topc @ sk_B @ sk_A))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf('4', plain,
% 8.23/8.43      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.23/8.43      inference('split', [status(esa)], ['3'])).
% 8.23/8.43  thf('5', plain,
% 8.23/8.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf(t56_tops_1, axiom,
% 8.23/8.43    (![A:$i]:
% 8.23/8.43     ( ( l1_pre_topc @ A ) =>
% 8.23/8.43       ( ![B:$i]:
% 8.23/8.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.43           ( ![C:$i]:
% 8.23/8.43             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.43               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 8.23/8.43                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.23/8.43  thf('6', plain,
% 8.23/8.43      (![X51 : $i, X52 : $i, X53 : $i]:
% 8.23/8.43         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 8.23/8.43          | ~ (v3_pre_topc @ X51 @ X52)
% 8.23/8.43          | ~ (r1_tarski @ X51 @ X53)
% 8.23/8.43          | (r1_tarski @ X51 @ (k1_tops_1 @ X52 @ X53))
% 8.23/8.43          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 8.23/8.43          | ~ (l1_pre_topc @ X52))),
% 8.23/8.43      inference('cnf', [status(esa)], [t56_tops_1])).
% 8.23/8.43  thf('7', plain,
% 8.23/8.43      (![X0 : $i]:
% 8.23/8.43         (~ (l1_pre_topc @ sk_A)
% 8.23/8.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.23/8.43          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 8.23/8.43          | ~ (r1_tarski @ sk_B @ X0)
% 8.23/8.43          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 8.23/8.43      inference('sup-', [status(thm)], ['5', '6'])).
% 8.23/8.43  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf('9', plain,
% 8.23/8.43      (![X0 : $i]:
% 8.23/8.43         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.23/8.43          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 8.23/8.43          | ~ (r1_tarski @ sk_B @ X0)
% 8.23/8.43          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 8.23/8.43      inference('demod', [status(thm)], ['7', '8'])).
% 8.23/8.43  thf('10', plain,
% 8.23/8.43      ((![X0 : $i]:
% 8.23/8.43          (~ (r1_tarski @ sk_B @ X0)
% 8.23/8.43           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 8.23/8.43           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 8.23/8.43         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['4', '9'])).
% 8.23/8.43  thf('11', plain,
% 8.23/8.43      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 8.23/8.43         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['2', '10'])).
% 8.23/8.43  thf(d10_xboole_0, axiom,
% 8.23/8.43    (![A:$i,B:$i]:
% 8.23/8.43     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.23/8.43  thf('12', plain,
% 8.23/8.43      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 8.23/8.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.23/8.43  thf('13', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 8.23/8.43      inference('simplify', [status(thm)], ['12'])).
% 8.23/8.43  thf('14', plain,
% 8.23/8.43      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 8.23/8.43         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.23/8.43      inference('demod', [status(thm)], ['11', '13'])).
% 8.23/8.43  thf('15', plain,
% 8.23/8.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf(t74_tops_1, axiom,
% 8.23/8.43    (![A:$i]:
% 8.23/8.43     ( ( l1_pre_topc @ A ) =>
% 8.23/8.43       ( ![B:$i]:
% 8.23/8.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.43           ( ( k1_tops_1 @ A @ B ) =
% 8.23/8.43             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.23/8.43  thf('16', plain,
% 8.23/8.43      (![X58 : $i, X59 : $i]:
% 8.23/8.43         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 8.23/8.43          | ((k1_tops_1 @ X59 @ X58)
% 8.23/8.43              = (k7_subset_1 @ (u1_struct_0 @ X59) @ X58 @ 
% 8.23/8.43                 (k2_tops_1 @ X59 @ X58)))
% 8.23/8.43          | ~ (l1_pre_topc @ X59))),
% 8.23/8.43      inference('cnf', [status(esa)], [t74_tops_1])).
% 8.23/8.43  thf('17', plain,
% 8.23/8.43      ((~ (l1_pre_topc @ sk_A)
% 8.23/8.43        | ((k1_tops_1 @ sk_A @ sk_B)
% 8.23/8.43            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.23/8.43               (k2_tops_1 @ sk_A @ sk_B))))),
% 8.23/8.43      inference('sup-', [status(thm)], ['15', '16'])).
% 8.23/8.43  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf('19', plain,
% 8.23/8.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf(redefinition_k7_subset_1, axiom,
% 8.23/8.43    (![A:$i,B:$i,C:$i]:
% 8.23/8.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.23/8.43       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.23/8.43  thf('20', plain,
% 8.23/8.43      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.23/8.43         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 8.23/8.43          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k4_xboole_0 @ X37 @ X39)))),
% 8.23/8.43      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.23/8.43  thf(redefinition_k6_subset_1, axiom,
% 8.23/8.43    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 8.23/8.43  thf('21', plain,
% 8.23/8.43      (![X35 : $i, X36 : $i]:
% 8.23/8.43         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 8.23/8.43      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.23/8.43  thf('22', plain,
% 8.23/8.43      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.23/8.43         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 8.23/8.43          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k6_subset_1 @ X37 @ X39)))),
% 8.23/8.43      inference('demod', [status(thm)], ['20', '21'])).
% 8.23/8.43  thf('23', plain,
% 8.23/8.43      (![X0 : $i]:
% 8.23/8.43         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.23/8.43           = (k6_subset_1 @ sk_B @ X0))),
% 8.23/8.43      inference('sup-', [status(thm)], ['19', '22'])).
% 8.23/8.43  thf('24', plain,
% 8.23/8.43      (((k1_tops_1 @ sk_A @ sk_B)
% 8.23/8.43         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.23/8.43      inference('demod', [status(thm)], ['17', '18', '23'])).
% 8.23/8.43  thf(dt_k6_subset_1, axiom,
% 8.23/8.43    (![A:$i,B:$i]:
% 8.23/8.43     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 8.23/8.43  thf('25', plain,
% 8.23/8.43      (![X31 : $i, X32 : $i]:
% 8.23/8.43         (m1_subset_1 @ (k6_subset_1 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))),
% 8.23/8.43      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 8.23/8.43  thf(t3_subset, axiom,
% 8.23/8.43    (![A:$i,B:$i]:
% 8.23/8.43     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.23/8.43  thf('26', plain,
% 8.23/8.43      (![X42 : $i, X43 : $i]:
% 8.23/8.43         ((r1_tarski @ X42 @ X43) | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 8.23/8.43      inference('cnf', [status(esa)], [t3_subset])).
% 8.23/8.43  thf('27', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 8.23/8.43      inference('sup-', [status(thm)], ['25', '26'])).
% 8.23/8.43  thf('28', plain,
% 8.23/8.43      (![X10 : $i, X12 : $i]:
% 8.23/8.43         (((X10) = (X12))
% 8.23/8.43          | ~ (r1_tarski @ X12 @ X10)
% 8.23/8.43          | ~ (r1_tarski @ X10 @ X12))),
% 8.23/8.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.23/8.43  thf('29', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]:
% 8.23/8.43         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 8.23/8.43          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['27', '28'])).
% 8.23/8.43  thf('30', plain,
% 8.23/8.43      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 8.23/8.43        | ((sk_B) = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 8.23/8.43      inference('sup-', [status(thm)], ['24', '29'])).
% 8.23/8.43  thf('31', plain,
% 8.23/8.43      (((k1_tops_1 @ sk_A @ sk_B)
% 8.23/8.43         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.23/8.43      inference('demod', [status(thm)], ['17', '18', '23'])).
% 8.23/8.43  thf('32', plain,
% 8.23/8.43      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 8.23/8.43        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 8.23/8.43      inference('demod', [status(thm)], ['30', '31'])).
% 8.23/8.43  thf('33', plain,
% 8.23/8.43      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 8.23/8.43         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['14', '32'])).
% 8.23/8.43  thf('34', plain,
% 8.23/8.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf(l78_tops_1, axiom,
% 8.23/8.43    (![A:$i]:
% 8.23/8.43     ( ( l1_pre_topc @ A ) =>
% 8.23/8.43       ( ![B:$i]:
% 8.23/8.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.43           ( ( k2_tops_1 @ A @ B ) =
% 8.23/8.43             ( k7_subset_1 @
% 8.23/8.43               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 8.23/8.43               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.23/8.43  thf('35', plain,
% 8.23/8.43      (![X49 : $i, X50 : $i]:
% 8.23/8.43         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 8.23/8.43          | ((k2_tops_1 @ X50 @ X49)
% 8.23/8.43              = (k7_subset_1 @ (u1_struct_0 @ X50) @ 
% 8.23/8.43                 (k2_pre_topc @ X50 @ X49) @ (k1_tops_1 @ X50 @ X49)))
% 8.23/8.43          | ~ (l1_pre_topc @ X50))),
% 8.23/8.43      inference('cnf', [status(esa)], [l78_tops_1])).
% 8.23/8.43  thf('36', plain,
% 8.23/8.43      ((~ (l1_pre_topc @ sk_A)
% 8.23/8.43        | ((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 8.23/8.43      inference('sup-', [status(thm)], ['34', '35'])).
% 8.23/8.43  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf('38', plain,
% 8.23/8.43      (((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 8.23/8.43            (k1_tops_1 @ sk_A @ sk_B)))),
% 8.23/8.43      inference('demod', [status(thm)], ['36', '37'])).
% 8.23/8.43  thf('39', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 8.23/8.43         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.23/8.43      inference('sup+', [status(thm)], ['33', '38'])).
% 8.23/8.43  thf('40', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 8.23/8.43         <= (~
% 8.23/8.43             (((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.43      inference('split', [status(esa)], ['0'])).
% 8.23/8.43  thf('41', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 8.23/8.43         <= (~
% 8.23/8.43             (((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 8.23/8.43             ((v3_pre_topc @ sk_B @ sk_A)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['39', '40'])).
% 8.23/8.43  thf('42', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 8.23/8.43       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 8.23/8.43      inference('simplify', [status(thm)], ['41'])).
% 8.23/8.43  thf('43', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 8.23/8.43       ((v3_pre_topc @ sk_B @ sk_A))),
% 8.23/8.43      inference('split', [status(esa)], ['3'])).
% 8.23/8.43  thf(d3_tarski, axiom,
% 8.23/8.43    (![A:$i,B:$i]:
% 8.23/8.43     ( ( r1_tarski @ A @ B ) <=>
% 8.23/8.43       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.23/8.43  thf('44', plain,
% 8.23/8.43      (![X1 : $i, X3 : $i]:
% 8.23/8.43         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.23/8.43      inference('cnf', [status(esa)], [d3_tarski])).
% 8.23/8.43  thf(d5_xboole_0, axiom,
% 8.23/8.43    (![A:$i,B:$i,C:$i]:
% 8.23/8.43     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 8.23/8.43       ( ![D:$i]:
% 8.23/8.43         ( ( r2_hidden @ D @ C ) <=>
% 8.23/8.43           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 8.23/8.43  thf('45', plain,
% 8.23/8.43      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 8.23/8.43         (~ (r2_hidden @ X4 @ X5)
% 8.23/8.43          | (r2_hidden @ X4 @ X6)
% 8.23/8.43          | (r2_hidden @ X4 @ X7)
% 8.23/8.43          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 8.23/8.43      inference('cnf', [status(esa)], [d5_xboole_0])).
% 8.23/8.43  thf('46', plain,
% 8.23/8.43      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.23/8.43         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 8.23/8.43          | (r2_hidden @ X4 @ X6)
% 8.23/8.43          | ~ (r2_hidden @ X4 @ X5))),
% 8.23/8.43      inference('simplify', [status(thm)], ['45'])).
% 8.23/8.43  thf('47', plain,
% 8.23/8.43      (![X35 : $i, X36 : $i]:
% 8.23/8.43         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 8.23/8.43      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.23/8.43  thf('48', plain,
% 8.23/8.43      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.23/8.43         ((r2_hidden @ X4 @ (k6_subset_1 @ X5 @ X6))
% 8.23/8.43          | (r2_hidden @ X4 @ X6)
% 8.23/8.43          | ~ (r2_hidden @ X4 @ X5))),
% 8.23/8.43      inference('demod', [status(thm)], ['46', '47'])).
% 8.23/8.43  thf('49', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.43         ((r1_tarski @ X0 @ X1)
% 8.23/8.43          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 8.23/8.43          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k6_subset_1 @ X0 @ X2)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['44', '48'])).
% 8.23/8.43  thf('50', plain,
% 8.23/8.43      (![X1 : $i, X3 : $i]:
% 8.23/8.43         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 8.23/8.43      inference('cnf', [status(esa)], [d3_tarski])).
% 8.23/8.43  thf('51', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]:
% 8.23/8.43         ((r2_hidden @ (sk_C @ (k6_subset_1 @ X1 @ X0) @ X1) @ X0)
% 8.23/8.43          | (r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))
% 8.23/8.43          | (r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['49', '50'])).
% 8.23/8.43  thf('52', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]:
% 8.23/8.43         ((r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))
% 8.23/8.43          | (r2_hidden @ (sk_C @ (k6_subset_1 @ X1 @ X0) @ X1) @ X0))),
% 8.23/8.43      inference('simplify', [status(thm)], ['51'])).
% 8.23/8.43  thf('53', plain,
% 8.23/8.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf(dt_k2_tops_1, axiom,
% 8.23/8.43    (![A:$i,B:$i]:
% 8.23/8.43     ( ( ( l1_pre_topc @ A ) & 
% 8.23/8.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.23/8.43       ( m1_subset_1 @
% 8.23/8.43         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.23/8.43  thf('54', plain,
% 8.23/8.43      (![X45 : $i, X46 : $i]:
% 8.23/8.43         (~ (l1_pre_topc @ X45)
% 8.23/8.43          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 8.23/8.43          | (m1_subset_1 @ (k2_tops_1 @ X45 @ X46) @ 
% 8.23/8.43             (k1_zfmisc_1 @ (u1_struct_0 @ X45))))),
% 8.23/8.43      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 8.23/8.43  thf('55', plain,
% 8.23/8.43      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.43         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.23/8.43        | ~ (l1_pre_topc @ sk_A))),
% 8.23/8.43      inference('sup-', [status(thm)], ['53', '54'])).
% 8.23/8.43  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf('57', plain,
% 8.23/8.43      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('demod', [status(thm)], ['55', '56'])).
% 8.23/8.43  thf('58', plain,
% 8.23/8.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf(dt_k4_subset_1, axiom,
% 8.23/8.43    (![A:$i,B:$i,C:$i]:
% 8.23/8.43     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 8.23/8.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.23/8.43       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.23/8.43  thf('59', plain,
% 8.23/8.43      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.23/8.43         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 8.23/8.43          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 8.23/8.43          | (m1_subset_1 @ (k4_subset_1 @ X29 @ X28 @ X30) @ 
% 8.23/8.43             (k1_zfmisc_1 @ X29)))),
% 8.23/8.43      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 8.23/8.43  thf('60', plain,
% 8.23/8.43      (![X0 : $i]:
% 8.23/8.43         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 8.23/8.43           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.23/8.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.23/8.43      inference('sup-', [status(thm)], ['58', '59'])).
% 8.23/8.43  thf('61', plain,
% 8.23/8.43      ((m1_subset_1 @ 
% 8.23/8.43        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 8.23/8.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['57', '60'])).
% 8.23/8.43  thf('62', plain,
% 8.23/8.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf(t65_tops_1, axiom,
% 8.23/8.43    (![A:$i]:
% 8.23/8.43     ( ( l1_pre_topc @ A ) =>
% 8.23/8.43       ( ![B:$i]:
% 8.23/8.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.43           ( ( k2_pre_topc @ A @ B ) =
% 8.23/8.43             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.23/8.43  thf('63', plain,
% 8.23/8.43      (![X56 : $i, X57 : $i]:
% 8.23/8.43         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 8.23/8.43          | ((k2_pre_topc @ X57 @ X56)
% 8.23/8.43              = (k4_subset_1 @ (u1_struct_0 @ X57) @ X56 @ 
% 8.23/8.43                 (k2_tops_1 @ X57 @ X56)))
% 8.23/8.43          | ~ (l1_pre_topc @ X57))),
% 8.23/8.43      inference('cnf', [status(esa)], [t65_tops_1])).
% 8.23/8.43  thf('64', plain,
% 8.23/8.43      ((~ (l1_pre_topc @ sk_A)
% 8.23/8.43        | ((k2_pre_topc @ sk_A @ sk_B)
% 8.23/8.43            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.23/8.43               (k2_tops_1 @ sk_A @ sk_B))))),
% 8.23/8.43      inference('sup-', [status(thm)], ['62', '63'])).
% 8.23/8.43  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.43  thf('66', plain,
% 8.23/8.43      (((k2_pre_topc @ sk_A @ sk_B)
% 8.23/8.43         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.23/8.43            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.23/8.43      inference('demod', [status(thm)], ['64', '65'])).
% 8.23/8.43  thf('67', plain,
% 8.23/8.43      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 8.23/8.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.43      inference('demod', [status(thm)], ['61', '66'])).
% 8.23/8.43  thf('68', plain,
% 8.23/8.43      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.23/8.43         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 8.23/8.43          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k6_subset_1 @ X37 @ X39)))),
% 8.23/8.43      inference('demod', [status(thm)], ['20', '21'])).
% 8.23/8.43  thf('69', plain,
% 8.23/8.43      (![X0 : $i]:
% 8.23/8.43         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 8.23/8.43           X0) = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 8.23/8.43      inference('sup-', [status(thm)], ['67', '68'])).
% 8.23/8.43  thf('70', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 8.23/8.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.43      inference('split', [status(esa)], ['3'])).
% 8.23/8.43  thf('71', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 8.23/8.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.43      inference('sup+', [status(thm)], ['69', '70'])).
% 8.23/8.43  thf('72', plain,
% 8.23/8.43      (![X1 : $i, X3 : $i]:
% 8.23/8.43         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.23/8.43      inference('cnf', [status(esa)], [d3_tarski])).
% 8.23/8.43  thf('73', plain,
% 8.23/8.43      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.23/8.43         (~ (r2_hidden @ X8 @ X7)
% 8.23/8.43          | ~ (r2_hidden @ X8 @ X6)
% 8.23/8.43          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 8.23/8.43      inference('cnf', [status(esa)], [d5_xboole_0])).
% 8.23/8.43  thf('74', plain,
% 8.23/8.43      (![X5 : $i, X6 : $i, X8 : $i]:
% 8.23/8.43         (~ (r2_hidden @ X8 @ X6)
% 8.23/8.43          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 8.23/8.43      inference('simplify', [status(thm)], ['73'])).
% 8.23/8.43  thf('75', plain,
% 8.23/8.43      (![X35 : $i, X36 : $i]:
% 8.23/8.43         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 8.23/8.43      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.23/8.43  thf('76', plain,
% 8.23/8.43      (![X5 : $i, X6 : $i, X8 : $i]:
% 8.23/8.43         (~ (r2_hidden @ X8 @ X6)
% 8.23/8.43          | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 8.23/8.43      inference('demod', [status(thm)], ['74', '75'])).
% 8.23/8.43  thf('77', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.43         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 8.23/8.43          | ~ (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X0))),
% 8.23/8.43      inference('sup-', [status(thm)], ['72', '76'])).
% 8.23/8.43  thf('78', plain,
% 8.23/8.43      ((![X0 : $i]:
% 8.23/8.43          (~ (r2_hidden @ (sk_C @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 8.23/8.43           | (r1_tarski @ (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) @ 
% 8.23/8.43              X0)))
% 8.23/8.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.43      inference('sup-', [status(thm)], ['71', '77'])).
% 8.23/8.43  thf('79', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 8.23/8.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.43      inference('sup+', [status(thm)], ['69', '70'])).
% 8.23/8.43  thf('80', plain,
% 8.23/8.43      ((![X0 : $i]:
% 8.23/8.43          (~ (r2_hidden @ (sk_C @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 8.23/8.43           | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)))
% 8.23/8.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.43      inference('demod', [status(thm)], ['78', '79'])).
% 8.23/8.43  thf('81', plain,
% 8.23/8.43      ((((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.43          (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 8.23/8.43         | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.43            (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))))
% 8.23/8.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.43      inference('sup-', [status(thm)], ['52', '80'])).
% 8.23/8.43  thf('82', plain,
% 8.23/8.43      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.43         (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 8.23/8.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.43      inference('simplify', [status(thm)], ['81'])).
% 8.23/8.43  thf('83', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]:
% 8.23/8.43         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 8.23/8.43          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['27', '28'])).
% 8.23/8.43  thf('84', plain,
% 8.23/8.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43          = (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 8.23/8.43         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.43                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.43      inference('sup-', [status(thm)], ['82', '83'])).
% 8.23/8.43  thf(t51_xboole_1, axiom,
% 8.23/8.43    (![A:$i,B:$i]:
% 8.23/8.43     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 8.23/8.43       ( A ) ))).
% 8.23/8.43  thf('85', plain,
% 8.23/8.43      (![X16 : $i, X17 : $i]:
% 8.23/8.43         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 8.23/8.43           = (X16))),
% 8.23/8.43      inference('cnf', [status(esa)], [t51_xboole_1])).
% 8.23/8.43  thf('86', plain,
% 8.23/8.43      (![X35 : $i, X36 : $i]:
% 8.23/8.43         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 8.23/8.43      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.23/8.43  thf(commutativity_k2_tarski, axiom,
% 8.23/8.43    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 8.23/8.43  thf('87', plain,
% 8.23/8.43      (![X20 : $i, X21 : $i]:
% 8.23/8.43         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 8.23/8.43      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.23/8.43  thf(l51_zfmisc_1, axiom,
% 8.23/8.43    (![A:$i,B:$i]:
% 8.23/8.43     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.23/8.43  thf('88', plain,
% 8.23/8.43      (![X22 : $i, X23 : $i]:
% 8.23/8.43         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 8.23/8.43      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.23/8.43  thf('89', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]:
% 8.23/8.43         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 8.23/8.43      inference('sup+', [status(thm)], ['87', '88'])).
% 8.23/8.43  thf('90', plain,
% 8.23/8.43      (![X22 : $i, X23 : $i]:
% 8.23/8.43         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 8.23/8.43      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.23/8.43  thf('91', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.23/8.43      inference('sup+', [status(thm)], ['89', '90'])).
% 8.23/8.43  thf('92', plain,
% 8.23/8.43      (![X16 : $i, X17 : $i]:
% 8.23/8.43         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 8.23/8.43           = (X16))),
% 8.23/8.43      inference('demod', [status(thm)], ['85', '86', '91'])).
% 8.23/8.43  thf('93', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.23/8.43      inference('sup+', [status(thm)], ['89', '90'])).
% 8.23/8.43  thf(t7_xboole_1, axiom,
% 8.23/8.43    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 8.23/8.43  thf('94', plain,
% 8.23/8.43      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 8.23/8.43      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.23/8.43  thf('95', plain,
% 8.23/8.43      (![X42 : $i, X44 : $i]:
% 8.23/8.43         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 8.23/8.43      inference('cnf', [status(esa)], [t3_subset])).
% 8.23/8.43  thf('96', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]:
% 8.23/8.43         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.23/8.43      inference('sup-', [status(thm)], ['94', '95'])).
% 8.23/8.43  thf('97', plain,
% 8.23/8.43      (![X0 : $i, X1 : $i]:
% 8.23/8.43         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.23/8.44      inference('sup+', [status(thm)], ['93', '96'])).
% 8.23/8.44  thf('98', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['92', '97'])).
% 8.23/8.44  thf(involutiveness_k3_subset_1, axiom,
% 8.23/8.44    (![A:$i,B:$i]:
% 8.23/8.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.23/8.44       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 8.23/8.44  thf('99', plain,
% 8.23/8.44      (![X33 : $i, X34 : $i]:
% 8.23/8.44         (((k3_subset_1 @ X34 @ (k3_subset_1 @ X34 @ X33)) = (X33))
% 8.23/8.44          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 8.23/8.44      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.23/8.44  thf('100', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 8.23/8.44           = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup-', [status(thm)], ['98', '99'])).
% 8.23/8.44  thf('101', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['92', '97'])).
% 8.23/8.44  thf(d5_subset_1, axiom,
% 8.23/8.44    (![A:$i,B:$i]:
% 8.23/8.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.23/8.44       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 8.23/8.44  thf('102', plain,
% 8.23/8.44      (![X24 : $i, X25 : $i]:
% 8.23/8.44         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 8.23/8.44          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 8.23/8.44      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.23/8.44  thf('103', plain,
% 8.23/8.44      (![X35 : $i, X36 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 8.23/8.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.23/8.44  thf('104', plain,
% 8.23/8.44      (![X24 : $i, X25 : $i]:
% 8.23/8.44         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 8.23/8.44          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 8.23/8.44      inference('demod', [status(thm)], ['102', '103'])).
% 8.23/8.44  thf('105', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 8.23/8.44           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.23/8.44      inference('sup-', [status(thm)], ['101', '104'])).
% 8.23/8.44  thf('106', plain,
% 8.23/8.44      (![X31 : $i, X32 : $i]:
% 8.23/8.44         (m1_subset_1 @ (k6_subset_1 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))),
% 8.23/8.44      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 8.23/8.44  thf('107', plain,
% 8.23/8.44      (![X24 : $i, X25 : $i]:
% 8.23/8.44         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 8.23/8.44          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 8.23/8.44      inference('demod', [status(thm)], ['102', '103'])).
% 8.23/8.44  thf('108', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 8.23/8.44           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 8.23/8.44      inference('sup-', [status(thm)], ['106', '107'])).
% 8.23/8.44  thf('109', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 8.23/8.44           = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('demod', [status(thm)], ['100', '105', '108'])).
% 8.23/8.44  thf('110', plain,
% 8.23/8.44      (![X16 : $i, X17 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 8.23/8.44           = (X16))),
% 8.23/8.44      inference('demod', [status(thm)], ['85', '86', '91'])).
% 8.23/8.44  thf('111', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['89', '90'])).
% 8.23/8.44  thf('112', plain,
% 8.23/8.44      (![X1 : $i, X3 : $i]:
% 8.23/8.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.23/8.44      inference('cnf', [status(esa)], [d3_tarski])).
% 8.23/8.44  thf('113', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 8.23/8.44      inference('sup-', [status(thm)], ['25', '26'])).
% 8.23/8.44  thf('114', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.44         (~ (r2_hidden @ X0 @ X1)
% 8.23/8.44          | (r2_hidden @ X0 @ X2)
% 8.23/8.44          | ~ (r1_tarski @ X1 @ X2))),
% 8.23/8.44      inference('cnf', [status(esa)], [d3_tarski])).
% 8.23/8.44  thf('115', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.44         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 8.23/8.44      inference('sup-', [status(thm)], ['113', '114'])).
% 8.23/8.44  thf('116', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.44         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 8.23/8.44          | (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 8.23/8.44      inference('sup-', [status(thm)], ['112', '115'])).
% 8.23/8.44  thf('117', plain,
% 8.23/8.44      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 8.23/8.44      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.23/8.44  thf('118', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.44         (~ (r2_hidden @ X0 @ X1)
% 8.23/8.44          | (r2_hidden @ X0 @ X2)
% 8.23/8.44          | ~ (r1_tarski @ X1 @ X2))),
% 8.23/8.44      inference('cnf', [status(esa)], [d3_tarski])).
% 8.23/8.44  thf('119', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.44         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 8.23/8.44      inference('sup-', [status(thm)], ['117', '118'])).
% 8.23/8.44  thf('120', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.23/8.44         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2)
% 8.23/8.44          | (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X0 @ X1)) @ 
% 8.23/8.44             (k2_xboole_0 @ X0 @ X3)))),
% 8.23/8.44      inference('sup-', [status(thm)], ['116', '119'])).
% 8.23/8.44  thf('121', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.44         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 8.23/8.44          | ~ (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X0))),
% 8.23/8.44      inference('sup-', [status(thm)], ['72', '76'])).
% 8.23/8.44  thf('122', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.44         ((r1_tarski @ (k6_subset_1 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 8.23/8.44          | (r1_tarski @ (k6_subset_1 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ X2))),
% 8.23/8.44      inference('sup-', [status(thm)], ['120', '121'])).
% 8.23/8.44  thf('123', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.44         (r1_tarski @ (k6_subset_1 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)),
% 8.23/8.44      inference('simplify', [status(thm)], ['122'])).
% 8.23/8.44  thf('124', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['89', '90'])).
% 8.23/8.44  thf(t1_boole, axiom,
% 8.23/8.44    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.23/8.44  thf('125', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 8.23/8.44      inference('cnf', [status(esa)], [t1_boole])).
% 8.23/8.44  thf('126', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['124', '125'])).
% 8.23/8.44  thf('127', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.23/8.44      inference('sup-', [status(thm)], ['94', '95'])).
% 8.23/8.44  thf('128', plain,
% 8.23/8.44      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['126', '127'])).
% 8.23/8.44  thf('129', plain,
% 8.23/8.44      (![X33 : $i, X34 : $i]:
% 8.23/8.44         (((k3_subset_1 @ X34 @ (k3_subset_1 @ X34 @ X33)) = (X33))
% 8.23/8.44          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 8.23/8.44      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.23/8.44  thf('130', plain,
% 8.23/8.44      (![X0 : $i]:
% 8.23/8.44         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 8.23/8.44      inference('sup-', [status(thm)], ['128', '129'])).
% 8.23/8.44  thf('131', plain,
% 8.23/8.44      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['126', '127'])).
% 8.23/8.44  thf('132', plain,
% 8.23/8.44      (![X24 : $i, X25 : $i]:
% 8.23/8.44         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 8.23/8.44          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 8.23/8.44      inference('demod', [status(thm)], ['102', '103'])).
% 8.23/8.44  thf('133', plain,
% 8.23/8.44      (![X0 : $i]:
% 8.23/8.44         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 8.23/8.44      inference('sup-', [status(thm)], ['131', '132'])).
% 8.23/8.44  thf('134', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 8.23/8.44      inference('sup-', [status(thm)], ['25', '26'])).
% 8.23/8.44  thf('135', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['124', '125'])).
% 8.23/8.44  thf('136', plain,
% 8.23/8.44      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 8.23/8.44      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.23/8.44  thf('137', plain,
% 8.23/8.44      (![X10 : $i, X12 : $i]:
% 8.23/8.44         (((X10) = (X12))
% 8.23/8.44          | ~ (r1_tarski @ X12 @ X10)
% 8.23/8.44          | ~ (r1_tarski @ X10 @ X12))),
% 8.23/8.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.23/8.44  thf('138', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 8.23/8.44          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 8.23/8.44      inference('sup-', [status(thm)], ['136', '137'])).
% 8.23/8.44  thf('139', plain,
% 8.23/8.44      (![X0 : $i]:
% 8.23/8.44         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 8.23/8.44          | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 8.23/8.44      inference('sup-', [status(thm)], ['135', '138'])).
% 8.23/8.44  thf('140', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['124', '125'])).
% 8.23/8.44  thf('141', plain,
% 8.23/8.44      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.23/8.44      inference('demod', [status(thm)], ['139', '140'])).
% 8.23/8.44  thf('142', plain,
% 8.23/8.44      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.23/8.44      inference('sup-', [status(thm)], ['134', '141'])).
% 8.23/8.44  thf('143', plain,
% 8.23/8.44      (![X16 : $i, X17 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 8.23/8.44           = (X16))),
% 8.23/8.44      inference('demod', [status(thm)], ['85', '86', '91'])).
% 8.23/8.44  thf('144', plain,
% 8.23/8.44      (![X0 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 8.23/8.44           = (k1_xboole_0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['142', '143'])).
% 8.23/8.44  thf('145', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['124', '125'])).
% 8.23/8.44  thf('146', plain,
% 8.23/8.44      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.23/8.44      inference('demod', [status(thm)], ['144', '145'])).
% 8.23/8.44  thf('147', plain,
% 8.23/8.44      (![X20 : $i, X21 : $i]:
% 8.23/8.44         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 8.23/8.44      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.23/8.44  thf(t12_setfam_1, axiom,
% 8.23/8.44    (![A:$i,B:$i]:
% 8.23/8.44     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.23/8.44  thf('148', plain,
% 8.23/8.44      (![X40 : $i, X41 : $i]:
% 8.23/8.44         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 8.23/8.44      inference('cnf', [status(esa)], [t12_setfam_1])).
% 8.23/8.44  thf('149', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['147', '148'])).
% 8.23/8.44  thf('150', plain,
% 8.23/8.44      (![X40 : $i, X41 : $i]:
% 8.23/8.44         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 8.23/8.44      inference('cnf', [status(esa)], [t12_setfam_1])).
% 8.23/8.44  thf('151', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['149', '150'])).
% 8.23/8.44  thf('152', plain,
% 8.23/8.44      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['146', '151'])).
% 8.23/8.44  thf('153', plain,
% 8.23/8.44      (![X16 : $i, X17 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 8.23/8.44           = (X16))),
% 8.23/8.44      inference('demod', [status(thm)], ['85', '86', '91'])).
% 8.23/8.44  thf('154', plain,
% 8.23/8.44      (![X0 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['152', '153'])).
% 8.23/8.44  thf('155', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['89', '90'])).
% 8.23/8.44  thf('156', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['124', '125'])).
% 8.23/8.44  thf('157', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.23/8.44      inference('demod', [status(thm)], ['154', '155', '156'])).
% 8.23/8.44  thf('158', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.23/8.44      inference('demod', [status(thm)], ['133', '157'])).
% 8.23/8.44  thf('159', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.23/8.44      inference('demod', [status(thm)], ['130', '158'])).
% 8.23/8.44  thf('160', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 8.23/8.44      inference('simplify', [status(thm)], ['12'])).
% 8.23/8.44  thf('161', plain,
% 8.23/8.44      (![X42 : $i, X44 : $i]:
% 8.23/8.44         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 8.23/8.44      inference('cnf', [status(esa)], [t3_subset])).
% 8.23/8.44  thf('162', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.23/8.44      inference('sup-', [status(thm)], ['160', '161'])).
% 8.23/8.44  thf('163', plain,
% 8.23/8.44      (![X24 : $i, X25 : $i]:
% 8.23/8.44         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 8.23/8.44          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 8.23/8.44      inference('demod', [status(thm)], ['102', '103'])).
% 8.23/8.44  thf('164', plain,
% 8.23/8.44      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k6_subset_1 @ X0 @ X0))),
% 8.23/8.44      inference('sup-', [status(thm)], ['162', '163'])).
% 8.23/8.44  thf('165', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.23/8.44      inference('demod', [status(thm)], ['159', '164'])).
% 8.23/8.44  thf('166', plain,
% 8.23/8.44      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.23/8.44      inference('demod', [status(thm)], ['139', '140'])).
% 8.23/8.44  thf('167', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         (~ (r1_tarski @ X1 @ (k6_subset_1 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 8.23/8.44      inference('sup-', [status(thm)], ['165', '166'])).
% 8.23/8.44  thf('168', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.23/8.44      inference('demod', [status(thm)], ['159', '164'])).
% 8.23/8.44  thf('169', plain,
% 8.23/8.44      (![X16 : $i, X17 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 8.23/8.44           = (X16))),
% 8.23/8.44      inference('demod', [status(thm)], ['85', '86', '91'])).
% 8.23/8.44  thf('170', plain,
% 8.23/8.44      (![X0 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['168', '169'])).
% 8.23/8.44  thf('171', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['124', '125'])).
% 8.23/8.44  thf('172', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 8.23/8.44      inference('demod', [status(thm)], ['170', '171'])).
% 8.23/8.44  thf(t100_xboole_1, axiom,
% 8.23/8.44    (![A:$i,B:$i]:
% 8.23/8.44     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.23/8.44  thf('173', plain,
% 8.23/8.44      (![X13 : $i, X14 : $i]:
% 8.23/8.44         ((k4_xboole_0 @ X13 @ X14)
% 8.23/8.44           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 8.23/8.44      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.23/8.44  thf('174', plain,
% 8.23/8.44      (![X35 : $i, X36 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 8.23/8.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.23/8.44  thf('175', plain,
% 8.23/8.44      (![X13 : $i, X14 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X13 @ X14)
% 8.23/8.44           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 8.23/8.44      inference('demod', [status(thm)], ['173', '174'])).
% 8.23/8.44  thf('176', plain,
% 8.23/8.44      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['172', '175'])).
% 8.23/8.44  thf('177', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 8.23/8.44      inference('demod', [status(thm)], ['167', '176'])).
% 8.23/8.44  thf('178', plain,
% 8.23/8.44      (![X1 : $i, X2 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X2 @ (k2_xboole_0 @ X2 @ X1)) = (k1_xboole_0))),
% 8.23/8.44      inference('sup-', [status(thm)], ['123', '177'])).
% 8.23/8.44  thf('179', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['149', '150'])).
% 8.23/8.44  thf('180', plain,
% 8.23/8.44      (![X16 : $i, X17 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 8.23/8.44           = (X16))),
% 8.23/8.44      inference('demod', [status(thm)], ['85', '86', '91'])).
% 8.23/8.44  thf('181', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 8.23/8.44           = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['179', '180'])).
% 8.23/8.44  thf('182', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ k1_xboole_0 @ 
% 8.23/8.44           (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['178', '181'])).
% 8.23/8.44  thf('183', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['149', '150'])).
% 8.23/8.44  thf('184', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['124', '125'])).
% 8.23/8.44  thf('185', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 8.23/8.44      inference('demod', [status(thm)], ['182', '183', '184'])).
% 8.23/8.44  thf('186', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['111', '185'])).
% 8.23/8.44  thf('187', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 8.23/8.44           = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['110', '186'])).
% 8.23/8.44  thf('188', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['149', '150'])).
% 8.23/8.44  thf('189', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 8.23/8.44           = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('demod', [status(thm)], ['187', '188'])).
% 8.23/8.44  thf('190', plain,
% 8.23/8.44      (![X13 : $i, X14 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X13 @ X14)
% 8.23/8.44           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 8.23/8.44      inference('demod', [status(thm)], ['173', '174'])).
% 8.23/8.44  thf('191', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.23/8.44           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.23/8.44      inference('sup+', [status(thm)], ['189', '190'])).
% 8.23/8.44  thf('192', plain,
% 8.23/8.44      (![X13 : $i, X14 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X13 @ X14)
% 8.23/8.44           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 8.23/8.44      inference('demod', [status(thm)], ['173', '174'])).
% 8.23/8.44  thf('193', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.23/8.44           = (k6_subset_1 @ X1 @ X0))),
% 8.23/8.44      inference('demod', [status(thm)], ['191', '192'])).
% 8.23/8.44  thf('194', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]:
% 8.23/8.44         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 8.23/8.44           = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('demod', [status(thm)], ['109', '193'])).
% 8.23/8.44  thf('195', plain,
% 8.23/8.44      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 8.23/8.44          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 8.23/8.44         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.44                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.44                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.44      inference('sup+', [status(thm)], ['84', '194'])).
% 8.23/8.44  thf('196', plain,
% 8.23/8.44      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['172', '175'])).
% 8.23/8.44  thf('197', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.23/8.44      inference('demod', [status(thm)], ['159', '164'])).
% 8.23/8.44  thf('198', plain,
% 8.23/8.44      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['172', '175'])).
% 8.23/8.44  thf('199', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.23/8.44      inference('demod', [status(thm)], ['197', '198'])).
% 8.23/8.44  thf('200', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['149', '150'])).
% 8.23/8.44  thf('201', plain,
% 8.23/8.44      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.23/8.44         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.44                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.44                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.44      inference('demod', [status(thm)], ['195', '196', '199', '200'])).
% 8.23/8.44  thf('202', plain,
% 8.23/8.44      (![X16 : $i, X17 : $i]:
% 8.23/8.44         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 8.23/8.44           = (X16))),
% 8.23/8.44      inference('demod', [status(thm)], ['85', '86', '91'])).
% 8.23/8.44  thf('203', plain,
% 8.23/8.44      ((((k2_xboole_0 @ (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 8.23/8.44          k1_xboole_0) = (sk_B)))
% 8.23/8.44         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.44                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.44                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.44      inference('sup+', [status(thm)], ['201', '202'])).
% 8.23/8.44  thf('204', plain,
% 8.23/8.44      (((k1_tops_1 @ sk_A @ sk_B)
% 8.23/8.44         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.23/8.44      inference('demod', [status(thm)], ['17', '18', '23'])).
% 8.23/8.44  thf('205', plain,
% 8.23/8.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.23/8.44      inference('sup+', [status(thm)], ['89', '90'])).
% 8.23/8.44  thf('206', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.23/8.44      inference('sup+', [status(thm)], ['124', '125'])).
% 8.23/8.44  thf('207', plain,
% 8.23/8.44      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 8.23/8.44         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.44                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.44                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.44      inference('demod', [status(thm)], ['203', '204', '205', '206'])).
% 8.23/8.44  thf('208', plain,
% 8.23/8.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.44  thf(fc9_tops_1, axiom,
% 8.23/8.44    (![A:$i,B:$i]:
% 8.23/8.44     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 8.23/8.44         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.23/8.44       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 8.23/8.44  thf('209', plain,
% 8.23/8.44      (![X47 : $i, X48 : $i]:
% 8.23/8.44         (~ (l1_pre_topc @ X47)
% 8.23/8.44          | ~ (v2_pre_topc @ X47)
% 8.23/8.44          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 8.23/8.44          | (v3_pre_topc @ (k1_tops_1 @ X47 @ X48) @ X47))),
% 8.23/8.44      inference('cnf', [status(esa)], [fc9_tops_1])).
% 8.23/8.44  thf('210', plain,
% 8.23/8.44      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 8.23/8.44        | ~ (v2_pre_topc @ sk_A)
% 8.23/8.44        | ~ (l1_pre_topc @ sk_A))),
% 8.23/8.44      inference('sup-', [status(thm)], ['208', '209'])).
% 8.23/8.44  thf('211', plain, ((v2_pre_topc @ sk_A)),
% 8.23/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.44  thf('212', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.44  thf('213', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 8.23/8.44      inference('demod', [status(thm)], ['210', '211', '212'])).
% 8.23/8.44  thf('214', plain,
% 8.23/8.44      (((v3_pre_topc @ sk_B @ sk_A))
% 8.23/8.44         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.44                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.44                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 8.23/8.44      inference('sup+', [status(thm)], ['207', '213'])).
% 8.23/8.44  thf('215', plain,
% 8.23/8.44      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 8.23/8.44      inference('split', [status(esa)], ['0'])).
% 8.23/8.44  thf('216', plain,
% 8.23/8.44      (~
% 8.23/8.44       (((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.44          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.44             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 8.23/8.44       ((v3_pre_topc @ sk_B @ sk_A))),
% 8.23/8.44      inference('sup-', [status(thm)], ['214', '215'])).
% 8.23/8.44  thf('217', plain, ($false),
% 8.23/8.44      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '216'])).
% 8.23/8.44  
% 8.23/8.44  % SZS output end Refutation
% 8.23/8.44  
% 8.23/8.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
