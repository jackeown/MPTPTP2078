%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2KagfUV7r6

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:25 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 336 expanded)
%              Number of leaves         :   45 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          : 1498 (3553 expanded)
%              Number of equality atoms :  110 ( 259 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( ( k1_tops_1 @ X63 @ X62 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X63 ) @ X62 @ ( k2_tops_1 @ X63 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k6_subset_1 @ X44 @ X46 ) ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
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
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( v3_pre_topc @ X55 @ X56 )
      | ~ ( r1_tarski @ X55 @ X57 )
      | ( r1_tarski @ X55 @ ( k1_tops_1 @ X56 @ X57 ) )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
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
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k2_tops_1 @ X54 @ X53 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X54 ) @ ( k2_pre_topc @ X54 @ X53 ) @ ( k1_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
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

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X49 @ X50 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X36 @ X35 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('52',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k2_pre_topc @ X61 @ X60 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X61 ) @ X60 @ ( k2_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k6_subset_1 @ X44 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('61',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('63',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('65',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('67',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k6_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X17 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('69',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) ) @ X18 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('71',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('73',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('75',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X30 @ X29 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('79',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k6_subset_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ X0 ) )
      = ( k6_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('86',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X30 @ X29 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('87',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X30 @ X29 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('88',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) ) @ X18 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('89',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('90',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('91',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k6_subset_1 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85','86','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X30 @ X29 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('98',plain,(
    ! [X23: $i] :
      ( r1_tarski @ k1_xboole_0 @ X23 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('99',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('106',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('107',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('108',plain,(
    ! [X26: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('109',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('110',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('111',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k6_subset_1 @ X28 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('113',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['105','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','115'])).

thf('117',plain,
    ( ( sk_B
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','116'])).

thf('118',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('119',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('121',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X51 @ X52 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('122',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['119','125'])).

thf('127',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('128',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2KagfUV7r6
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.34  % CPULimit   : 60
% 0.21/0.34  % DateTime   : Tue Dec  1 16:18:36 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.74/1.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.98  % Solved by: fo/fo7.sh
% 1.74/1.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.98  % done 3937 iterations in 1.526s
% 1.74/1.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.98  % SZS output start Refutation
% 1.74/1.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.98  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.74/1.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.74/1.98  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.74/1.98  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.74/1.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.74/1.98  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.74/1.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.74/1.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.74/1.98  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.74/1.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.74/1.98  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.74/1.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.74/1.98  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.74/1.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.74/1.98  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.74/1.98  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.74/1.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.74/1.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.98  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.98  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.74/1.98  thf(t76_tops_1, conjecture,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.74/1.98           ( ( v3_pre_topc @ B @ A ) <=>
% 1.74/1.98             ( ( k2_tops_1 @ A @ B ) =
% 1.74/1.98               ( k7_subset_1 @
% 1.74/1.98                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.98    (~( ![A:$i]:
% 1.74/1.98        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.98          ( ![B:$i]:
% 1.74/1.98            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.74/1.98              ( ( v3_pre_topc @ B @ A ) <=>
% 1.74/1.98                ( ( k2_tops_1 @ A @ B ) =
% 1.74/1.98                  ( k7_subset_1 @
% 1.74/1.98                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.74/1.98    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.74/1.98  thf('0', plain,
% 1.74/1.98      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.74/1.98        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('1', plain,
% 1.74/1.98      (~
% 1.74/1.98       (((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.74/1.98       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.74/1.98      inference('split', [status(esa)], ['0'])).
% 1.74/1.98  thf('2', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(t74_tops_1, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( l1_pre_topc @ A ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.74/1.98           ( ( k1_tops_1 @ A @ B ) =
% 1.74/1.98             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.74/1.98  thf('3', plain,
% 1.74/1.98      (![X62 : $i, X63 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 1.74/1.98          | ((k1_tops_1 @ X63 @ X62)
% 1.74/1.98              = (k7_subset_1 @ (u1_struct_0 @ X63) @ X62 @ 
% 1.74/1.98                 (k2_tops_1 @ X63 @ X62)))
% 1.74/1.98          | ~ (l1_pre_topc @ X63))),
% 1.74/1.98      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.74/1.98  thf('4', plain,
% 1.74/1.98      ((~ (l1_pre_topc @ sk_A)
% 1.74/1.98        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.74/1.98            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.74/1.98               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['2', '3'])).
% 1.74/1.98  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('6', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(redefinition_k7_subset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.74/1.98       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.74/1.98  thf('7', plain,
% 1.74/1.98      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 1.74/1.98          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.74/1.98  thf(redefinition_k6_subset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.74/1.98  thf('8', plain,
% 1.74/1.98      (![X42 : $i, X43 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.74/1.98  thf('9', plain,
% 1.74/1.98      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 1.74/1.98          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k6_subset_1 @ X44 @ X46)))),
% 1.74/1.98      inference('demod', [status(thm)], ['7', '8'])).
% 1.74/1.98  thf('10', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.74/1.98           = (k6_subset_1 @ sk_B @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['6', '9'])).
% 1.74/1.98  thf('11', plain,
% 1.74/1.98      (((k1_tops_1 @ sk_A @ sk_B)
% 1.74/1.98         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.74/1.98      inference('demod', [status(thm)], ['4', '5', '10'])).
% 1.74/1.98  thf(t36_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.74/1.98  thf('12', plain,
% 1.74/1.98      (![X24 : $i, X25 : $i]: (r1_tarski @ (k4_xboole_0 @ X24 @ X25) @ X24)),
% 1.74/1.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.74/1.98  thf('13', plain,
% 1.74/1.98      (![X42 : $i, X43 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.74/1.98  thf('14', plain,
% 1.74/1.98      (![X24 : $i, X25 : $i]: (r1_tarski @ (k6_subset_1 @ X24 @ X25) @ X24)),
% 1.74/1.98      inference('demod', [status(thm)], ['12', '13'])).
% 1.74/1.98  thf('15', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.74/1.98      inference('sup+', [status(thm)], ['11', '14'])).
% 1.74/1.98  thf('16', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('17', plain,
% 1.74/1.98      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.74/1.98        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('18', plain,
% 1.74/1.98      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.74/1.98      inference('split', [status(esa)], ['17'])).
% 1.74/1.98  thf('19', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(t56_tops_1, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( l1_pre_topc @ A ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.74/1.98           ( ![C:$i]:
% 1.74/1.98             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.74/1.98               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.74/1.98                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.74/1.98  thf('20', plain,
% 1.74/1.98      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 1.74/1.98          | ~ (v3_pre_topc @ X55 @ X56)
% 1.74/1.98          | ~ (r1_tarski @ X55 @ X57)
% 1.74/1.98          | (r1_tarski @ X55 @ (k1_tops_1 @ X56 @ X57))
% 1.74/1.98          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 1.74/1.98          | ~ (l1_pre_topc @ X56))),
% 1.74/1.98      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.74/1.98  thf('21', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (l1_pre_topc @ sk_A)
% 1.74/1.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.74/1.98          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.74/1.98          | ~ (r1_tarski @ sk_B @ X0)
% 1.74/1.98          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['19', '20'])).
% 1.74/1.98  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('23', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.74/1.98          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.74/1.98          | ~ (r1_tarski @ sk_B @ X0)
% 1.74/1.98          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.74/1.98      inference('demod', [status(thm)], ['21', '22'])).
% 1.74/1.98  thf('24', plain,
% 1.74/1.98      ((![X0 : $i]:
% 1.74/1.98          (~ (r1_tarski @ sk_B @ X0)
% 1.74/1.98           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.74/1.98           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.74/1.98         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['18', '23'])).
% 1.74/1.98  thf('25', plain,
% 1.74/1.98      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.74/1.98         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['16', '24'])).
% 1.74/1.98  thf(d10_xboole_0, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.74/1.98  thf('26', plain,
% 1.74/1.98      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.98  thf('27', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.74/1.98      inference('simplify', [status(thm)], ['26'])).
% 1.74/1.98  thf('28', plain,
% 1.74/1.98      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.74/1.98         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.74/1.98      inference('demod', [status(thm)], ['25', '27'])).
% 1.74/1.98  thf('29', plain,
% 1.74/1.98      (![X7 : $i, X9 : $i]:
% 1.74/1.98         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.74/1.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.98  thf('30', plain,
% 1.74/1.98      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.74/1.98         | ((k1_tops_1 @ sk_A @ sk_B) = (sk_B))))
% 1.74/1.98         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['28', '29'])).
% 1.74/1.98  thf('31', plain,
% 1.74/1.98      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.74/1.98         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['15', '30'])).
% 1.74/1.98  thf('32', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(l78_tops_1, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( l1_pre_topc @ A ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.74/1.98           ( ( k2_tops_1 @ A @ B ) =
% 1.74/1.98             ( k7_subset_1 @
% 1.74/1.98               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.74/1.98               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.74/1.98  thf('33', plain,
% 1.74/1.98      (![X53 : $i, X54 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.74/1.98          | ((k2_tops_1 @ X54 @ X53)
% 1.74/1.98              = (k7_subset_1 @ (u1_struct_0 @ X54) @ 
% 1.74/1.98                 (k2_pre_topc @ X54 @ X53) @ (k1_tops_1 @ X54 @ X53)))
% 1.74/1.98          | ~ (l1_pre_topc @ X54))),
% 1.74/1.98      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.74/1.98  thf('34', plain,
% 1.74/1.98      ((~ (l1_pre_topc @ sk_A)
% 1.74/1.98        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['32', '33'])).
% 1.74/1.98  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('36', plain,
% 1.74/1.98      (((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.74/1.98            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.74/1.98      inference('demod', [status(thm)], ['34', '35'])).
% 1.74/1.98  thf('37', plain,
% 1.74/1.98      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.74/1.98         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.74/1.98      inference('sup+', [status(thm)], ['31', '36'])).
% 1.74/1.98  thf('38', plain,
% 1.74/1.98      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.74/1.98         <= (~
% 1.74/1.98             (((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.74/1.98      inference('split', [status(esa)], ['0'])).
% 1.74/1.98  thf('39', plain,
% 1.74/1.98      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.74/1.98         <= (~
% 1.74/1.98             (((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.74/1.98             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['37', '38'])).
% 1.74/1.98  thf('40', plain,
% 1.74/1.98      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.74/1.98       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.74/1.98      inference('simplify', [status(thm)], ['39'])).
% 1.74/1.98  thf('41', plain,
% 1.74/1.98      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.74/1.98       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.74/1.98      inference('split', [status(esa)], ['17'])).
% 1.74/1.98  thf('42', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(dt_k2_tops_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( l1_pre_topc @ A ) & 
% 1.74/1.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.74/1.98       ( m1_subset_1 @
% 1.74/1.98         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.74/1.98  thf('43', plain,
% 1.74/1.98      (![X49 : $i, X50 : $i]:
% 1.74/1.98         (~ (l1_pre_topc @ X49)
% 1.74/1.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 1.74/1.98          | (m1_subset_1 @ (k2_tops_1 @ X49 @ X50) @ 
% 1.74/1.98             (k1_zfmisc_1 @ (u1_struct_0 @ X49))))),
% 1.74/1.98      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.74/1.98  thf('44', plain,
% 1.74/1.98      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.74/1.98         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.74/1.98        | ~ (l1_pre_topc @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['42', '43'])).
% 1.74/1.98  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('46', plain,
% 1.74/1.98      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.74/1.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('demod', [status(thm)], ['44', '45'])).
% 1.74/1.98  thf('47', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(dt_k4_subset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.74/1.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.98       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.74/1.98  thf('48', plain,
% 1.74/1.98      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.74/1.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 1.74/1.98          | (m1_subset_1 @ (k4_subset_1 @ X36 @ X35 @ X37) @ 
% 1.74/1.98             (k1_zfmisc_1 @ X36)))),
% 1.74/1.98      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 1.74/1.98  thf('49', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.74/1.98           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.74/1.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['47', '48'])).
% 1.74/1.98  thf('50', plain,
% 1.74/1.98      ((m1_subset_1 @ 
% 1.74/1.98        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.74/1.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['46', '49'])).
% 1.74/1.98  thf('51', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(t65_tops_1, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( l1_pre_topc @ A ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.74/1.98           ( ( k2_pre_topc @ A @ B ) =
% 1.74/1.98             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.74/1.98  thf('52', plain,
% 1.74/1.98      (![X60 : $i, X61 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 1.74/1.98          | ((k2_pre_topc @ X61 @ X60)
% 1.74/1.98              = (k4_subset_1 @ (u1_struct_0 @ X61) @ X60 @ 
% 1.74/1.98                 (k2_tops_1 @ X61 @ X60)))
% 1.74/1.98          | ~ (l1_pre_topc @ X61))),
% 1.74/1.98      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.74/1.98  thf('53', plain,
% 1.74/1.98      ((~ (l1_pre_topc @ sk_A)
% 1.74/1.98        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.74/1.98            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.74/1.98               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['51', '52'])).
% 1.74/1.98  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('55', plain,
% 1.74/1.98      (((k2_pre_topc @ sk_A @ sk_B)
% 1.74/1.98         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.74/1.98            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.74/1.98      inference('demod', [status(thm)], ['53', '54'])).
% 1.74/1.98  thf('56', plain,
% 1.74/1.98      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.74/1.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('demod', [status(thm)], ['50', '55'])).
% 1.74/1.98  thf('57', plain,
% 1.74/1.98      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 1.74/1.98          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k6_subset_1 @ X44 @ X46)))),
% 1.74/1.98      inference('demod', [status(thm)], ['7', '8'])).
% 1.74/1.98  thf('58', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.74/1.98           X0) = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['56', '57'])).
% 1.74/1.98  thf('59', plain,
% 1.74/1.98      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.74/1.98         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.74/1.98      inference('split', [status(esa)], ['17'])).
% 1.74/1.98  thf('60', plain,
% 1.74/1.98      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.74/1.98         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.74/1.98      inference('sup+', [status(thm)], ['58', '59'])).
% 1.74/1.98  thf(t111_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.74/1.98       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 1.74/1.98  thf('61', plain,
% 1.74/1.98      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.74/1.98         ((k4_xboole_0 @ (k3_xboole_0 @ X15 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 1.74/1.98           = (k3_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 1.74/1.98      inference('cnf', [status(esa)], [t111_xboole_1])).
% 1.74/1.98  thf(t12_setfam_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.74/1.98  thf('62', plain,
% 1.74/1.98      (![X47 : $i, X48 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.74/1.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.74/1.98  thf('63', plain,
% 1.74/1.98      (![X47 : $i, X48 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.74/1.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.74/1.98  thf('64', plain,
% 1.74/1.98      (![X42 : $i, X43 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.74/1.98  thf('65', plain,
% 1.74/1.98      (![X42 : $i, X43 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.74/1.98  thf('66', plain,
% 1.74/1.98      (![X47 : $i, X48 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.74/1.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.74/1.98  thf('67', plain,
% 1.74/1.98      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.74/1.98         ((k6_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X17)) @ 
% 1.74/1.98           (k1_setfam_1 @ (k2_tarski @ X16 @ X17)))
% 1.74/1.98           = (k1_setfam_1 @ (k2_tarski @ (k6_subset_1 @ X15 @ X16) @ X17)))),
% 1.74/1.98      inference('demod', [status(thm)], ['61', '62', '63', '64', '65', '66'])).
% 1.74/1.98  thf(t17_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.74/1.98  thf('68', plain,
% 1.74/1.98      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 1.74/1.98      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.74/1.98  thf('69', plain,
% 1.74/1.98      (![X47 : $i, X48 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.74/1.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.74/1.98  thf('70', plain,
% 1.74/1.98      (![X18 : $i, X19 : $i]:
% 1.74/1.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X18 @ X19)) @ X18)),
% 1.74/1.98      inference('demod', [status(thm)], ['68', '69'])).
% 1.74/1.98  thf(t28_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.74/1.98  thf('71', plain,
% 1.74/1.98      (![X21 : $i, X22 : $i]:
% 1.74/1.98         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 1.74/1.98      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.74/1.98  thf('72', plain,
% 1.74/1.98      (![X47 : $i, X48 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.74/1.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.74/1.98  thf('73', plain,
% 1.74/1.98      (![X21 : $i, X22 : $i]:
% 1.74/1.98         (((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (X21))
% 1.74/1.98          | ~ (r1_tarski @ X21 @ X22))),
% 1.74/1.98      inference('demod', [status(thm)], ['71', '72'])).
% 1.74/1.98  thf('74', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ 
% 1.74/1.98           (k2_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0))
% 1.74/1.98           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['70', '73'])).
% 1.74/1.98  thf(commutativity_k2_tarski, axiom,
% 1.74/1.98    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.74/1.98  thf('75', plain,
% 1.74/1.98      (![X29 : $i, X30 : $i]:
% 1.74/1.98         ((k2_tarski @ X30 @ X29) = (k2_tarski @ X29 @ X30))),
% 1.74/1.98      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.74/1.98  thf('76', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ 
% 1.74/1.98           (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))
% 1.74/1.98           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 1.74/1.98      inference('demod', [status(thm)], ['74', '75'])).
% 1.74/1.98  thf(t100_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.74/1.98  thf('77', plain,
% 1.74/1.98      (![X13 : $i, X14 : $i]:
% 1.74/1.98         ((k4_xboole_0 @ X13 @ X14)
% 1.74/1.98           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.74/1.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.98  thf('78', plain,
% 1.74/1.98      (![X42 : $i, X43 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.74/1.98  thf('79', plain,
% 1.74/1.98      (![X47 : $i, X48 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.74/1.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.74/1.98  thf('80', plain,
% 1.74/1.98      (![X13 : $i, X14 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X13 @ X14)
% 1.74/1.98           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 1.74/1.98      inference('demod', [status(thm)], ['77', '78', '79'])).
% 1.74/1.98  thf('81', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.74/1.98           = (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.74/1.98      inference('sup+', [status(thm)], ['76', '80'])).
% 1.74/1.98  thf('82', plain,
% 1.74/1.98      (![X13 : $i, X14 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X13 @ X14)
% 1.74/1.98           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 1.74/1.98      inference('demod', [status(thm)], ['77', '78', '79'])).
% 1.74/1.98  thf('83', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.74/1.98           = (k6_subset_1 @ X1 @ X0))),
% 1.74/1.98      inference('demod', [status(thm)], ['81', '82'])).
% 1.74/1.98  thf('84', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ 
% 1.74/1.98           (k2_tarski @ 
% 1.74/1.98            (k6_subset_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ X0))
% 1.74/1.98           = (k6_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['67', '83'])).
% 1.74/1.98  thf('85', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.74/1.98           = (k6_subset_1 @ X1 @ X0))),
% 1.74/1.98      inference('demod', [status(thm)], ['81', '82'])).
% 1.74/1.98  thf('86', plain,
% 1.74/1.98      (![X29 : $i, X30 : $i]:
% 1.74/1.98         ((k2_tarski @ X30 @ X29) = (k2_tarski @ X29 @ X30))),
% 1.74/1.98      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.74/1.98  thf('87', plain,
% 1.74/1.98      (![X29 : $i, X30 : $i]:
% 1.74/1.98         ((k2_tarski @ X30 @ X29) = (k2_tarski @ X29 @ X30))),
% 1.74/1.98      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.74/1.98  thf('88', plain,
% 1.74/1.98      (![X18 : $i, X19 : $i]:
% 1.74/1.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X18 @ X19)) @ X18)),
% 1.74/1.98      inference('demod', [status(thm)], ['68', '69'])).
% 1.74/1.98  thf(l32_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.74/1.98  thf('89', plain,
% 1.74/1.98      (![X10 : $i, X12 : $i]:
% 1.74/1.98         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 1.74/1.98          | ~ (r1_tarski @ X10 @ X12))),
% 1.74/1.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.74/1.98  thf('90', plain,
% 1.74/1.98      (![X42 : $i, X43 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.74/1.98  thf('91', plain,
% 1.74/1.98      (![X10 : $i, X12 : $i]:
% 1.74/1.98         (((k6_subset_1 @ X10 @ X12) = (k1_xboole_0))
% 1.74/1.98          | ~ (r1_tarski @ X10 @ X12))),
% 1.74/1.98      inference('demod', [status(thm)], ['89', '90'])).
% 1.74/1.98  thf('92', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k6_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)
% 1.74/1.98           = (k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['88', '91'])).
% 1.74/1.98  thf('93', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k6_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 1.74/1.98           = (k1_xboole_0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['87', '92'])).
% 1.74/1.98  thf('94', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ X0 @ (k6_subset_1 @ X1 @ X0)))
% 1.74/1.98           = (k1_xboole_0))),
% 1.74/1.98      inference('demod', [status(thm)], ['84', '85', '86', '93'])).
% 1.74/1.98  thf('95', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.74/1.98           = (k6_subset_1 @ X1 @ X0))),
% 1.74/1.98      inference('demod', [status(thm)], ['81', '82'])).
% 1.74/1.98  thf('96', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X0 @ k1_xboole_0)
% 1.74/1.98           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 1.74/1.98      inference('sup+', [status(thm)], ['94', '95'])).
% 1.74/1.98  thf('97', plain,
% 1.74/1.98      (![X29 : $i, X30 : $i]:
% 1.74/1.98         ((k2_tarski @ X30 @ X29) = (k2_tarski @ X29 @ X30))),
% 1.74/1.98      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.74/1.98  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.74/1.98  thf('98', plain, (![X23 : $i]: (r1_tarski @ k1_xboole_0 @ X23)),
% 1.74/1.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.74/1.98  thf('99', plain,
% 1.74/1.98      (![X21 : $i, X22 : $i]:
% 1.74/1.98         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 1.74/1.98      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.74/1.98  thf('100', plain,
% 1.74/1.98      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['98', '99'])).
% 1.74/1.98  thf('101', plain,
% 1.74/1.98      (![X47 : $i, X48 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.74/1.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.74/1.98  thf('102', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 1.74/1.98      inference('demod', [status(thm)], ['100', '101'])).
% 1.74/1.98  thf('103', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['97', '102'])).
% 1.74/1.98  thf('104', plain,
% 1.74/1.98      (![X13 : $i, X14 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X13 @ X14)
% 1.74/1.98           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 1.74/1.98      inference('demod', [status(thm)], ['77', '78', '79'])).
% 1.74/1.98  thf('105', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['103', '104'])).
% 1.74/1.98  thf(t4_boole, axiom,
% 1.74/1.98    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.74/1.98  thf('106', plain,
% 1.74/1.98      (![X26 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [t4_boole])).
% 1.74/1.98  thf('107', plain,
% 1.74/1.98      (![X42 : $i, X43 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.74/1.98  thf('108', plain,
% 1.74/1.98      (![X26 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 1.74/1.98      inference('demod', [status(thm)], ['106', '107'])).
% 1.74/1.98  thf(t98_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.74/1.98  thf('109', plain,
% 1.74/1.98      (![X27 : $i, X28 : $i]:
% 1.74/1.98         ((k2_xboole_0 @ X27 @ X28)
% 1.74/1.98           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 1.74/1.98      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.74/1.98  thf('110', plain,
% 1.74/1.98      (![X42 : $i, X43 : $i]:
% 1.74/1.98         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.74/1.98  thf('111', plain,
% 1.74/1.98      (![X27 : $i, X28 : $i]:
% 1.74/1.98         ((k2_xboole_0 @ X27 @ X28)
% 1.74/1.98           = (k5_xboole_0 @ X27 @ (k6_subset_1 @ X28 @ X27)))),
% 1.74/1.98      inference('demod', [status(thm)], ['109', '110'])).
% 1.74/1.98  thf('112', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['108', '111'])).
% 1.74/1.98  thf(t1_boole, axiom,
% 1.74/1.98    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.74/1.98  thf('113', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 1.74/1.98      inference('cnf', [status(esa)], [t1_boole])).
% 1.74/1.98  thf('114', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['112', '113'])).
% 1.74/1.98  thf('115', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.74/1.98      inference('demod', [status(thm)], ['105', '114'])).
% 1.74/1.98  thf('116', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((X0) = (k6_subset_1 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['96', '115'])).
% 1.74/1.98  thf('117', plain,
% 1.74/1.98      ((((sk_B) = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.74/1.98         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.74/1.98      inference('sup+', [status(thm)], ['60', '116'])).
% 1.74/1.98  thf('118', plain,
% 1.74/1.98      (((k1_tops_1 @ sk_A @ sk_B)
% 1.74/1.98         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.74/1.98      inference('demod', [status(thm)], ['4', '5', '10'])).
% 1.74/1.98  thf('119', plain,
% 1.74/1.98      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.74/1.98         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.74/1.98      inference('sup+', [status(thm)], ['117', '118'])).
% 1.74/1.98  thf('120', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(fc9_tops_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.74/1.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.74/1.98       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.74/1.98  thf('121', plain,
% 1.74/1.98      (![X51 : $i, X52 : $i]:
% 1.74/1.98         (~ (l1_pre_topc @ X51)
% 1.74/1.98          | ~ (v2_pre_topc @ X51)
% 1.74/1.98          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 1.74/1.98          | (v3_pre_topc @ (k1_tops_1 @ X51 @ X52) @ X51))),
% 1.74/1.98      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.74/1.98  thf('122', plain,
% 1.74/1.98      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.74/1.98        | ~ (v2_pre_topc @ sk_A)
% 1.74/1.98        | ~ (l1_pre_topc @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['120', '121'])).
% 1.74/1.98  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('125', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.74/1.98      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.74/1.98  thf('126', plain,
% 1.74/1.98      (((v3_pre_topc @ sk_B @ sk_A))
% 1.74/1.98         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.74/1.98      inference('sup+', [status(thm)], ['119', '125'])).
% 1.74/1.98  thf('127', plain,
% 1.74/1.98      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.74/1.98      inference('split', [status(esa)], ['0'])).
% 1.74/1.98  thf('128', plain,
% 1.74/1.98      (~
% 1.74/1.98       (((k2_tops_1 @ sk_A @ sk_B)
% 1.74/1.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.74/1.98       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['126', '127'])).
% 1.74/1.98  thf('129', plain, ($false),
% 1.74/1.98      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '128'])).
% 1.74/1.98  
% 1.74/1.98  % SZS output end Refutation
% 1.74/1.98  
% 1.83/1.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
