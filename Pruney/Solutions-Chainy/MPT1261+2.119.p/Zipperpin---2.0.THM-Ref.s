%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JG86jGG4yM

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:56 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 255 expanded)
%              Number of leaves         :   30 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :  884 (3196 expanded)
%              Number of equality atoms :   60 ( 180 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k2_tops_1 @ X56 @ X55 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X56 ) @ ( k2_pre_topc @ X56 @ X55 ) @ ( k1_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v4_pre_topc @ X49 @ X50 )
      | ( ( k2_pre_topc @ X50 @ X49 )
        = X49 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k7_subset_1 @ X42 @ X41 @ X43 )
        = ( k4_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X36 @ X35 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k4_subset_1 @ X39 @ X38 @ X40 )
        = ( k2_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X34 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('30',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X36 @ X35 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('41',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k7_subset_1 @ X42 @ X41 @ X43 )
        = ( k4_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['28','43'])).

thf('45',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k2_pre_topc @ X58 @ X57 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X58 ) @ X57 @ ( k2_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('53',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X53 @ X54 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('54',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','57'])).

thf('59',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('60',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('62',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','60','61'])).

thf('63',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['12','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('65',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','63','64'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['14','60'])).

thf('70',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JG86jGG4yM
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:46:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 270 iterations in 0.157s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.62  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.62  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.36/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.62  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.62  thf(t77_tops_1, conjecture,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.62           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.62             ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.62               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i]:
% 0.36/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.62          ( ![B:$i]:
% 0.36/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.62              ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.62                ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.62                  ( k7_subset_1 @
% 0.36/0.62                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.36/0.62  thf('0', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(l78_tops_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( l1_pre_topc @ A ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.62           ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.62             ( k7_subset_1 @
% 0.36/0.62               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.36/0.62               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.62  thf('1', plain,
% 0.36/0.62      (![X55 : $i, X56 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.36/0.62          | ((k2_tops_1 @ X56 @ X55)
% 0.36/0.62              = (k7_subset_1 @ (u1_struct_0 @ X56) @ 
% 0.36/0.62                 (k2_pre_topc @ X56 @ X55) @ (k1_tops_1 @ X56 @ X55)))
% 0.36/0.62          | ~ (l1_pre_topc @ X56))),
% 0.36/0.62      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.36/0.62  thf('2', plain,
% 0.36/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.62        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.62  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.62            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.62  thf('5', plain,
% 0.36/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62             (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.62        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('6', plain,
% 0.36/0.62      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.62      inference('split', [status(esa)], ['5'])).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(t52_pre_topc, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( l1_pre_topc @ A ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.62           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.36/0.62             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.36/0.62               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.36/0.62  thf('8', plain,
% 0.36/0.62      (![X49 : $i, X50 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.36/0.62          | ~ (v4_pre_topc @ X49 @ X50)
% 0.36/0.62          | ((k2_pre_topc @ X50 @ X49) = (X49))
% 0.36/0.62          | ~ (l1_pre_topc @ X50))),
% 0.36/0.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.36/0.62  thf('9', plain,
% 0.36/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.62        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.36/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.62  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.62  thf('12', plain,
% 0.36/0.62      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.36/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['6', '11'])).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62              (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('14', plain,
% 0.36/0.62      (~
% 0.36/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.36/0.62       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.62      inference('split', [status(esa)], ['13'])).
% 0.36/0.62  thf('15', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.62       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.62  thf('16', plain,
% 0.36/0.62      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.36/0.62          | ((k7_subset_1 @ X42 @ X41 @ X43) = (k4_xboole_0 @ X41 @ X43)))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.62  thf('17', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('18', plain,
% 0.36/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62             (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.62      inference('split', [status(esa)], ['5'])).
% 0.36/0.62  thf('19', plain,
% 0.36/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['17', '18'])).
% 0.36/0.62  thf('20', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(dt_k7_subset_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.62       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.62  thf('21', plain,
% 0.36/0.62      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.36/0.62          | (m1_subset_1 @ (k7_subset_1 @ X36 @ X35 @ X37) @ 
% 0.36/0.62             (k1_zfmisc_1 @ X36)))),
% 0.36/0.62      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.36/0.62  thf('22', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.36/0.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.62  thf('23', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.36/0.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.36/0.62  thf('25', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.62       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.62  thf('26', plain,
% 0.36/0.62      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.36/0.62          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 0.36/0.62          | ((k4_subset_1 @ X39 @ X38 @ X40) = (k2_xboole_0 @ X38 @ X40)))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.62  thf('27', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.62            = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.62  thf('28', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62           (k4_xboole_0 @ sk_B @ X0))
% 0.36/0.62           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['24', '27'])).
% 0.36/0.62  thf(dt_k2_subset_1, axiom,
% 0.36/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.62  thf('29', plain,
% 0.36/0.62      (![X34 : $i]: (m1_subset_1 @ (k2_subset_1 @ X34) @ (k1_zfmisc_1 @ X34))),
% 0.36/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.36/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.62  thf('30', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.36/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.62  thf('31', plain, (![X34 : $i]: (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X34))),
% 0.36/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.62  thf('32', plain,
% 0.36/0.62      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.36/0.62          | (m1_subset_1 @ (k7_subset_1 @ X36 @ X35 @ X37) @ 
% 0.36/0.62             (k1_zfmisc_1 @ X36)))),
% 0.36/0.62      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.36/0.62  thf('33', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.62  thf(t3_subset, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.62  thf('34', plain,
% 0.36/0.62      (![X46 : $i, X47 : $i]:
% 0.36/0.62         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.62  thf('35', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k7_subset_1 @ X0 @ X0 @ X1) @ X0)),
% 0.36/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.62  thf(t12_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.62  thf('36', plain,
% 0.36/0.62      (![X4 : $i, X5 : $i]:
% 0.36/0.62         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.36/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.62  thf('37', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ (k7_subset_1 @ X0 @ X0 @ X1) @ X0) = (X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.62  thf('38', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.62  thf('39', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1)) = (X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['37', '38'])).
% 0.36/0.62  thf('40', plain, (![X34 : $i]: (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X34))),
% 0.36/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.62  thf('41', plain,
% 0.36/0.62      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.36/0.62          | ((k7_subset_1 @ X42 @ X41 @ X43) = (k4_xboole_0 @ X41 @ X43)))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.62  thf('42', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.62  thf('43', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['39', '42'])).
% 0.36/0.62  thf('44', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62           (k4_xboole_0 @ sk_B @ X0)) = (sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['28', '43'])).
% 0.36/0.62  thf('45', plain,
% 0.36/0.62      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.62          = (sk_B)))
% 0.36/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['19', '44'])).
% 0.36/0.62  thf('46', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(t65_tops_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( l1_pre_topc @ A ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.62           ( ( k2_pre_topc @ A @ B ) =
% 0.36/0.62             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.62  thf('47', plain,
% 0.36/0.62      (![X57 : $i, X58 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.36/0.62          | ((k2_pre_topc @ X58 @ X57)
% 0.36/0.62              = (k4_subset_1 @ (u1_struct_0 @ X58) @ X57 @ 
% 0.36/0.62                 (k2_tops_1 @ X58 @ X57)))
% 0.36/0.62          | ~ (l1_pre_topc @ X58))),
% 0.36/0.62      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.36/0.62  thf('48', plain,
% 0.36/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.62        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.62            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.62  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('50', plain,
% 0.36/0.62      (((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.62         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.36/0.62  thf('51', plain,
% 0.36/0.62      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.36/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['45', '50'])).
% 0.36/0.62  thf('52', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(fc1_tops_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.36/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.62       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.36/0.62  thf('53', plain,
% 0.36/0.62      (![X53 : $i, X54 : $i]:
% 0.36/0.62         (~ (l1_pre_topc @ X53)
% 0.36/0.62          | ~ (v2_pre_topc @ X53)
% 0.36/0.62          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.36/0.62          | (v4_pre_topc @ (k2_pre_topc @ X53 @ X54) @ X53))),
% 0.36/0.62      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.36/0.62  thf('54', plain,
% 0.36/0.62      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.36/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.62  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('57', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.36/0.62      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.36/0.62  thf('58', plain,
% 0.36/0.62      (((v4_pre_topc @ sk_B @ sk_A))
% 0.36/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['51', '57'])).
% 0.36/0.62  thf('59', plain,
% 0.36/0.62      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.62      inference('split', [status(esa)], ['13'])).
% 0.36/0.62  thf('60', plain,
% 0.36/0.62      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.62       ~
% 0.36/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.62  thf('61', plain,
% 0.36/0.62      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.62      inference('split', [status(esa)], ['5'])).
% 0.36/0.62  thf('62', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.62      inference('sat_resolution*', [status(thm)], ['14', '60', '61'])).
% 0.36/0.62  thf('63', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.36/0.62      inference('simpl_trail', [status(thm)], ['12', '62'])).
% 0.36/0.62  thf('64', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('65', plain,
% 0.36/0.62      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.62      inference('demod', [status(thm)], ['4', '63', '64'])).
% 0.36/0.62  thf('66', plain,
% 0.36/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62              (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.62         <= (~
% 0.36/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.62      inference('split', [status(esa)], ['13'])).
% 0.36/0.62  thf('67', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('68', plain,
% 0.36/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.62         <= (~
% 0.36/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.62      inference('demod', [status(thm)], ['66', '67'])).
% 0.36/0.62  thf('69', plain,
% 0.36/0.62      (~
% 0.36/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.62             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.62      inference('sat_resolution*', [status(thm)], ['14', '60'])).
% 0.36/0.62  thf('70', plain,
% 0.36/0.62      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.62         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.62      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.36/0.62  thf('71', plain, ($false),
% 0.36/0.62      inference('simplify_reflect-', [status(thm)], ['65', '70'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.50/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
