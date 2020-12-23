%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bd4Z8UXcdd

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:20 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 140 expanded)
%              Number of leaves         :   28 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  675 (1514 expanded)
%              Number of equality atoms :   41 (  75 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t75_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
              = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k2_pre_topc @ X36 @ X35 ) @ ( k1_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ ( k2_tops_1 @ X40 @ ( k2_tops_1 @ X40 @ X39 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('15',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l79_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) )
            = ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k2_pre_topc @ X38 @ ( k2_tops_1 @ X38 @ X37 ) )
        = ( k2_tops_1 @ X38 @ X37 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[l79_tops_1])).

thf('22',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('49',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','52'])).

thf('54',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','25','28','53'])).

thf('55',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bd4Z8UXcdd
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.91/1.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.12  % Solved by: fo/fo7.sh
% 0.91/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.12  % done 2101 iterations in 0.674s
% 0.91/1.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.12  % SZS output start Refutation
% 0.91/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.12  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.91/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.12  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.91/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.12  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.91/1.12  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.91/1.12  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.12  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.91/1.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.12  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.91/1.12  thf(t75_tops_1, conjecture,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.91/1.12             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.91/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.12    (~( ![A:$i]:
% 0.91/1.12        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.12          ( ![B:$i]:
% 0.91/1.12            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.91/1.12                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.91/1.12    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 0.91/1.12  thf('0', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(dt_k2_tops_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.12       ( m1_subset_1 @
% 0.91/1.12         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.12  thf('1', plain,
% 0.91/1.12      (![X33 : $i, X34 : $i]:
% 0.91/1.12         (~ (l1_pre_topc @ X33)
% 0.91/1.12          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.91/1.12          | (m1_subset_1 @ (k2_tops_1 @ X33 @ X34) @ 
% 0.91/1.12             (k1_zfmisc_1 @ (u1_struct_0 @ X33))))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.91/1.12  thf('2', plain,
% 0.91/1.12      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.12        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.12  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('4', plain,
% 0.91/1.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.12  thf('5', plain,
% 0.91/1.12      (![X33 : $i, X34 : $i]:
% 0.91/1.12         (~ (l1_pre_topc @ X33)
% 0.91/1.12          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.91/1.12          | (m1_subset_1 @ (k2_tops_1 @ X33 @ X34) @ 
% 0.91/1.12             (k1_zfmisc_1 @ (u1_struct_0 @ X33))))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.91/1.12  thf('6', plain,
% 0.91/1.12      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.12        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.12  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('8', plain,
% 0.91/1.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['6', '7'])).
% 0.91/1.12  thf(l78_tops_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( l1_pre_topc @ A ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12           ( ( k2_tops_1 @ A @ B ) =
% 0.91/1.12             ( k7_subset_1 @
% 0.91/1.12               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.91/1.12               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.91/1.12  thf('9', plain,
% 0.91/1.12      (![X35 : $i, X36 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.91/1.12          | ((k2_tops_1 @ X36 @ X35)
% 0.91/1.12              = (k7_subset_1 @ (u1_struct_0 @ X36) @ 
% 0.91/1.12                 (k2_pre_topc @ X36 @ X35) @ (k1_tops_1 @ X36 @ X35)))
% 0.91/1.12          | ~ (l1_pre_topc @ X36))),
% 0.91/1.12      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.91/1.12  thf('10', plain,
% 0.91/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.12        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12               (k2_pre_topc @ sk_A @ 
% 0.91/1.12                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.91/1.12               (k1_tops_1 @ sk_A @ 
% 0.91/1.12                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.12  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('12', plain,
% 0.91/1.12      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12            (k2_pre_topc @ sk_A @ 
% 0.91/1.12             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.91/1.12            (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('demod', [status(thm)], ['10', '11'])).
% 0.91/1.12  thf('13', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(l80_tops_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.91/1.12             ( k1_xboole_0 ) ) ) ) ))).
% 0.91/1.12  thf('14', plain,
% 0.91/1.12      (![X39 : $i, X40 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.91/1.12          | ((k1_tops_1 @ X40 @ (k2_tops_1 @ X40 @ (k2_tops_1 @ X40 @ X39)))
% 0.91/1.12              = (k1_xboole_0))
% 0.91/1.12          | ~ (l1_pre_topc @ X40)
% 0.91/1.12          | ~ (v2_pre_topc @ X40))),
% 0.91/1.12      inference('cnf', [status(esa)], [l80_tops_1])).
% 0.91/1.12  thf('15', plain,
% 0.91/1.12      ((~ (v2_pre_topc @ sk_A)
% 0.91/1.12        | ~ (l1_pre_topc @ sk_A)
% 0.91/1.12        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12            = (k1_xboole_0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['13', '14'])).
% 0.91/1.12  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('18', plain,
% 0.91/1.12      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12         = (k1_xboole_0))),
% 0.91/1.12      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.91/1.12  thf('19', plain,
% 0.91/1.12      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12            (k2_pre_topc @ sk_A @ 
% 0.91/1.12             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.91/1.12            k1_xboole_0))),
% 0.91/1.12      inference('demod', [status(thm)], ['12', '18'])).
% 0.91/1.12  thf('20', plain,
% 0.91/1.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.12  thf(l79_tops_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12           ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) ) =
% 0.91/1.12             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.91/1.12  thf('21', plain,
% 0.91/1.12      (![X37 : $i, X38 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.91/1.12          | ((k2_pre_topc @ X38 @ (k2_tops_1 @ X38 @ X37))
% 0.91/1.12              = (k2_tops_1 @ X38 @ X37))
% 0.91/1.12          | ~ (l1_pre_topc @ X38)
% 0.91/1.12          | ~ (v2_pre_topc @ X38))),
% 0.91/1.12      inference('cnf', [status(esa)], [l79_tops_1])).
% 0.91/1.12  thf('22', plain,
% 0.91/1.12      ((~ (v2_pre_topc @ sk_A)
% 0.91/1.12        | ~ (l1_pre_topc @ sk_A)
% 0.91/1.12        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.12  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('25', plain,
% 0.91/1.12      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.91/1.12  thf('26', plain,
% 0.91/1.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['6', '7'])).
% 0.91/1.12  thf(redefinition_k7_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.91/1.12  thf('27', plain,
% 0.91/1.12      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.91/1.12          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.91/1.12  thf('28', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 0.91/1.12           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.12  thf(t36_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.91/1.12  thf('29', plain,
% 0.91/1.12      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.91/1.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.91/1.12  thf(t3_xboole_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.12  thf('30', plain,
% 0.91/1.12      (![X15 : $i]:
% 0.91/1.12         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.12  thf('31', plain,
% 0.91/1.12      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.12  thf(l32_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.12  thf('32', plain,
% 0.91/1.12      (![X5 : $i, X6 : $i]:
% 0.91/1.12         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.91/1.12  thf('33', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['31', '32'])).
% 0.91/1.12  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.12      inference('simplify', [status(thm)], ['33'])).
% 0.91/1.12  thf(t3_subset, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.12  thf('35', plain,
% 0.91/1.12      (![X28 : $i, X30 : $i]:
% 0.91/1.12         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.12  thf('36', plain,
% 0.91/1.12      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.12  thf(d5_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.91/1.12  thf('37', plain,
% 0.91/1.12      (![X21 : $i, X22 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 0.91/1.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.12  thf('38', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['36', '37'])).
% 0.91/1.12  thf(d10_xboole_0, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.12  thf('39', plain,
% 0.91/1.12      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.12  thf('40', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.91/1.12      inference('simplify', [status(thm)], ['39'])).
% 0.91/1.12  thf('41', plain,
% 0.91/1.12      (![X28 : $i, X30 : $i]:
% 0.91/1.12         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.12  thf('42', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf(involutiveness_k3_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.91/1.12  thf('43', plain,
% 0.91/1.12      (![X23 : $i, X24 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 0.91/1.12          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.91/1.12      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.91/1.12  thf('44', plain,
% 0.91/1.12      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.12  thf('45', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf('46', plain,
% 0.91/1.12      (![X21 : $i, X22 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 0.91/1.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.12  thf('47', plain,
% 0.91/1.12      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['45', '46'])).
% 0.91/1.12  thf('48', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.91/1.12      inference('simplify', [status(thm)], ['39'])).
% 0.91/1.12  thf('49', plain,
% 0.91/1.12      (![X5 : $i, X7 : $i]:
% 0.91/1.12         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.91/1.12      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.91/1.12  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['48', '49'])).
% 0.91/1.12  thf('51', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['47', '50'])).
% 0.91/1.12  thf('52', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.12      inference('demod', [status(thm)], ['44', '51'])).
% 0.91/1.12  thf('53', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.12      inference('demod', [status(thm)], ['38', '52'])).
% 0.91/1.12  thf('54', plain,
% 0.91/1.12      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)], ['19', '25', '28', '53'])).
% 0.91/1.12  thf('55', plain,
% 0.91/1.12      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('56', plain, ($false),
% 0.91/1.12      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.91/1.12  
% 0.91/1.12  % SZS output end Refutation
% 0.91/1.12  
% 0.91/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
