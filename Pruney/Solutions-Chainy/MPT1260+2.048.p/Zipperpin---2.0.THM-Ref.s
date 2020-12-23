%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7LzizGnzRe

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:30 EST 2020

% Result     : Theorem 10.58s
% Output     : Refutation 10.58s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 225 expanded)
%              Number of leaves         :   35 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          : 1194 (2817 expanded)
%              Number of equality atoms :   75 ( 159 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X78: $i,X79: $i,X80: $i] :
      ( ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X79 ) ) )
      | ~ ( v3_pre_topc @ X78 @ X79 )
      | ~ ( r1_tarski @ X78 @ X80 )
      | ( r1_tarski @ X78 @ ( k1_tops_1 @ X79 @ X80 ) )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X79 ) ) )
      | ~ ( l1_pre_topc @ X79 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X85: $i,X86: $i] :
      ( ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X86 ) ) )
      | ( ( k1_tops_1 @ X86 @ X85 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X86 ) @ X85 @ ( k2_tops_1 @ X86 @ X85 ) ) )
      | ~ ( l1_pre_topc @ X86 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( ( k7_subset_1 @ X47 @ X46 @ X48 )
        = ( k4_xboole_0 @ X46 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X77 ) ) )
      | ( ( k2_tops_1 @ X77 @ X76 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X77 ) @ ( k2_pre_topc @ X77 @ X76 ) @ ( k1_tops_1 @ X77 @ X76 ) ) )
      | ~ ( l1_pre_topc @ X77 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X72: $i,X73: $i] :
      ( ~ ( l1_pre_topc @ X72 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X72 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X72 @ X73 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X72 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X32 @ X31 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('50',plain,(
    ! [X83: $i,X84: $i] :
      ( ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X84 ) ) )
      | ( ( k2_pre_topc @ X84 @ X83 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X84 ) @ X83 @ ( k2_tops_1 @ X84 @ X83 ) ) )
      | ~ ( l1_pre_topc @ X84 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( ( k7_subset_1 @ X47 @ X46 @ X48 )
        = ( k4_xboole_0 @ X46 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('62',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('64',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('71',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('72',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('76',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['63','81'])).

thf('83',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['58','82'])).

thf('84',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('85',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('87',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( l1_pre_topc @ X74 )
      | ~ ( v2_pre_topc @ X74 )
      | ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X74 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X74 @ X75 ) @ X74 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('88',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['85','91'])).

thf('93',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7LzizGnzRe
% 0.16/0.35  % Computer   : n007.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % DateTime   : Tue Dec  1 09:32:21 EST 2020
% 0.16/0.35  % CPUTime    : 
% 0.16/0.35  % Running portfolio for 600 s
% 0.16/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.35  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 10.58/10.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.58/10.78  % Solved by: fo/fo7.sh
% 10.58/10.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.58/10.78  % done 16953 iterations in 10.309s
% 10.58/10.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.58/10.78  % SZS output start Refutation
% 10.58/10.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.58/10.78  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 10.58/10.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.58/10.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.58/10.78  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 10.58/10.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 10.58/10.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 10.58/10.78  thf(sk_A_type, type, sk_A: $i).
% 10.58/10.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 10.58/10.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.58/10.78  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 10.58/10.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 10.58/10.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.58/10.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.58/10.78  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 10.58/10.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.58/10.78  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 10.58/10.78  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 10.58/10.78  thf(t76_tops_1, conjecture,
% 10.58/10.78    (![A:$i]:
% 10.58/10.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.58/10.78       ( ![B:$i]:
% 10.58/10.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.58/10.78           ( ( v3_pre_topc @ B @ A ) <=>
% 10.58/10.78             ( ( k2_tops_1 @ A @ B ) =
% 10.58/10.78               ( k7_subset_1 @
% 10.58/10.78                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 10.58/10.78  thf(zf_stmt_0, negated_conjecture,
% 10.58/10.78    (~( ![A:$i]:
% 10.58/10.78        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.58/10.78          ( ![B:$i]:
% 10.58/10.78            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.58/10.78              ( ( v3_pre_topc @ B @ A ) <=>
% 10.58/10.78                ( ( k2_tops_1 @ A @ B ) =
% 10.58/10.78                  ( k7_subset_1 @
% 10.58/10.78                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 10.58/10.78    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 10.58/10.78  thf('0', plain,
% 10.58/10.78      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 10.58/10.78        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('1', plain,
% 10.58/10.78      (~
% 10.58/10.78       (((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 10.58/10.78       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 10.58/10.78      inference('split', [status(esa)], ['0'])).
% 10.58/10.78  thf('2', plain,
% 10.58/10.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('3', plain,
% 10.58/10.78      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 10.58/10.78        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('4', plain,
% 10.58/10.78      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 10.58/10.78      inference('split', [status(esa)], ['3'])).
% 10.58/10.78  thf('5', plain,
% 10.58/10.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf(t56_tops_1, axiom,
% 10.58/10.78    (![A:$i]:
% 10.58/10.78     ( ( l1_pre_topc @ A ) =>
% 10.58/10.78       ( ![B:$i]:
% 10.58/10.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.58/10.78           ( ![C:$i]:
% 10.58/10.78             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.58/10.78               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 10.58/10.78                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 10.58/10.78  thf('6', plain,
% 10.58/10.78      (![X78 : $i, X79 : $i, X80 : $i]:
% 10.58/10.78         (~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (u1_struct_0 @ X79)))
% 10.58/10.78          | ~ (v3_pre_topc @ X78 @ X79)
% 10.58/10.78          | ~ (r1_tarski @ X78 @ X80)
% 10.58/10.78          | (r1_tarski @ X78 @ (k1_tops_1 @ X79 @ X80))
% 10.58/10.78          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (u1_struct_0 @ X79)))
% 10.58/10.78          | ~ (l1_pre_topc @ X79))),
% 10.58/10.78      inference('cnf', [status(esa)], [t56_tops_1])).
% 10.58/10.78  thf('7', plain,
% 10.58/10.78      (![X0 : $i]:
% 10.58/10.78         (~ (l1_pre_topc @ sk_A)
% 10.58/10.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.58/10.78          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 10.58/10.78          | ~ (r1_tarski @ sk_B_1 @ X0)
% 10.58/10.78          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 10.58/10.78      inference('sup-', [status(thm)], ['5', '6'])).
% 10.58/10.78  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('9', plain,
% 10.58/10.78      (![X0 : $i]:
% 10.58/10.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.58/10.78          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 10.58/10.78          | ~ (r1_tarski @ sk_B_1 @ X0)
% 10.58/10.78          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 10.58/10.78      inference('demod', [status(thm)], ['7', '8'])).
% 10.58/10.78  thf('10', plain,
% 10.58/10.78      ((![X0 : $i]:
% 10.58/10.78          (~ (r1_tarski @ sk_B_1 @ X0)
% 10.58/10.78           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 10.58/10.78           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 10.58/10.78         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 10.58/10.78      inference('sup-', [status(thm)], ['4', '9'])).
% 10.58/10.78  thf('11', plain,
% 10.58/10.78      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 10.58/10.78         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 10.58/10.78         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 10.58/10.78      inference('sup-', [status(thm)], ['2', '10'])).
% 10.58/10.78  thf(d10_xboole_0, axiom,
% 10.58/10.78    (![A:$i,B:$i]:
% 10.58/10.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.58/10.78  thf('12', plain,
% 10.58/10.78      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 10.58/10.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.58/10.78  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 10.58/10.78      inference('simplify', [status(thm)], ['12'])).
% 10.58/10.78  thf('14', plain,
% 10.58/10.78      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 10.58/10.78         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 10.58/10.78      inference('demod', [status(thm)], ['11', '13'])).
% 10.58/10.78  thf('15', plain,
% 10.58/10.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf(t74_tops_1, axiom,
% 10.58/10.78    (![A:$i]:
% 10.58/10.78     ( ( l1_pre_topc @ A ) =>
% 10.58/10.78       ( ![B:$i]:
% 10.58/10.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.58/10.78           ( ( k1_tops_1 @ A @ B ) =
% 10.58/10.78             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 10.58/10.78  thf('16', plain,
% 10.58/10.78      (![X85 : $i, X86 : $i]:
% 10.58/10.78         (~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ (u1_struct_0 @ X86)))
% 10.58/10.78          | ((k1_tops_1 @ X86 @ X85)
% 10.58/10.78              = (k7_subset_1 @ (u1_struct_0 @ X86) @ X85 @ 
% 10.58/10.78                 (k2_tops_1 @ X86 @ X85)))
% 10.58/10.78          | ~ (l1_pre_topc @ X86))),
% 10.58/10.78      inference('cnf', [status(esa)], [t74_tops_1])).
% 10.58/10.78  thf('17', plain,
% 10.58/10.78      ((~ (l1_pre_topc @ sk_A)
% 10.58/10.78        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 10.58/10.78               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 10.58/10.78      inference('sup-', [status(thm)], ['15', '16'])).
% 10.58/10.78  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('19', plain,
% 10.58/10.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf(redefinition_k7_subset_1, axiom,
% 10.58/10.78    (![A:$i,B:$i,C:$i]:
% 10.58/10.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.58/10.78       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 10.58/10.78  thf('20', plain,
% 10.58/10.78      (![X46 : $i, X47 : $i, X48 : $i]:
% 10.58/10.78         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 10.58/10.78          | ((k7_subset_1 @ X47 @ X46 @ X48) = (k4_xboole_0 @ X46 @ X48)))),
% 10.58/10.78      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 10.58/10.78  thf('21', plain,
% 10.58/10.78      (![X0 : $i]:
% 10.58/10.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 10.58/10.78           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 10.58/10.78      inference('sup-', [status(thm)], ['19', '20'])).
% 10.58/10.78  thf('22', plain,
% 10.58/10.78      (((k1_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 10.58/10.78      inference('demod', [status(thm)], ['17', '18', '21'])).
% 10.58/10.78  thf(t36_xboole_1, axiom,
% 10.58/10.78    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 10.58/10.78  thf('23', plain,
% 10.58/10.78      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 10.58/10.78      inference('cnf', [status(esa)], [t36_xboole_1])).
% 10.58/10.78  thf('24', plain,
% 10.58/10.78      (![X2 : $i, X4 : $i]:
% 10.58/10.78         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 10.58/10.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.58/10.78  thf('25', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 10.58/10.78          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 10.58/10.78      inference('sup-', [status(thm)], ['23', '24'])).
% 10.58/10.78  thf('26', plain,
% 10.58/10.78      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 10.58/10.78        | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 10.58/10.78      inference('sup-', [status(thm)], ['22', '25'])).
% 10.58/10.78  thf('27', plain,
% 10.58/10.78      (((k1_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 10.58/10.78      inference('demod', [status(thm)], ['17', '18', '21'])).
% 10.58/10.78  thf('28', plain,
% 10.58/10.78      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 10.58/10.78        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 10.58/10.78      inference('demod', [status(thm)], ['26', '27'])).
% 10.58/10.78  thf('29', plain,
% 10.58/10.78      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 10.58/10.78         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 10.58/10.78      inference('sup-', [status(thm)], ['14', '28'])).
% 10.58/10.78  thf('30', plain,
% 10.58/10.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf(l78_tops_1, axiom,
% 10.58/10.78    (![A:$i]:
% 10.58/10.78     ( ( l1_pre_topc @ A ) =>
% 10.58/10.78       ( ![B:$i]:
% 10.58/10.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.58/10.78           ( ( k2_tops_1 @ A @ B ) =
% 10.58/10.78             ( k7_subset_1 @
% 10.58/10.78               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 10.58/10.78               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 10.58/10.78  thf('31', plain,
% 10.58/10.78      (![X76 : $i, X77 : $i]:
% 10.58/10.78         (~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (u1_struct_0 @ X77)))
% 10.58/10.78          | ((k2_tops_1 @ X77 @ X76)
% 10.58/10.78              = (k7_subset_1 @ (u1_struct_0 @ X77) @ 
% 10.58/10.78                 (k2_pre_topc @ X77 @ X76) @ (k1_tops_1 @ X77 @ X76)))
% 10.58/10.78          | ~ (l1_pre_topc @ X77))),
% 10.58/10.78      inference('cnf', [status(esa)], [l78_tops_1])).
% 10.58/10.78  thf('32', plain,
% 10.58/10.78      ((~ (l1_pre_topc @ sk_A)
% 10.58/10.78        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 10.58/10.78      inference('sup-', [status(thm)], ['30', '31'])).
% 10.58/10.78  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('34', plain,
% 10.58/10.78      (((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 10.58/10.78      inference('demod', [status(thm)], ['32', '33'])).
% 10.58/10.78  thf('35', plain,
% 10.58/10.78      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 10.58/10.78         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 10.58/10.78      inference('sup+', [status(thm)], ['29', '34'])).
% 10.58/10.78  thf('36', plain,
% 10.58/10.78      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 10.58/10.78         <= (~
% 10.58/10.78             (((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 10.58/10.78      inference('split', [status(esa)], ['0'])).
% 10.58/10.78  thf('37', plain,
% 10.58/10.78      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 10.58/10.78         <= (~
% 10.58/10.78             (((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 10.58/10.78             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 10.58/10.78      inference('sup-', [status(thm)], ['35', '36'])).
% 10.58/10.78  thf('38', plain,
% 10.58/10.78      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 10.58/10.78       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 10.58/10.78      inference('simplify', [status(thm)], ['37'])).
% 10.58/10.78  thf('39', plain,
% 10.58/10.78      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 10.58/10.78       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 10.58/10.78      inference('split', [status(esa)], ['3'])).
% 10.58/10.78  thf('40', plain,
% 10.58/10.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf(dt_k2_tops_1, axiom,
% 10.58/10.78    (![A:$i,B:$i]:
% 10.58/10.78     ( ( ( l1_pre_topc @ A ) & 
% 10.58/10.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.58/10.78       ( m1_subset_1 @
% 10.58/10.78         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 10.58/10.78  thf('41', plain,
% 10.58/10.78      (![X72 : $i, X73 : $i]:
% 10.58/10.78         (~ (l1_pre_topc @ X72)
% 10.58/10.78          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (u1_struct_0 @ X72)))
% 10.58/10.78          | (m1_subset_1 @ (k2_tops_1 @ X72 @ X73) @ 
% 10.58/10.78             (k1_zfmisc_1 @ (u1_struct_0 @ X72))))),
% 10.58/10.78      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 10.58/10.78  thf('42', plain,
% 10.58/10.78      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 10.58/10.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.58/10.78        | ~ (l1_pre_topc @ sk_A))),
% 10.58/10.78      inference('sup-', [status(thm)], ['40', '41'])).
% 10.58/10.78  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('44', plain,
% 10.58/10.78      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 10.58/10.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('demod', [status(thm)], ['42', '43'])).
% 10.58/10.78  thf('45', plain,
% 10.58/10.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf(dt_k4_subset_1, axiom,
% 10.58/10.78    (![A:$i,B:$i,C:$i]:
% 10.58/10.78     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 10.58/10.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 10.58/10.78       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 10.58/10.78  thf('46', plain,
% 10.58/10.78      (![X31 : $i, X32 : $i, X33 : $i]:
% 10.58/10.78         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 10.58/10.78          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 10.58/10.78          | (m1_subset_1 @ (k4_subset_1 @ X32 @ X31 @ X33) @ 
% 10.58/10.78             (k1_zfmisc_1 @ X32)))),
% 10.58/10.78      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 10.58/10.78  thf('47', plain,
% 10.58/10.78      (![X0 : $i]:
% 10.58/10.78         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 10.58/10.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.58/10.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 10.58/10.78      inference('sup-', [status(thm)], ['45', '46'])).
% 10.58/10.78  thf('48', plain,
% 10.58/10.78      ((m1_subset_1 @ 
% 10.58/10.78        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 10.58/10.78         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 10.58/10.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('sup-', [status(thm)], ['44', '47'])).
% 10.58/10.78  thf('49', plain,
% 10.58/10.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf(t65_tops_1, axiom,
% 10.58/10.78    (![A:$i]:
% 10.58/10.78     ( ( l1_pre_topc @ A ) =>
% 10.58/10.78       ( ![B:$i]:
% 10.58/10.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.58/10.78           ( ( k2_pre_topc @ A @ B ) =
% 10.58/10.78             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 10.58/10.78  thf('50', plain,
% 10.58/10.78      (![X83 : $i, X84 : $i]:
% 10.58/10.78         (~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ (u1_struct_0 @ X84)))
% 10.58/10.78          | ((k2_pre_topc @ X84 @ X83)
% 10.58/10.78              = (k4_subset_1 @ (u1_struct_0 @ X84) @ X83 @ 
% 10.58/10.78                 (k2_tops_1 @ X84 @ X83)))
% 10.58/10.78          | ~ (l1_pre_topc @ X84))),
% 10.58/10.78      inference('cnf', [status(esa)], [t65_tops_1])).
% 10.58/10.78  thf('51', plain,
% 10.58/10.78      ((~ (l1_pre_topc @ sk_A)
% 10.58/10.78        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 10.58/10.78            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 10.58/10.78               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 10.58/10.78      inference('sup-', [status(thm)], ['49', '50'])).
% 10.58/10.78  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('53', plain,
% 10.58/10.78      (((k2_pre_topc @ sk_A @ sk_B_1)
% 10.58/10.78         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 10.58/10.78            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 10.58/10.78      inference('demod', [status(thm)], ['51', '52'])).
% 10.58/10.78  thf('54', plain,
% 10.58/10.78      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 10.58/10.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('demod', [status(thm)], ['48', '53'])).
% 10.58/10.78  thf('55', plain,
% 10.58/10.78      (![X46 : $i, X47 : $i, X48 : $i]:
% 10.58/10.78         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 10.58/10.78          | ((k7_subset_1 @ X47 @ X46 @ X48) = (k4_xboole_0 @ X46 @ X48)))),
% 10.58/10.78      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 10.58/10.78  thf('56', plain,
% 10.58/10.78      (![X0 : $i]:
% 10.58/10.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 10.58/10.78           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 10.58/10.78      inference('sup-', [status(thm)], ['54', '55'])).
% 10.58/10.78  thf('57', plain,
% 10.58/10.78      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 10.58/10.78         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 10.58/10.78      inference('split', [status(esa)], ['3'])).
% 10.58/10.78  thf('58', plain,
% 10.58/10.78      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 10.58/10.78         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 10.58/10.78      inference('sup+', [status(thm)], ['56', '57'])).
% 10.58/10.78  thf('59', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 10.58/10.78      inference('simplify', [status(thm)], ['12'])).
% 10.58/10.78  thf(t28_xboole_1, axiom,
% 10.58/10.78    (![A:$i,B:$i]:
% 10.58/10.78     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 10.58/10.78  thf('60', plain,
% 10.58/10.78      (![X15 : $i, X16 : $i]:
% 10.58/10.78         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 10.58/10.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 10.58/10.78  thf('61', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 10.58/10.78      inference('sup-', [status(thm)], ['59', '60'])).
% 10.58/10.78  thf(t52_xboole_1, axiom,
% 10.58/10.78    (![A:$i,B:$i,C:$i]:
% 10.58/10.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 10.58/10.78       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 10.58/10.78  thf('62', plain,
% 10.58/10.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 10.58/10.78           = (k2_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ 
% 10.58/10.78              (k3_xboole_0 @ X22 @ X24)))),
% 10.58/10.78      inference('cnf', [status(esa)], [t52_xboole_1])).
% 10.58/10.78  thf('63', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 10.58/10.78           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 10.58/10.78      inference('sup+', [status(thm)], ['61', '62'])).
% 10.58/10.78  thf(t48_xboole_1, axiom,
% 10.58/10.78    (![A:$i,B:$i]:
% 10.58/10.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 10.58/10.78  thf('64', plain,
% 10.58/10.78      (![X20 : $i, X21 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 10.58/10.78           = (k3_xboole_0 @ X20 @ X21))),
% 10.58/10.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.58/10.78  thf('65', plain,
% 10.58/10.78      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 10.58/10.78      inference('cnf', [status(esa)], [t36_xboole_1])).
% 10.58/10.78  thf(l32_xboole_1, axiom,
% 10.58/10.78    (![A:$i,B:$i]:
% 10.58/10.78     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.58/10.78  thf('66', plain,
% 10.58/10.78      (![X5 : $i, X7 : $i]:
% 10.58/10.78         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 10.58/10.78      inference('cnf', [status(esa)], [l32_xboole_1])).
% 10.58/10.78  thf('67', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 10.58/10.78      inference('sup-', [status(thm)], ['65', '66'])).
% 10.58/10.78  thf('68', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 10.58/10.78      inference('sup+', [status(thm)], ['64', '67'])).
% 10.58/10.78  thf('69', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 10.58/10.78           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 10.58/10.78      inference('sup+', [status(thm)], ['61', '62'])).
% 10.58/10.78  thf('70', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 10.58/10.78           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 10.58/10.78      inference('sup+', [status(thm)], ['68', '69'])).
% 10.58/10.78  thf(t3_boole, axiom,
% 10.58/10.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 10.58/10.78  thf('71', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 10.58/10.78      inference('cnf', [status(esa)], [t3_boole])).
% 10.58/10.78  thf('72', plain,
% 10.58/10.78      (![X20 : $i, X21 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 10.58/10.78           = (k3_xboole_0 @ X20 @ X21))),
% 10.58/10.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.58/10.78  thf('73', plain,
% 10.58/10.78      (![X20 : $i, X21 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 10.58/10.78           = (k3_xboole_0 @ X20 @ X21))),
% 10.58/10.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.58/10.78  thf('74', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 10.58/10.78           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 10.58/10.78      inference('sup+', [status(thm)], ['72', '73'])).
% 10.58/10.78  thf('75', plain,
% 10.58/10.78      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 10.58/10.78      inference('cnf', [status(esa)], [t36_xboole_1])).
% 10.58/10.78  thf('76', plain,
% 10.58/10.78      (![X15 : $i, X16 : $i]:
% 10.58/10.78         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 10.58/10.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 10.58/10.78  thf('77', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 10.58/10.78           = (k4_xboole_0 @ X0 @ X1))),
% 10.58/10.78      inference('sup-', [status(thm)], ['75', '76'])).
% 10.58/10.78  thf(commutativity_k3_xboole_0, axiom,
% 10.58/10.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 10.58/10.78  thf('78', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.58/10.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 10.58/10.78  thf('79', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 10.58/10.78           = (k4_xboole_0 @ X0 @ X1))),
% 10.58/10.78      inference('demod', [status(thm)], ['77', '78'])).
% 10.58/10.78  thf('80', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 10.58/10.78           = (k4_xboole_0 @ X1 @ X0))),
% 10.58/10.78      inference('demod', [status(thm)], ['74', '79'])).
% 10.58/10.78  thf('81', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 10.58/10.78      inference('demod', [status(thm)], ['70', '71', '80'])).
% 10.58/10.78  thf('82', plain,
% 10.58/10.78      (![X0 : $i, X1 : $i]:
% 10.58/10.78         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 10.58/10.78      inference('demod', [status(thm)], ['63', '81'])).
% 10.58/10.78  thf('83', plain,
% 10.58/10.78      ((((k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 10.58/10.78         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 10.58/10.78      inference('sup+', [status(thm)], ['58', '82'])).
% 10.58/10.78  thf('84', plain,
% 10.58/10.78      (((k1_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 10.58/10.78      inference('demod', [status(thm)], ['17', '18', '21'])).
% 10.58/10.78  thf('85', plain,
% 10.58/10.78      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 10.58/10.78         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 10.58/10.78      inference('sup+', [status(thm)], ['83', '84'])).
% 10.58/10.78  thf('86', plain,
% 10.58/10.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf(fc9_tops_1, axiom,
% 10.58/10.78    (![A:$i,B:$i]:
% 10.58/10.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 10.58/10.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.58/10.78       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 10.58/10.78  thf('87', plain,
% 10.58/10.78      (![X74 : $i, X75 : $i]:
% 10.58/10.78         (~ (l1_pre_topc @ X74)
% 10.58/10.78          | ~ (v2_pre_topc @ X74)
% 10.58/10.78          | ~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (u1_struct_0 @ X74)))
% 10.58/10.78          | (v3_pre_topc @ (k1_tops_1 @ X74 @ X75) @ X74))),
% 10.58/10.78      inference('cnf', [status(esa)], [fc9_tops_1])).
% 10.58/10.78  thf('88', plain,
% 10.58/10.78      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 10.58/10.78        | ~ (v2_pre_topc @ sk_A)
% 10.58/10.78        | ~ (l1_pre_topc @ sk_A))),
% 10.58/10.78      inference('sup-', [status(thm)], ['86', '87'])).
% 10.58/10.78  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 10.58/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.58/10.78  thf('91', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 10.58/10.78      inference('demod', [status(thm)], ['88', '89', '90'])).
% 10.58/10.78  thf('92', plain,
% 10.58/10.78      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 10.58/10.78         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 10.58/10.78      inference('sup+', [status(thm)], ['85', '91'])).
% 10.58/10.78  thf('93', plain,
% 10.58/10.78      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 10.58/10.78      inference('split', [status(esa)], ['0'])).
% 10.58/10.78  thf('94', plain,
% 10.58/10.78      (~
% 10.58/10.78       (((k2_tops_1 @ sk_A @ sk_B_1)
% 10.58/10.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.58/10.78             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 10.58/10.78       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 10.58/10.78      inference('sup-', [status(thm)], ['92', '93'])).
% 10.58/10.78  thf('95', plain, ($false),
% 10.58/10.78      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '94'])).
% 10.58/10.78  
% 10.58/10.78  % SZS output end Refutation
% 10.58/10.78  
% 10.58/10.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
