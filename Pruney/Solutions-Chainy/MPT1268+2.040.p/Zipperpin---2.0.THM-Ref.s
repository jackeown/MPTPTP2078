%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7xBqLCQDo0

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:21 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 709 expanded)
%              Number of leaves         :   25 ( 199 expanded)
%              Depth                    :   24
%              Number of atoms          : 1119 (10845 expanded)
%              Number of equality atoms :   50 ( 430 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t86_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( r1_tarski @ C @ B )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r1_tarski @ C @ B )
                      & ( v3_pre_topc @ C @ A ) )
                   => ( C = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tops_1])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    ! [X40: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X40 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X40 @ sk_A )
      | ~ ( r1_tarski @ X40 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X40: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X40 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X40 @ sk_A )
      | ~ ( r1_tarski @ X40 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B ) )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('22',plain,
    ( ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
       != X36 )
      | ( v3_pre_topc @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('25',plain,
    ( ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 )
        | ( ( k1_tops_1 @ X37 @ X36 )
         != X36 )
        | ( v3_pre_topc @ X36 @ X37 ) )
   <= ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 )
        | ( ( k1_tops_1 @ X37 @ X36 )
         != X36 )
        | ( v3_pre_topc @ X36 @ X37 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
       != X36 )
      | ( v3_pre_topc @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('28',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 )
        | ( ( k1_tops_1 @ X37 @ X36 )
         != X36 )
        | ( v3_pre_topc @ X36 @ X37 ) )
    | ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('33',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( ( k1_tops_1 @ X37 @ X36 )
       != X36 )
      | ( v3_pre_topc @ X36 @ X37 ) ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( ( k1_tops_1 @ X37 @ X36 )
       != X36 )
      | ( v3_pre_topc @ X36 @ X37 ) ) ),
    inference(simpl_trail,[status(thm)],['25','33'])).

thf('35',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ ( k1_tops_1 @ X26 @ X27 ) )
        = ( k1_tops_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('38',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','40','41','42'])).

thf('44',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('47',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k1_tops_1 @ X39 @ X38 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X38 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ~ ! [X40: $i] :
          ( ( X40 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X40 @ sk_A )
          | ~ ( r1_tarski @ X40 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['2','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X30 )
      | ~ ( v3_pre_topc @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r2_hidden @ X32 @ ( k1_tops_1 @ X31 @ X30 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v2_tops_1 @ X38 @ X39 )
      | ( ( k1_tops_1 @ X39 @ X38 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','55'])).

thf('73',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ sk_C_1 @ sk_B )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','74'])).

thf('76',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['53'])).

thf('77',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('78',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['4','55','77'])).

thf('79',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['80'])).

thf('83',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','55','82'])).

thf('84',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','79','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','85'])).

thf('87',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    r1_tarski @ sk_C_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['88'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('90',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('91',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['92'])).

thf('95',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','55','94'])).

thf('96',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7xBqLCQDo0
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.29/1.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.29/1.45  % Solved by: fo/fo7.sh
% 1.29/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.45  % done 2247 iterations in 0.999s
% 1.29/1.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.29/1.45  % SZS output start Refutation
% 1.29/1.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.29/1.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.29/1.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.29/1.45  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.29/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.29/1.45  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.29/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.29/1.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.29/1.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.29/1.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.29/1.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.29/1.45  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.29/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.29/1.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.29/1.45  thf(d3_tarski, axiom,
% 1.29/1.45    (![A:$i,B:$i]:
% 1.29/1.45     ( ( r1_tarski @ A @ B ) <=>
% 1.29/1.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.29/1.45  thf('0', plain,
% 1.29/1.45      (![X1 : $i, X3 : $i]:
% 1.29/1.45         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.29/1.45      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.45  thf(t86_tops_1, conjecture,
% 1.29/1.45    (![A:$i]:
% 1.29/1.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.45       ( ![B:$i]:
% 1.29/1.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.45           ( ( v2_tops_1 @ B @ A ) <=>
% 1.29/1.45             ( ![C:$i]:
% 1.29/1.45               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.45                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.29/1.45                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 1.29/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.45    (~( ![A:$i]:
% 1.29/1.45        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.45          ( ![B:$i]:
% 1.29/1.45            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.45              ( ( v2_tops_1 @ B @ A ) <=>
% 1.29/1.45                ( ![C:$i]:
% 1.29/1.45                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.45                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.29/1.45                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 1.29/1.45    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 1.29/1.45  thf('1', plain,
% 1.29/1.45      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('2', plain,
% 1.29/1.45      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.29/1.45         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.29/1.45      inference('split', [status(esa)], ['1'])).
% 1.29/1.45  thf('3', plain,
% 1.29/1.45      (![X40 : $i]:
% 1.29/1.45         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45          | ((X40) = (k1_xboole_0))
% 1.29/1.45          | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45          | ~ (r1_tarski @ X40 @ sk_B)
% 1.29/1.45          | (v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('4', plain,
% 1.29/1.45      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 1.29/1.45       (![X40 : $i]:
% 1.29/1.45          (((X40) = (k1_xboole_0))
% 1.29/1.45           | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45           | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45           | ~ (r1_tarski @ X40 @ sk_B)))),
% 1.29/1.45      inference('split', [status(esa)], ['3'])).
% 1.29/1.45  thf('5', plain,
% 1.29/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf(t3_subset, axiom,
% 1.29/1.45    (![A:$i,B:$i]:
% 1.29/1.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.29/1.45  thf('6', plain,
% 1.29/1.45      (![X18 : $i, X19 : $i]:
% 1.29/1.45         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.29/1.45      inference('cnf', [status(esa)], [t3_subset])).
% 1.29/1.45  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.29/1.45      inference('sup-', [status(thm)], ['5', '6'])).
% 1.29/1.45  thf('8', plain,
% 1.29/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf(t44_tops_1, axiom,
% 1.29/1.45    (![A:$i]:
% 1.29/1.45     ( ( l1_pre_topc @ A ) =>
% 1.29/1.45       ( ![B:$i]:
% 1.29/1.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.45           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.29/1.45  thf('9', plain,
% 1.29/1.45      (![X28 : $i, X29 : $i]:
% 1.29/1.45         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.29/1.45          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ X28)
% 1.29/1.45          | ~ (l1_pre_topc @ X29))),
% 1.29/1.45      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.29/1.45  thf('10', plain,
% 1.29/1.45      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.29/1.45      inference('sup-', [status(thm)], ['8', '9'])).
% 1.29/1.45  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.29/1.45      inference('demod', [status(thm)], ['10', '11'])).
% 1.29/1.45  thf(t1_xboole_1, axiom,
% 1.29/1.45    (![A:$i,B:$i,C:$i]:
% 1.29/1.45     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.29/1.45       ( r1_tarski @ A @ C ) ))).
% 1.29/1.45  thf('13', plain,
% 1.29/1.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.29/1.45         (~ (r1_tarski @ X9 @ X10)
% 1.29/1.45          | ~ (r1_tarski @ X10 @ X11)
% 1.29/1.45          | (r1_tarski @ X9 @ X11))),
% 1.29/1.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.29/1.45  thf('14', plain,
% 1.29/1.45      (![X0 : $i]:
% 1.29/1.45         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.29/1.45          | ~ (r1_tarski @ sk_B @ X0))),
% 1.29/1.45      inference('sup-', [status(thm)], ['12', '13'])).
% 1.29/1.45  thf('15', plain,
% 1.29/1.45      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.29/1.45      inference('sup-', [status(thm)], ['7', '14'])).
% 1.29/1.45  thf('16', plain,
% 1.29/1.45      (![X18 : $i, X20 : $i]:
% 1.29/1.45         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 1.29/1.45      inference('cnf', [status(esa)], [t3_subset])).
% 1.29/1.45  thf('17', plain,
% 1.29/1.45      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.29/1.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('sup-', [status(thm)], ['15', '16'])).
% 1.29/1.45  thf('18', plain,
% 1.29/1.45      (![X40 : $i]:
% 1.29/1.45         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45          | ((X40) = (k1_xboole_0))
% 1.29/1.45          | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45          | ~ (r1_tarski @ X40 @ sk_B)
% 1.29/1.45          | (v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('19', plain,
% 1.29/1.45      ((![X40 : $i]:
% 1.29/1.45          (((X40) = (k1_xboole_0))
% 1.29/1.45           | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45           | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45           | ~ (r1_tarski @ X40 @ sk_B)))
% 1.29/1.45         <= ((![X40 : $i]:
% 1.29/1.45                (((X40) = (k1_xboole_0))
% 1.29/1.45                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45                 | ~ (r1_tarski @ X40 @ sk_B))))),
% 1.29/1.45      inference('split', [status(esa)], ['18'])).
% 1.29/1.45  thf('20', plain,
% 1.29/1.45      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.29/1.45         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.29/1.45         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 1.29/1.45         <= ((![X40 : $i]:
% 1.29/1.45                (((X40) = (k1_xboole_0))
% 1.29/1.45                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45                 | ~ (r1_tarski @ X40 @ sk_B))))),
% 1.29/1.45      inference('sup-', [status(thm)], ['17', '19'])).
% 1.29/1.45  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.29/1.45      inference('demod', [status(thm)], ['10', '11'])).
% 1.29/1.45  thf('22', plain,
% 1.29/1.45      (((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.29/1.45         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 1.29/1.45         <= ((![X40 : $i]:
% 1.29/1.45                (((X40) = (k1_xboole_0))
% 1.29/1.45                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45                 | ~ (r1_tarski @ X40 @ sk_B))))),
% 1.29/1.45      inference('demod', [status(thm)], ['20', '21'])).
% 1.29/1.45  thf('23', plain,
% 1.29/1.45      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.29/1.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('sup-', [status(thm)], ['15', '16'])).
% 1.29/1.45  thf(t55_tops_1, axiom,
% 1.29/1.45    (![A:$i]:
% 1.29/1.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.45       ( ![B:$i]:
% 1.29/1.45         ( ( l1_pre_topc @ B ) =>
% 1.29/1.45           ( ![C:$i]:
% 1.29/1.45             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.45               ( ![D:$i]:
% 1.29/1.45                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.29/1.45                   ( ( ( v3_pre_topc @ D @ B ) =>
% 1.29/1.45                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 1.29/1.45                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 1.29/1.45                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 1.29/1.45  thf('24', plain,
% 1.29/1.45      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.29/1.45         (~ (l1_pre_topc @ X34)
% 1.29/1.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.29/1.45          | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.29/1.45          | (v3_pre_topc @ X36 @ X37)
% 1.29/1.45          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.29/1.45          | ~ (l1_pre_topc @ X37)
% 1.29/1.45          | ~ (v2_pre_topc @ X37))),
% 1.29/1.45      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.29/1.45  thf('25', plain,
% 1.29/1.45      ((![X36 : $i, X37 : $i]:
% 1.29/1.45          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.29/1.45           | ~ (l1_pre_topc @ X37)
% 1.29/1.45           | ~ (v2_pre_topc @ X37)
% 1.29/1.45           | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.29/1.45           | (v3_pre_topc @ X36 @ X37)))
% 1.29/1.45         <= ((![X36 : $i, X37 : $i]:
% 1.29/1.45                (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.29/1.45                 | ~ (l1_pre_topc @ X37)
% 1.29/1.45                 | ~ (v2_pre_topc @ X37)
% 1.29/1.45                 | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.29/1.45                 | (v3_pre_topc @ X36 @ X37))))),
% 1.29/1.45      inference('split', [status(esa)], ['24'])).
% 1.29/1.45  thf('26', plain,
% 1.29/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('27', plain,
% 1.29/1.45      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.29/1.45         (~ (l1_pre_topc @ X34)
% 1.29/1.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.29/1.45          | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.29/1.45          | (v3_pre_topc @ X36 @ X37)
% 1.29/1.45          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.29/1.45          | ~ (l1_pre_topc @ X37)
% 1.29/1.45          | ~ (v2_pre_topc @ X37))),
% 1.29/1.45      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.29/1.45  thf('28', plain,
% 1.29/1.45      ((![X34 : $i, X35 : $i]:
% 1.29/1.45          (~ (l1_pre_topc @ X34)
% 1.29/1.45           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))))
% 1.29/1.45         <= ((![X34 : $i, X35 : $i]:
% 1.29/1.45                (~ (l1_pre_topc @ X34)
% 1.29/1.45                 | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))))),
% 1.29/1.45      inference('split', [status(esa)], ['27'])).
% 1.29/1.45  thf('29', plain,
% 1.29/1.45      ((~ (l1_pre_topc @ sk_A))
% 1.29/1.45         <= ((![X34 : $i, X35 : $i]:
% 1.29/1.45                (~ (l1_pre_topc @ X34)
% 1.29/1.45                 | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))))),
% 1.29/1.45      inference('sup-', [status(thm)], ['26', '28'])).
% 1.29/1.45  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('31', plain,
% 1.29/1.45      (~
% 1.29/1.45       (![X34 : $i, X35 : $i]:
% 1.29/1.45          (~ (l1_pre_topc @ X34)
% 1.29/1.45           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))))),
% 1.29/1.45      inference('demod', [status(thm)], ['29', '30'])).
% 1.29/1.45  thf('32', plain,
% 1.29/1.45      ((![X36 : $i, X37 : $i]:
% 1.29/1.45          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.29/1.45           | ~ (l1_pre_topc @ X37)
% 1.29/1.45           | ~ (v2_pre_topc @ X37)
% 1.29/1.45           | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.29/1.45           | (v3_pre_topc @ X36 @ X37))) | 
% 1.29/1.45       (![X34 : $i, X35 : $i]:
% 1.29/1.45          (~ (l1_pre_topc @ X34)
% 1.29/1.45           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))))),
% 1.29/1.45      inference('split', [status(esa)], ['27'])).
% 1.29/1.45  thf('33', plain,
% 1.29/1.45      ((![X36 : $i, X37 : $i]:
% 1.29/1.45          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.29/1.45           | ~ (l1_pre_topc @ X37)
% 1.29/1.45           | ~ (v2_pre_topc @ X37)
% 1.29/1.45           | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.29/1.45           | (v3_pre_topc @ X36 @ X37)))),
% 1.29/1.45      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 1.29/1.45  thf('34', plain,
% 1.29/1.45      (![X36 : $i, X37 : $i]:
% 1.29/1.45         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.29/1.45          | ~ (l1_pre_topc @ X37)
% 1.29/1.45          | ~ (v2_pre_topc @ X37)
% 1.29/1.45          | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.29/1.45          | (v3_pre_topc @ X36 @ X37))),
% 1.29/1.45      inference('simpl_trail', [status(thm)], ['25', '33'])).
% 1.29/1.45  thf('35', plain,
% 1.29/1.45      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.29/1.45        | ((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.29/1.45            != (k1_tops_1 @ sk_A @ sk_B))
% 1.29/1.45        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.45        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.45      inference('sup-', [status(thm)], ['23', '34'])).
% 1.29/1.45  thf('36', plain,
% 1.29/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf(projectivity_k1_tops_1, axiom,
% 1.29/1.45    (![A:$i,B:$i]:
% 1.29/1.45     ( ( ( l1_pre_topc @ A ) & 
% 1.29/1.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.29/1.45       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 1.29/1.45  thf('37', plain,
% 1.29/1.45      (![X26 : $i, X27 : $i]:
% 1.29/1.45         (~ (l1_pre_topc @ X26)
% 1.29/1.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.29/1.45          | ((k1_tops_1 @ X26 @ (k1_tops_1 @ X26 @ X27))
% 1.29/1.45              = (k1_tops_1 @ X26 @ X27)))),
% 1.29/1.45      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 1.29/1.45  thf('38', plain,
% 1.29/1.45      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.29/1.45          = (k1_tops_1 @ sk_A @ sk_B))
% 1.29/1.45        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.45      inference('sup-', [status(thm)], ['36', '37'])).
% 1.29/1.45  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('40', plain,
% 1.29/1.45      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.29/1.45         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.29/1.45      inference('demod', [status(thm)], ['38', '39'])).
% 1.29/1.45  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('43', plain,
% 1.29/1.45      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.29/1.45        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_tops_1 @ sk_A @ sk_B)))),
% 1.29/1.45      inference('demod', [status(thm)], ['35', '40', '41', '42'])).
% 1.29/1.45  thf('44', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.29/1.45      inference('simplify', [status(thm)], ['43'])).
% 1.29/1.45  thf('45', plain,
% 1.29/1.45      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.29/1.45         <= ((![X40 : $i]:
% 1.29/1.45                (((X40) = (k1_xboole_0))
% 1.29/1.45                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45                 | ~ (r1_tarski @ X40 @ sk_B))))),
% 1.29/1.45      inference('demod', [status(thm)], ['22', '44'])).
% 1.29/1.45  thf('46', plain,
% 1.29/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf(t84_tops_1, axiom,
% 1.29/1.45    (![A:$i]:
% 1.29/1.45     ( ( l1_pre_topc @ A ) =>
% 1.29/1.45       ( ![B:$i]:
% 1.29/1.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.45           ( ( v2_tops_1 @ B @ A ) <=>
% 1.29/1.45             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.29/1.45  thf('47', plain,
% 1.29/1.45      (![X38 : $i, X39 : $i]:
% 1.29/1.45         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.29/1.45          | ((k1_tops_1 @ X39 @ X38) != (k1_xboole_0))
% 1.29/1.45          | (v2_tops_1 @ X38 @ X39)
% 1.29/1.45          | ~ (l1_pre_topc @ X39))),
% 1.29/1.45      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.29/1.45  thf('48', plain,
% 1.29/1.45      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.45        | (v2_tops_1 @ sk_B @ sk_A)
% 1.29/1.45        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.29/1.45      inference('sup-', [status(thm)], ['46', '47'])).
% 1.29/1.45  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('50', plain,
% 1.29/1.45      (((v2_tops_1 @ sk_B @ sk_A)
% 1.29/1.45        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.29/1.45      inference('demod', [status(thm)], ['48', '49'])).
% 1.29/1.45  thf('51', plain,
% 1.29/1.45      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 1.29/1.45         <= ((![X40 : $i]:
% 1.29/1.45                (((X40) = (k1_xboole_0))
% 1.29/1.45                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45                 | ~ (r1_tarski @ X40 @ sk_B))))),
% 1.29/1.45      inference('sup-', [status(thm)], ['45', '50'])).
% 1.29/1.45  thf('52', plain,
% 1.29/1.45      (((v2_tops_1 @ sk_B @ sk_A))
% 1.29/1.45         <= ((![X40 : $i]:
% 1.29/1.45                (((X40) = (k1_xboole_0))
% 1.29/1.45                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45                 | ~ (r1_tarski @ X40 @ sk_B))))),
% 1.29/1.45      inference('simplify', [status(thm)], ['51'])).
% 1.29/1.45  thf('53', plain,
% 1.29/1.45      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('54', plain,
% 1.29/1.45      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.29/1.45      inference('split', [status(esa)], ['53'])).
% 1.29/1.45  thf('55', plain,
% 1.29/1.45      (~
% 1.29/1.45       (![X40 : $i]:
% 1.29/1.45          (((X40) = (k1_xboole_0))
% 1.29/1.45           | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45           | ~ (v3_pre_topc @ X40 @ sk_A)
% 1.29/1.45           | ~ (r1_tarski @ X40 @ sk_B))) | 
% 1.29/1.45       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('sup-', [status(thm)], ['52', '54'])).
% 1.29/1.45  thf('56', plain,
% 1.29/1.45      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.29/1.45       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('split', [status(esa)], ['1'])).
% 1.29/1.45  thf('57', plain,
% 1.29/1.45      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.29/1.45      inference('sat_resolution*', [status(thm)], ['4', '55', '56'])).
% 1.29/1.45  thf('58', plain,
% 1.29/1.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('simpl_trail', [status(thm)], ['2', '57'])).
% 1.29/1.45  thf('59', plain,
% 1.29/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf(t54_tops_1, axiom,
% 1.29/1.45    (![A:$i]:
% 1.29/1.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.45       ( ![B:$i,C:$i]:
% 1.29/1.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.45           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 1.29/1.45             ( ?[D:$i]:
% 1.29/1.45               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 1.29/1.45                 ( v3_pre_topc @ D @ A ) & 
% 1.29/1.45                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.29/1.45  thf('60', plain,
% 1.29/1.45      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.29/1.45         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.29/1.45          | ~ (r2_hidden @ X32 @ X33)
% 1.29/1.45          | ~ (r1_tarski @ X33 @ X30)
% 1.29/1.45          | ~ (v3_pre_topc @ X33 @ X31)
% 1.29/1.45          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.29/1.45          | (r2_hidden @ X32 @ (k1_tops_1 @ X31 @ X30))
% 1.29/1.45          | ~ (l1_pre_topc @ X31)
% 1.29/1.45          | ~ (v2_pre_topc @ X31))),
% 1.29/1.45      inference('cnf', [status(esa)], [t54_tops_1])).
% 1.29/1.45  thf('61', plain,
% 1.29/1.45      (![X0 : $i, X1 : $i]:
% 1.29/1.45         (~ (v2_pre_topc @ sk_A)
% 1.29/1.45          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.45          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 1.29/1.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45          | ~ (v3_pre_topc @ X1 @ sk_A)
% 1.29/1.45          | ~ (r1_tarski @ X1 @ sk_B)
% 1.29/1.45          | ~ (r2_hidden @ X0 @ X1))),
% 1.29/1.45      inference('sup-', [status(thm)], ['59', '60'])).
% 1.29/1.45  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('64', plain,
% 1.29/1.45      (![X0 : $i, X1 : $i]:
% 1.29/1.45         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 1.29/1.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45          | ~ (v3_pre_topc @ X1 @ sk_A)
% 1.29/1.45          | ~ (r1_tarski @ X1 @ sk_B)
% 1.29/1.45          | ~ (r2_hidden @ X0 @ X1))),
% 1.29/1.45      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.29/1.45  thf('65', plain,
% 1.29/1.45      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.29/1.45      inference('split', [status(esa)], ['3'])).
% 1.29/1.45  thf('66', plain,
% 1.29/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('67', plain,
% 1.29/1.45      (![X38 : $i, X39 : $i]:
% 1.29/1.45         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.29/1.45          | ~ (v2_tops_1 @ X38 @ X39)
% 1.29/1.45          | ((k1_tops_1 @ X39 @ X38) = (k1_xboole_0))
% 1.29/1.45          | ~ (l1_pre_topc @ X39))),
% 1.29/1.45      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.29/1.45  thf('68', plain,
% 1.29/1.45      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.45        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.29/1.45        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('sup-', [status(thm)], ['66', '67'])).
% 1.29/1.45  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('70', plain,
% 1.29/1.45      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.29/1.45        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('demod', [status(thm)], ['68', '69'])).
% 1.29/1.45  thf('71', plain,
% 1.29/1.45      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.29/1.45         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.29/1.45      inference('sup-', [status(thm)], ['65', '70'])).
% 1.29/1.45  thf('72', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('sat_resolution*', [status(thm)], ['4', '55'])).
% 1.29/1.45  thf('73', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.29/1.45      inference('simpl_trail', [status(thm)], ['71', '72'])).
% 1.29/1.45  thf('74', plain,
% 1.29/1.45      (![X0 : $i, X1 : $i]:
% 1.29/1.45         ((r2_hidden @ X0 @ k1_xboole_0)
% 1.29/1.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.45          | ~ (v3_pre_topc @ X1 @ sk_A)
% 1.29/1.45          | ~ (r1_tarski @ X1 @ sk_B)
% 1.29/1.45          | ~ (r2_hidden @ X0 @ X1))),
% 1.29/1.45      inference('demod', [status(thm)], ['64', '73'])).
% 1.29/1.45  thf('75', plain,
% 1.29/1.45      (![X0 : $i]:
% 1.29/1.45         (~ (r2_hidden @ X0 @ sk_C_1)
% 1.29/1.45          | ~ (r1_tarski @ sk_C_1 @ sk_B)
% 1.29/1.45          | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 1.29/1.45          | (r2_hidden @ X0 @ k1_xboole_0))),
% 1.29/1.45      inference('sup-', [status(thm)], ['58', '74'])).
% 1.29/1.45  thf('76', plain,
% 1.29/1.45      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 1.29/1.45      inference('split', [status(esa)], ['53'])).
% 1.29/1.45  thf('77', plain,
% 1.29/1.45      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('split', [status(esa)], ['53'])).
% 1.29/1.45  thf('78', plain, (((r1_tarski @ sk_C_1 @ sk_B))),
% 1.29/1.45      inference('sat_resolution*', [status(thm)], ['4', '55', '77'])).
% 1.29/1.45  thf('79', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 1.29/1.45      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 1.29/1.45  thf('80', plain,
% 1.29/1.45      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('81', plain,
% 1.29/1.45      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 1.29/1.45      inference('split', [status(esa)], ['80'])).
% 1.29/1.45  thf('82', plain,
% 1.29/1.45      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('split', [status(esa)], ['80'])).
% 1.29/1.45  thf('83', plain, (((v3_pre_topc @ sk_C_1 @ sk_A))),
% 1.29/1.45      inference('sat_resolution*', [status(thm)], ['4', '55', '82'])).
% 1.29/1.45  thf('84', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 1.29/1.45      inference('simpl_trail', [status(thm)], ['81', '83'])).
% 1.29/1.45  thf('85', plain,
% 1.29/1.45      (![X0 : $i]:
% 1.29/1.45         (~ (r2_hidden @ X0 @ sk_C_1) | (r2_hidden @ X0 @ k1_xboole_0))),
% 1.29/1.45      inference('demod', [status(thm)], ['75', '79', '84'])).
% 1.29/1.45  thf('86', plain,
% 1.29/1.45      (![X0 : $i]:
% 1.29/1.45         ((r1_tarski @ sk_C_1 @ X0)
% 1.29/1.45          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ k1_xboole_0))),
% 1.29/1.45      inference('sup-', [status(thm)], ['0', '85'])).
% 1.29/1.45  thf('87', plain,
% 1.29/1.45      (![X1 : $i, X3 : $i]:
% 1.29/1.45         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.29/1.45      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.45  thf('88', plain,
% 1.29/1.45      (((r1_tarski @ sk_C_1 @ k1_xboole_0) | (r1_tarski @ sk_C_1 @ k1_xboole_0))),
% 1.29/1.45      inference('sup-', [status(thm)], ['86', '87'])).
% 1.29/1.45  thf('89', plain, ((r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 1.29/1.45      inference('simplify', [status(thm)], ['88'])).
% 1.29/1.45  thf(t3_xboole_1, axiom,
% 1.29/1.45    (![A:$i]:
% 1.29/1.45     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.29/1.45  thf('90', plain,
% 1.29/1.45      (![X13 : $i]:
% 1.29/1.45         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 1.29/1.45      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.29/1.45  thf('91', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.29/1.45      inference('sup-', [status(thm)], ['89', '90'])).
% 1.29/1.45  thf('92', plain,
% 1.29/1.45      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.45  thf('93', plain,
% 1.29/1.45      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.29/1.45      inference('split', [status(esa)], ['92'])).
% 1.29/1.45  thf('94', plain,
% 1.29/1.45      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.29/1.45      inference('split', [status(esa)], ['92'])).
% 1.29/1.45  thf('95', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 1.29/1.45      inference('sat_resolution*', [status(thm)], ['4', '55', '94'])).
% 1.29/1.45  thf('96', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.29/1.45      inference('simpl_trail', [status(thm)], ['93', '95'])).
% 1.29/1.45  thf('97', plain, ($false),
% 1.29/1.45      inference('simplify_reflect-', [status(thm)], ['91', '96'])).
% 1.29/1.45  
% 1.29/1.45  % SZS output end Refutation
% 1.29/1.45  
% 1.30/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
