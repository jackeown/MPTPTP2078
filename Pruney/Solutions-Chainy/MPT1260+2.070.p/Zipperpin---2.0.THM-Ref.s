%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vBrxwR40c9

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:34 EST 2020

% Result     : Theorem 2.53s
% Output     : Refutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 697 expanded)
%              Number of leaves         :   32 ( 222 expanded)
%              Depth                    :   21
%              Number of atoms          : 2053 (7937 expanded)
%              Number of equality atoms :  131 ( 428 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X34 @ X35 )
      | ~ ( r1_tarski @ X34 @ X36 )
      | ( r1_tarski @ X34 @ ( k1_tops_1 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ X26 @ ( k2_pre_topc @ X27 @ X26 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('45',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('55',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('56',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('61',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('67',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('73',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('74',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('77',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('84',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('87',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k7_subset_1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k7_subset_1 @ X1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k7_subset_1 @ X1 @ X1 @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('97',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k7_subset_1 @ X1 @ X1 @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k7_subset_1 @ X1 @ X1 @ X0 ) )
      = ( k7_subset_1 @ X1 @ X1 @ ( k3_subset_1 @ X1 @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['89','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k7_subset_1 @ X1 @ X1 @ X0 ) )
      = ( k7_subset_1 @ X1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','105','106'])).

thf('108',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      = ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('110',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('112',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('114',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('115',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('117',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('118',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','119'])).

thf('121',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) )
        = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['79','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('125',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('126',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('127',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['124','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      | ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        = ( k4_xboole_0 @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','138','139'])).

thf('141',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['71','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('143',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('145',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k1_tops_1 @ X38 @ X37 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 @ ( k2_tops_1 @ X38 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('146',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147','150'])).

thf('152',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['143','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('154',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('155',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['152','158'])).

thf('160',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('161',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','53','54','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vBrxwR40c9
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:41:36 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 2.53/2.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.53/2.74  % Solved by: fo/fo7.sh
% 2.53/2.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.53/2.74  % done 4617 iterations in 2.289s
% 2.53/2.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.53/2.74  % SZS output start Refutation
% 2.53/2.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.53/2.74  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.53/2.74  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.53/2.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.53/2.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.53/2.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.53/2.74  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.53/2.74  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.53/2.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.53/2.74  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.53/2.74  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.53/2.74  thf(sk_A_type, type, sk_A: $i).
% 2.53/2.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.53/2.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.53/2.74  thf(sk_B_type, type, sk_B: $i).
% 2.53/2.74  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.53/2.74  thf(t76_tops_1, conjecture,
% 2.53/2.74    (![A:$i]:
% 2.53/2.74     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.53/2.74       ( ![B:$i]:
% 2.53/2.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.74           ( ( v3_pre_topc @ B @ A ) <=>
% 2.53/2.74             ( ( k2_tops_1 @ A @ B ) =
% 2.53/2.74               ( k7_subset_1 @
% 2.53/2.74                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 2.53/2.74  thf(zf_stmt_0, negated_conjecture,
% 2.53/2.74    (~( ![A:$i]:
% 2.53/2.74        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.53/2.74          ( ![B:$i]:
% 2.53/2.74            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.74              ( ( v3_pre_topc @ B @ A ) <=>
% 2.53/2.74                ( ( k2_tops_1 @ A @ B ) =
% 2.53/2.74                  ( k7_subset_1 @
% 2.53/2.74                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 2.53/2.74    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 2.53/2.74  thf('0', plain,
% 2.53/2.74      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.74          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 2.53/2.75        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('1', plain,
% 2.53/2.75      (~
% 2.53/2.75       (((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.53/2.75       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 2.53/2.75      inference('split', [status(esa)], ['0'])).
% 2.53/2.75  thf('2', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('3', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 2.53/2.75        | (v3_pre_topc @ sk_B @ sk_A))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('4', plain,
% 2.53/2.75      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.53/2.75      inference('split', [status(esa)], ['3'])).
% 2.53/2.75  thf('5', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf(t56_tops_1, axiom,
% 2.53/2.75    (![A:$i]:
% 2.53/2.75     ( ( l1_pre_topc @ A ) =>
% 2.53/2.75       ( ![B:$i]:
% 2.53/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.75           ( ![C:$i]:
% 2.53/2.75             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.75               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 2.53/2.75                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.53/2.75  thf('6', plain,
% 2.53/2.75      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.53/2.75         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.53/2.75          | ~ (v3_pre_topc @ X34 @ X35)
% 2.53/2.75          | ~ (r1_tarski @ X34 @ X36)
% 2.53/2.75          | (r1_tarski @ X34 @ (k1_tops_1 @ X35 @ X36))
% 2.53/2.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.53/2.75          | ~ (l1_pre_topc @ X35))),
% 2.53/2.75      inference('cnf', [status(esa)], [t56_tops_1])).
% 2.53/2.75  thf('7', plain,
% 2.53/2.75      (![X0 : $i]:
% 2.53/2.75         (~ (l1_pre_topc @ sk_A)
% 2.53/2.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.53/2.75          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 2.53/2.75          | ~ (r1_tarski @ sk_B @ X0)
% 2.53/2.75          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.53/2.75      inference('sup-', [status(thm)], ['5', '6'])).
% 2.53/2.75  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('9', plain,
% 2.53/2.75      (![X0 : $i]:
% 2.53/2.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.53/2.75          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 2.53/2.75          | ~ (r1_tarski @ sk_B @ X0)
% 2.53/2.75          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.53/2.75      inference('demod', [status(thm)], ['7', '8'])).
% 2.53/2.75  thf('10', plain,
% 2.53/2.75      ((![X0 : $i]:
% 2.53/2.75          (~ (r1_tarski @ sk_B @ X0)
% 2.53/2.75           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 2.53/2.75           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 2.53/2.75         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['4', '9'])).
% 2.53/2.75  thf('11', plain,
% 2.53/2.75      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.53/2.75         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['2', '10'])).
% 2.53/2.75  thf(d10_xboole_0, axiom,
% 2.53/2.75    (![A:$i,B:$i]:
% 2.53/2.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.53/2.75  thf('12', plain,
% 2.53/2.75      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 2.53/2.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.53/2.75  thf('13', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 2.53/2.75      inference('simplify', [status(thm)], ['12'])).
% 2.53/2.75  thf('14', plain,
% 2.53/2.75      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.53/2.75         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.53/2.75      inference('demod', [status(thm)], ['11', '13'])).
% 2.53/2.75  thf('15', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf(t44_tops_1, axiom,
% 2.53/2.75    (![A:$i]:
% 2.53/2.75     ( ( l1_pre_topc @ A ) =>
% 2.53/2.75       ( ![B:$i]:
% 2.53/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.75           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 2.53/2.75  thf('16', plain,
% 2.53/2.75      (![X32 : $i, X33 : $i]:
% 2.53/2.75         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 2.53/2.75          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 2.53/2.75          | ~ (l1_pre_topc @ X33))),
% 2.53/2.75      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.53/2.75  thf('17', plain,
% 2.53/2.75      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.53/2.75      inference('sup-', [status(thm)], ['15', '16'])).
% 2.53/2.75  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 2.53/2.75      inference('demod', [status(thm)], ['17', '18'])).
% 2.53/2.75  thf('20', plain,
% 2.53/2.75      (![X1 : $i, X3 : $i]:
% 2.53/2.75         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 2.53/2.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.53/2.75  thf('21', plain,
% 2.53/2.75      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.53/2.75        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['19', '20'])).
% 2.53/2.75  thf('22', plain,
% 2.53/2.75      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 2.53/2.75         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['14', '21'])).
% 2.53/2.75  thf('23', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf(l78_tops_1, axiom,
% 2.53/2.75    (![A:$i]:
% 2.53/2.75     ( ( l1_pre_topc @ A ) =>
% 2.53/2.75       ( ![B:$i]:
% 2.53/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.75           ( ( k2_tops_1 @ A @ B ) =
% 2.53/2.75             ( k7_subset_1 @
% 2.53/2.75               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.53/2.75               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.53/2.75  thf('24', plain,
% 2.53/2.75      (![X30 : $i, X31 : $i]:
% 2.53/2.75         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 2.53/2.75          | ((k2_tops_1 @ X31 @ X30)
% 2.53/2.75              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 2.53/2.75                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 2.53/2.75          | ~ (l1_pre_topc @ X31))),
% 2.53/2.75      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.53/2.75  thf('25', plain,
% 2.53/2.75      ((~ (l1_pre_topc @ sk_A)
% 2.53/2.75        | ((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.53/2.75      inference('sup-', [status(thm)], ['23', '24'])).
% 2.53/2.75  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('27', plain,
% 2.53/2.75      (((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.75      inference('demod', [status(thm)], ['25', '26'])).
% 2.53/2.75  thf('28', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf(dt_k2_pre_topc, axiom,
% 2.53/2.75    (![A:$i,B:$i]:
% 2.53/2.75     ( ( ( l1_pre_topc @ A ) & 
% 2.53/2.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.53/2.75       ( m1_subset_1 @
% 2.53/2.75         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.53/2.75  thf('29', plain,
% 2.53/2.75      (![X24 : $i, X25 : $i]:
% 2.53/2.75         (~ (l1_pre_topc @ X24)
% 2.53/2.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.53/2.75          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 2.53/2.75             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 2.53/2.75      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.53/2.75  thf('30', plain,
% 2.53/2.75      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.53/2.75        | ~ (l1_pre_topc @ sk_A))),
% 2.53/2.75      inference('sup-', [status(thm)], ['28', '29'])).
% 2.53/2.75  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('32', plain,
% 2.53/2.75      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('demod', [status(thm)], ['30', '31'])).
% 2.53/2.75  thf(redefinition_k7_subset_1, axiom,
% 2.53/2.75    (![A:$i,B:$i,C:$i]:
% 2.53/2.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.53/2.75       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.53/2.75  thf('33', plain,
% 2.53/2.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.53/2.75         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.53/2.75          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 2.53/2.75      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.53/2.75  thf('34', plain,
% 2.53/2.75      (![X0 : $i]:
% 2.53/2.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['32', '33'])).
% 2.53/2.75  thf('35', plain,
% 2.53/2.75      (((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.75      inference('demod', [status(thm)], ['27', '34'])).
% 2.53/2.75  thf('36', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.53/2.75         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.53/2.75      inference('sup+', [status(thm)], ['22', '35'])).
% 2.53/2.75  thf('37', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf(t48_pre_topc, axiom,
% 2.53/2.75    (![A:$i]:
% 2.53/2.75     ( ( l1_pre_topc @ A ) =>
% 2.53/2.75       ( ![B:$i]:
% 2.53/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.75           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 2.53/2.75  thf('38', plain,
% 2.53/2.75      (![X26 : $i, X27 : $i]:
% 2.53/2.75         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 2.53/2.75          | (r1_tarski @ X26 @ (k2_pre_topc @ X27 @ X26))
% 2.53/2.75          | ~ (l1_pre_topc @ X27))),
% 2.53/2.75      inference('cnf', [status(esa)], [t48_pre_topc])).
% 2.53/2.75  thf('39', plain,
% 2.53/2.75      ((~ (l1_pre_topc @ sk_A)
% 2.53/2.75        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['37', '38'])).
% 2.53/2.75  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('41', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 2.53/2.75      inference('demod', [status(thm)], ['39', '40'])).
% 2.53/2.75  thf(t3_subset, axiom,
% 2.53/2.75    (![A:$i,B:$i]:
% 2.53/2.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.53/2.75  thf('42', plain,
% 2.53/2.75      (![X21 : $i, X23 : $i]:
% 2.53/2.75         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 2.53/2.75      inference('cnf', [status(esa)], [t3_subset])).
% 2.53/2.75  thf('43', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['41', '42'])).
% 2.53/2.75  thf(d5_subset_1, axiom,
% 2.53/2.75    (![A:$i,B:$i]:
% 2.53/2.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.53/2.75       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.53/2.75  thf('44', plain,
% 2.53/2.75      (![X12 : $i, X13 : $i]:
% 2.53/2.75         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 2.53/2.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 2.53/2.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.53/2.75  thf('45', plain,
% 2.53/2.75      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 2.53/2.75         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 2.53/2.75      inference('sup-', [status(thm)], ['43', '44'])).
% 2.53/2.75  thf('46', plain,
% 2.53/2.75      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 2.53/2.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 2.53/2.75         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.53/2.75      inference('sup+', [status(thm)], ['36', '45'])).
% 2.53/2.75  thf('47', plain,
% 2.53/2.75      (![X0 : $i]:
% 2.53/2.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['32', '33'])).
% 2.53/2.75  thf('48', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.53/2.75         <= (~
% 2.53/2.75             (((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('split', [status(esa)], ['0'])).
% 2.53/2.75  thf('49', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.53/2.75         <= (~
% 2.53/2.75             (((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup-', [status(thm)], ['47', '48'])).
% 2.53/2.75  thf('50', plain,
% 2.53/2.75      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 2.53/2.75         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 2.53/2.75      inference('sup-', [status(thm)], ['43', '44'])).
% 2.53/2.75  thf('51', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          != (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.53/2.75         <= (~
% 2.53/2.75             (((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('demod', [status(thm)], ['49', '50'])).
% 2.53/2.75  thf('52', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 2.53/2.75         <= (~
% 2.53/2.75             (((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 2.53/2.75             ((v3_pre_topc @ sk_B @ sk_A)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['46', '51'])).
% 2.53/2.75  thf('53', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.53/2.75       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 2.53/2.75      inference('simplify', [status(thm)], ['52'])).
% 2.53/2.75  thf('54', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.53/2.75       ((v3_pre_topc @ sk_B @ sk_A))),
% 2.53/2.75      inference('split', [status(esa)], ['3'])).
% 2.53/2.75  thf('55', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 2.53/2.75      inference('simplify', [status(thm)], ['12'])).
% 2.53/2.75  thf('56', plain,
% 2.53/2.75      (![X21 : $i, X23 : $i]:
% 2.53/2.75         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 2.53/2.75      inference('cnf', [status(esa)], [t3_subset])).
% 2.53/2.75  thf('57', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['55', '56'])).
% 2.53/2.75  thf('58', plain,
% 2.53/2.75      (![X12 : $i, X13 : $i]:
% 2.53/2.75         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 2.53/2.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 2.53/2.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.53/2.75  thf('59', plain,
% 2.53/2.75      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['57', '58'])).
% 2.53/2.75  thf(t36_xboole_1, axiom,
% 2.53/2.75    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.53/2.75  thf('60', plain,
% 2.53/2.75      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 2.53/2.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.53/2.75  thf('61', plain,
% 2.53/2.75      (![X21 : $i, X23 : $i]:
% 2.53/2.75         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 2.53/2.75      inference('cnf', [status(esa)], [t3_subset])).
% 2.53/2.75  thf('62', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['60', '61'])).
% 2.53/2.75  thf('63', plain,
% 2.53/2.75      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 2.53/2.75      inference('sup+', [status(thm)], ['59', '62'])).
% 2.53/2.75  thf('64', plain,
% 2.53/2.75      (![X12 : $i, X13 : $i]:
% 2.53/2.75         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 2.53/2.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 2.53/2.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.53/2.75  thf('65', plain,
% 2.53/2.75      (![X0 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0))
% 2.53/2.75           = (k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['63', '64'])).
% 2.53/2.75  thf('66', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['55', '56'])).
% 2.53/2.75  thf(involutiveness_k3_subset_1, axiom,
% 2.53/2.75    (![A:$i,B:$i]:
% 2.53/2.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.53/2.75       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.53/2.75  thf('67', plain,
% 2.53/2.75      (![X16 : $i, X17 : $i]:
% 2.53/2.75         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 2.53/2.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.53/2.75      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.53/2.75  thf('68', plain,
% 2.53/2.75      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['66', '67'])).
% 2.53/2.75  thf('69', plain,
% 2.53/2.75      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 2.53/2.75      inference('demod', [status(thm)], ['65', '68'])).
% 2.53/2.75  thf(t41_xboole_1, axiom,
% 2.53/2.75    (![A:$i,B:$i,C:$i]:
% 2.53/2.75     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.53/2.75       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.53/2.75  thf('70', plain,
% 2.53/2.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.53/2.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.53/2.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.53/2.75  thf('71', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ X0 @ X1)
% 2.53/2.75           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k3_subset_1 @ X0 @ X0) @ X1)))),
% 2.53/2.75      inference('sup+', [status(thm)], ['69', '70'])).
% 2.53/2.75  thf(idempotence_k2_xboole_0, axiom,
% 2.53/2.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.53/2.75  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.53/2.75      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.53/2.75  thf('73', plain,
% 2.53/2.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.53/2.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.53/2.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.53/2.75  thf('74', plain,
% 2.53/2.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.53/2.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.53/2.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.53/2.75  thf('75', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 2.53/2.75           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 2.53/2.75      inference('sup+', [status(thm)], ['73', '74'])).
% 2.53/2.75  thf('76', plain,
% 2.53/2.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.53/2.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.53/2.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.53/2.75  thf('77', plain,
% 2.53/2.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.53/2.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.53/2.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.53/2.75  thf('78', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 2.53/2.75           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 2.53/2.75      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.53/2.75  thf('79', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.53/2.75           = (k4_xboole_0 @ X2 @ 
% 2.53/2.75              (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['72', '78'])).
% 2.53/2.75  thf('80', plain,
% 2.53/2.75      (![X0 : $i]:
% 2.53/2.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['32', '33'])).
% 2.53/2.75  thf('81', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('split', [status(esa)], ['3'])).
% 2.53/2.75  thf('82', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['80', '81'])).
% 2.53/2.75  thf('83', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['55', '56'])).
% 2.53/2.75  thf('84', plain,
% 2.53/2.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.53/2.75         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.53/2.75          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 2.53/2.75      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.53/2.75  thf('85', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.53/2.75      inference('sup-', [status(thm)], ['83', '84'])).
% 2.53/2.75  thf('86', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['60', '61'])).
% 2.53/2.75  thf('87', plain,
% 2.53/2.75      (![X12 : $i, X13 : $i]:
% 2.53/2.75         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 2.53/2.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 2.53/2.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.53/2.75  thf('88', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.53/2.75           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['86', '87'])).
% 2.53/2.75  thf('89', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 2.53/2.75           = (k4_xboole_0 @ X1 @ (k7_subset_1 @ X1 @ X1 @ X0)))),
% 2.53/2.75      inference('sup+', [status(thm)], ['85', '88'])).
% 2.53/2.75  thf('90', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.53/2.75           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['86', '87'])).
% 2.53/2.75  thf('91', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.53/2.75      inference('sup-', [status(thm)], ['83', '84'])).
% 2.53/2.75  thf('92', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.53/2.75           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['86', '87'])).
% 2.53/2.75  thf('93', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 2.53/2.75           = (k7_subset_1 @ X1 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.53/2.75      inference('sup+', [status(thm)], ['91', '92'])).
% 2.53/2.75  thf('94', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 2.53/2.75           = (k7_subset_1 @ X1 @ X1 @ 
% 2.53/2.75              (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['90', '93'])).
% 2.53/2.75  thf('95', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.53/2.75           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['86', '87'])).
% 2.53/2.75  thf('96', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['60', '61'])).
% 2.53/2.75  thf('97', plain,
% 2.53/2.75      (![X16 : $i, X17 : $i]:
% 2.53/2.75         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 2.53/2.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.53/2.75      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.53/2.75  thf('98', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 2.53/2.75           = (k4_xboole_0 @ X0 @ X1))),
% 2.53/2.75      inference('sup-', [status(thm)], ['96', '97'])).
% 2.53/2.75  thf('99', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ X1 @ X0)
% 2.53/2.75           = (k7_subset_1 @ X1 @ X1 @ 
% 2.53/2.75              (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 2.53/2.75      inference('demod', [status(thm)], ['94', '95', '98'])).
% 2.53/2.75  thf('100', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ X1 @ (k7_subset_1 @ X1 @ X1 @ X0))
% 2.53/2.75           = (k7_subset_1 @ X1 @ X1 @ 
% 2.53/2.75              (k3_subset_1 @ X1 @ (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['89', '99'])).
% 2.53/2.75  thf('101', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.53/2.75      inference('sup-', [status(thm)], ['83', '84'])).
% 2.53/2.75  thf('102', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['60', '61'])).
% 2.53/2.75  thf('103', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         (m1_subset_1 @ (k7_subset_1 @ X1 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 2.53/2.75      inference('sup+', [status(thm)], ['101', '102'])).
% 2.53/2.75  thf('104', plain,
% 2.53/2.75      (![X12 : $i, X13 : $i]:
% 2.53/2.75         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 2.53/2.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 2.53/2.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.53/2.75  thf('105', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1))
% 2.53/2.75           = (k4_xboole_0 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['103', '104'])).
% 2.53/2.75  thf('106', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 2.53/2.75           = (k4_xboole_0 @ X0 @ X1))),
% 2.53/2.75      inference('sup-', [status(thm)], ['96', '97'])).
% 2.53/2.75  thf('107', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k3_subset_1 @ X1 @ (k7_subset_1 @ X1 @ X1 @ X0))
% 2.53/2.75           = (k7_subset_1 @ X1 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.53/2.75      inference('demod', [status(thm)], ['100', '105', '106'])).
% 2.53/2.75  thf('108', plain,
% 2.53/2.75      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75          (k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75           (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 2.53/2.75          = (k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75             (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['82', '107'])).
% 2.53/2.75  thf('109', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.53/2.75      inference('sup-', [status(thm)], ['83', '84'])).
% 2.53/2.75  thf('110', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['80', '81'])).
% 2.53/2.75  thf('111', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i]:
% 2.53/2.75         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.53/2.75      inference('sup-', [status(thm)], ['83', '84'])).
% 2.53/2.75  thf('112', plain,
% 2.53/2.75      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 2.53/2.75          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75             (k2_tops_1 @ sk_A @ sk_B))))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 2.53/2.75  thf('113', plain,
% 2.53/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['80', '81'])).
% 2.53/2.75  thf('114', plain,
% 2.53/2.75      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 2.53/2.75         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 2.53/2.75      inference('sup-', [status(thm)], ['43', '44'])).
% 2.53/2.75  thf('115', plain,
% 2.53/2.75      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 2.53/2.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['113', '114'])).
% 2.53/2.75  thf('116', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.53/2.75      inference('sup-', [status(thm)], ['41', '42'])).
% 2.53/2.75  thf('117', plain,
% 2.53/2.75      (![X16 : $i, X17 : $i]:
% 2.53/2.75         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 2.53/2.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.53/2.75      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.53/2.75  thf('118', plain,
% 2.53/2.75      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 2.53/2.75      inference('sup-', [status(thm)], ['116', '117'])).
% 2.53/2.75  thf('119', plain,
% 2.53/2.75      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 2.53/2.75          = (sk_B)))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['115', '118'])).
% 2.53/2.75  thf('120', plain,
% 2.53/2.75      ((((sk_B)
% 2.53/2.75          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75             (k2_tops_1 @ sk_A @ sk_B))))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('demod', [status(thm)], ['112', '119'])).
% 2.53/2.75  thf('121', plain,
% 2.53/2.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.53/2.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.53/2.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.53/2.75  thf('122', plain,
% 2.53/2.75      ((![X0 : $i]:
% 2.53/2.75          ((k4_xboole_0 @ sk_B @ X0)
% 2.53/2.75            = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75               (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['120', '121'])).
% 2.53/2.75  thf('123', plain,
% 2.53/2.75      ((![X0 : $i]:
% 2.53/2.75          ((k4_xboole_0 @ sk_B @ 
% 2.53/2.75            (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0)))
% 2.53/2.75            = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75               (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['79', '122'])).
% 2.53/2.75  thf('124', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.53/2.75      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.53/2.75  thf('125', plain,
% 2.53/2.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.53/2.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.53/2.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.53/2.75  thf('126', plain,
% 2.53/2.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.53/2.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.53/2.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.53/2.75  thf('127', plain,
% 2.53/2.75      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 2.53/2.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.53/2.75  thf('128', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.75         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 2.53/2.75          (k4_xboole_0 @ X2 @ X1))),
% 2.53/2.75      inference('sup+', [status(thm)], ['126', '127'])).
% 2.53/2.75  thf('129', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.53/2.75         (r1_tarski @ 
% 2.53/2.75          (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 2.53/2.75          (k4_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1))),
% 2.53/2.75      inference('sup+', [status(thm)], ['125', '128'])).
% 2.53/2.75  thf('130', plain,
% 2.53/2.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.53/2.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.53/2.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.53/2.75  thf('131', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.53/2.75         (r1_tarski @ 
% 2.53/2.75          (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 2.53/2.75          (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ X1)))),
% 2.53/2.75      inference('demod', [status(thm)], ['129', '130'])).
% 2.53/2.75  thf('132', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.75         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 2.53/2.75          (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 2.53/2.75      inference('sup+', [status(thm)], ['124', '131'])).
% 2.53/2.75  thf('133', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 2.53/2.75           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 2.53/2.75      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.53/2.75  thf('134', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.75         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 2.53/2.75          (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 2.53/2.75      inference('demod', [status(thm)], ['132', '133'])).
% 2.53/2.75  thf('135', plain,
% 2.53/2.75      (![X1 : $i, X3 : $i]:
% 2.53/2.75         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 2.53/2.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.53/2.75  thf('136', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.75         (~ (r1_tarski @ 
% 2.53/2.75             (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 2.53/2.75             (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))
% 2.53/2.75          | ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 2.53/2.75              = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))))),
% 2.53/2.75      inference('sup-', [status(thm)], ['134', '135'])).
% 2.53/2.75  thf('137', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.53/2.75         (r1_tarski @ 
% 2.53/2.75          (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 2.53/2.75          (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ X1)))),
% 2.53/2.75      inference('demod', [status(thm)], ['129', '130'])).
% 2.53/2.75  thf('138', plain,
% 2.53/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.75         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 2.53/2.75           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 2.53/2.75      inference('demod', [status(thm)], ['136', '137'])).
% 2.53/2.75  thf('139', plain,
% 2.53/2.75      ((![X0 : $i]:
% 2.53/2.75          ((k4_xboole_0 @ sk_B @ X0)
% 2.53/2.75            = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.53/2.75               (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['120', '121'])).
% 2.53/2.75  thf('140', plain,
% 2.53/2.75      ((![X0 : $i]:
% 2.53/2.75          ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.53/2.75            = (k4_xboole_0 @ sk_B @ X0)))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('demod', [status(thm)], ['123', '138', '139'])).
% 2.53/2.75  thf('141', plain,
% 2.53/2.75      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.53/2.75          = (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ sk_B))))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['71', '140'])).
% 2.53/2.75  thf('142', plain,
% 2.53/2.75      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 2.53/2.75      inference('demod', [status(thm)], ['65', '68'])).
% 2.53/2.75  thf('143', plain,
% 2.53/2.75      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('demod', [status(thm)], ['141', '142'])).
% 2.53/2.75  thf('144', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf(t74_tops_1, axiom,
% 2.53/2.75    (![A:$i]:
% 2.53/2.75     ( ( l1_pre_topc @ A ) =>
% 2.53/2.75       ( ![B:$i]:
% 2.53/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.75           ( ( k1_tops_1 @ A @ B ) =
% 2.53/2.75             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.53/2.75  thf('145', plain,
% 2.53/2.75      (![X37 : $i, X38 : $i]:
% 2.53/2.75         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 2.53/2.75          | ((k1_tops_1 @ X38 @ X37)
% 2.53/2.75              = (k7_subset_1 @ (u1_struct_0 @ X38) @ X37 @ 
% 2.53/2.75                 (k2_tops_1 @ X38 @ X37)))
% 2.53/2.75          | ~ (l1_pre_topc @ X38))),
% 2.53/2.75      inference('cnf', [status(esa)], [t74_tops_1])).
% 2.53/2.75  thf('146', plain,
% 2.53/2.75      ((~ (l1_pre_topc @ sk_A)
% 2.53/2.75        | ((k1_tops_1 @ sk_A @ sk_B)
% 2.53/2.75            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.53/2.75               (k2_tops_1 @ sk_A @ sk_B))))),
% 2.53/2.75      inference('sup-', [status(thm)], ['144', '145'])).
% 2.53/2.75  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('148', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('149', plain,
% 2.53/2.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.53/2.75         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.53/2.75          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 2.53/2.75      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.53/2.75  thf('150', plain,
% 2.53/2.75      (![X0 : $i]:
% 2.53/2.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.53/2.75           = (k4_xboole_0 @ sk_B @ X0))),
% 2.53/2.75      inference('sup-', [status(thm)], ['148', '149'])).
% 2.53/2.75  thf('151', plain,
% 2.53/2.75      (((k1_tops_1 @ sk_A @ sk_B)
% 2.53/2.75         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.75      inference('demod', [status(thm)], ['146', '147', '150'])).
% 2.53/2.75  thf('152', plain,
% 2.53/2.75      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['143', '151'])).
% 2.53/2.75  thf('153', plain,
% 2.53/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf(fc9_tops_1, axiom,
% 2.53/2.75    (![A:$i,B:$i]:
% 2.53/2.75     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.53/2.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.53/2.75       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 2.53/2.75  thf('154', plain,
% 2.53/2.75      (![X28 : $i, X29 : $i]:
% 2.53/2.75         (~ (l1_pre_topc @ X28)
% 2.53/2.75          | ~ (v2_pre_topc @ X28)
% 2.53/2.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 2.53/2.75          | (v3_pre_topc @ (k1_tops_1 @ X28 @ X29) @ X28))),
% 2.53/2.75      inference('cnf', [status(esa)], [fc9_tops_1])).
% 2.53/2.75  thf('155', plain,
% 2.53/2.75      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 2.53/2.75        | ~ (v2_pre_topc @ sk_A)
% 2.53/2.75        | ~ (l1_pre_topc @ sk_A))),
% 2.53/2.75      inference('sup-', [status(thm)], ['153', '154'])).
% 2.53/2.75  thf('156', plain, ((v2_pre_topc @ sk_A)),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.75  thf('158', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 2.53/2.75      inference('demod', [status(thm)], ['155', '156', '157'])).
% 2.53/2.75  thf('159', plain,
% 2.53/2.75      (((v3_pre_topc @ sk_B @ sk_A))
% 2.53/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.53/2.75      inference('sup+', [status(thm)], ['152', '158'])).
% 2.53/2.75  thf('160', plain,
% 2.53/2.75      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 2.53/2.75      inference('split', [status(esa)], ['0'])).
% 2.53/2.75  thf('161', plain,
% 2.53/2.75      (~
% 2.53/2.75       (((k2_tops_1 @ sk_A @ sk_B)
% 2.53/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.75             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.53/2.75       ((v3_pre_topc @ sk_B @ sk_A))),
% 2.53/2.75      inference('sup-', [status(thm)], ['159', '160'])).
% 2.53/2.75  thf('162', plain, ($false),
% 2.53/2.75      inference('sat_resolution*', [status(thm)], ['1', '53', '54', '161'])).
% 2.53/2.75  
% 2.53/2.75  % SZS output end Refutation
% 2.53/2.75  
% 2.53/2.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
