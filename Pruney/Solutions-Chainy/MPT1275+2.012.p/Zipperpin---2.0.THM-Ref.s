%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pdh0JGJeyr

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:34 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 308 expanded)
%              Number of leaves         :   42 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          : 1203 (3034 expanded)
%              Number of equality atoms :   66 ( 170 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t94_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( ( v3_tops_1 @ B @ A )
              <=> ( B
                  = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_tops_1 @ X36 @ X35 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k2_pre_topc @ X36 @ X35 ) @ ( k2_pre_topc @ X36 @ ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 ) ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = X33 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4','10'])).

thf('12',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('16',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
        = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('24',plain,(
    ! [X32: $i] :
      ( ( l1_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('39',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v1_tops_1 @ X37 @ X38 )
      | ( ( k2_pre_topc @ X38 @ X37 )
        = ( k2_struct_0 @ X38 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('49',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 ) @ X42 )
      | ~ ( v3_tops_1 @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r1_tarski @ X39 @ ( k2_tops_1 @ X40 @ X39 ) )
      | ( v2_tops_1 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('64',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t93_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v2_tops_1 @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('66',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v3_tops_1 @ X43 @ X44 )
      | ~ ( v4_pre_topc @ X43 @ X44 )
      | ~ ( v2_tops_1 @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t93_tops_1])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('73',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('75',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['55','73','74'])).

thf('76',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['53','75'])).

thf('77',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','76'])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','39','80'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','81'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('83',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X15 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('84',plain,(
    ! [X14: $i] :
      ( ( k2_subset_1 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('85',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('89',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('90',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('92',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( m1_subset_1 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('95',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('103',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','105'])).

thf('107',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('108',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('111',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['88','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('114',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('116',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['82','87','114','115'])).

thf('117',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['54'])).

thf('118',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['55','73'])).

thf('119',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['116','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pdh0JGJeyr
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:39:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 503 iterations in 0.428s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.89  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.68/0.89  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.68/0.89  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.68/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.89  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.68/0.89  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.68/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.89  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.68/0.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.68/0.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.89  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.68/0.89  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.68/0.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.68/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.89  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.68/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.89  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(d3_struct_0, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.68/0.89  thf('0', plain,
% 0.68/0.89      (![X31 : $i]:
% 0.68/0.89         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.89  thf(t94_tops_1, conjecture,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( v4_pre_topc @ B @ A ) =>
% 0.68/0.89             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.89    (~( ![A:$i]:
% 0.68/0.89        ( ( l1_pre_topc @ A ) =>
% 0.68/0.89          ( ![B:$i]:
% 0.68/0.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89              ( ( v4_pre_topc @ B @ A ) =>
% 0.68/0.89                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.68/0.89  thf('1', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(d2_tops_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( k2_tops_1 @ A @ B ) =
% 0.68/0.89             ( k9_subset_1 @
% 0.68/0.89               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.68/0.89               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.68/0.89  thf('2', plain,
% 0.68/0.89      (![X35 : $i, X36 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.68/0.89          | ((k2_tops_1 @ X36 @ X35)
% 0.68/0.89              = (k9_subset_1 @ (u1_struct_0 @ X36) @ 
% 0.68/0.89                 (k2_pre_topc @ X36 @ X35) @ 
% 0.68/0.89                 (k2_pre_topc @ X36 @ (k3_subset_1 @ (u1_struct_0 @ X36) @ X35))))
% 0.68/0.89          | ~ (l1_pre_topc @ X36))),
% 0.68/0.89      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.68/0.89  thf('3', plain,
% 0.68/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.89               (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.68/0.89               (k2_pre_topc @ sk_A @ 
% 0.68/0.89                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.89  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('5', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t52_pre_topc, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.68/0.89             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.68/0.89               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.68/0.89  thf('6', plain,
% 0.68/0.89      (![X33 : $i, X34 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.68/0.89          | ~ (v4_pre_topc @ X33 @ X34)
% 0.68/0.89          | ((k2_pre_topc @ X34 @ X33) = (X33))
% 0.68/0.89          | ~ (l1_pre_topc @ X34))),
% 0.68/0.89      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.68/0.89  thf('7', plain,
% 0.68/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.68/0.89        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.68/0.89      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.89  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('9', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('10', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.68/0.89      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.68/0.89  thf('11', plain,
% 0.68/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.68/0.89            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.68/0.89      inference('demod', [status(thm)], ['3', '4', '10'])).
% 0.68/0.89  thf('12', plain,
% 0.68/0.89      (![X31 : $i]:
% 0.68/0.89         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.89  thf('13', plain,
% 0.68/0.89      (![X31 : $i]:
% 0.68/0.89         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(dt_k3_subset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.89       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      (![X16 : $i, X17 : $i]:
% 0.68/0.89         ((m1_subset_1 @ (k3_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.68/0.89          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.89  thf(redefinition_k9_subset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.89       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.68/0.89  thf('17', plain,
% 0.68/0.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.89         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 0.68/0.89          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.68/0.89      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.68/0.89  thf('18', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.68/0.89           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['16', '17'])).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.68/0.89            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89            = (k3_xboole_0 @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.68/0.89          | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['13', '18'])).
% 0.68/0.89  thf('20', plain,
% 0.68/0.89      (![X31 : $i]:
% 0.68/0.89         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.89  thf('22', plain,
% 0.68/0.89      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.89        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.89  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(dt_l1_pre_topc, axiom,
% 0.68/0.89    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.68/0.89  thf('24', plain,
% 0.68/0.89      (![X32 : $i]: ((l1_struct_0 @ X32) | ~ (l1_pre_topc @ X32))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.68/0.89  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.89  thf('26', plain,
% 0.68/0.89      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('demod', [status(thm)], ['22', '25'])).
% 0.68/0.89  thf('27', plain,
% 0.68/0.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.89         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 0.68/0.89          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.68/0.89      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.68/0.89  thf('28', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.68/0.89           (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['26', '27'])).
% 0.68/0.89  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.89  thf('30', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k3_xboole_0 @ X0 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.68/0.89      inference('demod', [status(thm)], ['19', '28', '29'])).
% 0.68/0.89  thf(d10_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.89  thf('31', plain,
% 0.68/0.89      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.89  thf('32', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.68/0.89      inference('simplify', [status(thm)], ['31'])).
% 0.68/0.89  thf(t28_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.89  thf('33', plain,
% 0.68/0.89      (![X7 : $i, X8 : $i]:
% 0.68/0.89         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.68/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.89  thf('34', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.68/0.89  thf('35', plain,
% 0.68/0.89      (((k3_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.89         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.89      inference('sup+', [status(thm)], ['30', '34'])).
% 0.68/0.89  thf('36', plain,
% 0.68/0.89      ((((k3_xboole_0 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.89          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['12', '35'])).
% 0.68/0.89  thf('37', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.68/0.89  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.89  thf('39', plain,
% 0.68/0.89      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.68/0.89         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.68/0.89      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.68/0.89  thf('40', plain,
% 0.68/0.89      (![X31 : $i]:
% 0.68/0.89         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.89  thf('41', plain,
% 0.68/0.89      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.68/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.89  thf(d3_tops_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( v1_tops_1 @ B @ A ) <=>
% 0.68/0.89             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.68/0.89  thf('42', plain,
% 0.68/0.89      (![X37 : $i, X38 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.68/0.89          | ~ (v1_tops_1 @ X37 @ X38)
% 0.68/0.89          | ((k2_pre_topc @ X38 @ X37) = (k2_struct_0 @ X38))
% 0.68/0.89          | ~ (l1_pre_topc @ X38))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.68/0.89  thf('43', plain,
% 0.68/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89            = (k2_struct_0 @ sk_A))
% 0.68/0.89        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.68/0.89      inference('sup-', [status(thm)], ['41', '42'])).
% 0.68/0.89  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('45', plain,
% 0.68/0.89      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89          = (k2_struct_0 @ sk_A))
% 0.68/0.89        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.68/0.89      inference('demod', [status(thm)], ['43', '44'])).
% 0.68/0.89  thf('46', plain,
% 0.68/0.89      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('47', plain,
% 0.68/0.89      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.89      inference('split', [status(esa)], ['46'])).
% 0.68/0.89  thf('48', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t91_tops_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( v3_tops_1 @ B @ A ) =>
% 0.68/0.89             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.68/0.89  thf('49', plain,
% 0.68/0.89      (![X41 : $i, X42 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.68/0.89          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X42) @ X41) @ X42)
% 0.68/0.89          | ~ (v3_tops_1 @ X41 @ X42)
% 0.68/0.89          | ~ (l1_pre_topc @ X42))),
% 0.68/0.89      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.68/0.89  thf('50', plain,
% 0.68/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.68/0.89        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.68/0.89      inference('sup-', [status(thm)], ['48', '49'])).
% 0.68/0.89  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('52', plain,
% 0.68/0.89      ((~ (v3_tops_1 @ sk_B @ sk_A)
% 0.68/0.89        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.68/0.89      inference('demod', [status(thm)], ['50', '51'])).
% 0.68/0.89  thf('53', plain,
% 0.68/0.89      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.68/0.89         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['47', '52'])).
% 0.68/0.89  thf('54', plain,
% 0.68/0.89      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('55', plain,
% 0.68/0.89      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.68/0.89      inference('split', [status(esa)], ['54'])).
% 0.68/0.89  thf('56', plain,
% 0.68/0.89      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.68/0.89         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('split', [status(esa)], ['46'])).
% 0.68/0.89  thf('57', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t88_tops_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( v2_tops_1 @ B @ A ) <=>
% 0.68/0.89             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.68/0.89  thf('58', plain,
% 0.68/0.89      (![X39 : $i, X40 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.68/0.89          | ~ (r1_tarski @ X39 @ (k2_tops_1 @ X40 @ X39))
% 0.68/0.89          | (v2_tops_1 @ X39 @ X40)
% 0.68/0.89          | ~ (l1_pre_topc @ X40))),
% 0.68/0.89      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.68/0.89  thf('59', plain,
% 0.68/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | (v2_tops_1 @ sk_B @ sk_A)
% 0.68/0.89        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['57', '58'])).
% 0.68/0.89  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('61', plain,
% 0.68/0.89      (((v2_tops_1 @ sk_B @ sk_A)
% 0.68/0.89        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('demod', [status(thm)], ['59', '60'])).
% 0.68/0.89  thf('62', plain,
% 0.68/0.89      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.68/0.89         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['56', '61'])).
% 0.68/0.89  thf('63', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.68/0.89      inference('simplify', [status(thm)], ['31'])).
% 0.68/0.89  thf('64', plain,
% 0.68/0.89      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('demod', [status(thm)], ['62', '63'])).
% 0.68/0.89  thf('65', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t93_tops_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_pre_topc @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ( ( v2_tops_1 @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.68/0.89             ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.68/0.89  thf('66', plain,
% 0.68/0.89      (![X43 : $i, X44 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.68/0.89          | (v3_tops_1 @ X43 @ X44)
% 0.68/0.89          | ~ (v4_pre_topc @ X43 @ X44)
% 0.68/0.89          | ~ (v2_tops_1 @ X43 @ X44)
% 0.68/0.89          | ~ (l1_pre_topc @ X44))),
% 0.68/0.89      inference('cnf', [status(esa)], [t93_tops_1])).
% 0.68/0.89  thf('67', plain,
% 0.68/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | ~ (v2_tops_1 @ sk_B @ sk_A)
% 0.68/0.89        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.68/0.89        | (v3_tops_1 @ sk_B @ sk_A))),
% 0.68/0.89      inference('sup-', [status(thm)], ['65', '66'])).
% 0.68/0.89  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('69', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('70', plain, ((~ (v2_tops_1 @ sk_B @ sk_A) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.68/0.89      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.68/0.89  thf('71', plain,
% 0.68/0.89      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['64', '70'])).
% 0.68/0.89  thf('72', plain,
% 0.68/0.89      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.68/0.89      inference('split', [status(esa)], ['54'])).
% 0.68/0.89  thf('73', plain,
% 0.68/0.89      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['71', '72'])).
% 0.68/0.89  thf('74', plain,
% 0.68/0.89      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('split', [status(esa)], ['46'])).
% 0.68/0.89  thf('75', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.68/0.89      inference('sat_resolution*', [status(thm)], ['55', '73', '74'])).
% 0.68/0.89  thf('76', plain,
% 0.68/0.89      ((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.68/0.89      inference('simpl_trail', [status(thm)], ['53', '75'])).
% 0.68/0.89  thf('77', plain,
% 0.68/0.89      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89         = (k2_struct_0 @ sk_A))),
% 0.68/0.89      inference('demod', [status(thm)], ['45', '76'])).
% 0.68/0.89  thf('78', plain,
% 0.68/0.89      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89          = (k2_struct_0 @ sk_A))
% 0.68/0.89        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['40', '77'])).
% 0.68/0.89  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.89  thf('80', plain,
% 0.68/0.89      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.68/0.89         = (k2_struct_0 @ sk_A))),
% 0.68/0.89      inference('demod', [status(thm)], ['78', '79'])).
% 0.68/0.89  thf('81', plain,
% 0.68/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_struct_0 @ sk_A)))),
% 0.68/0.89      inference('demod', [status(thm)], ['11', '39', '80'])).
% 0.68/0.89  thf('82', plain,
% 0.68/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.68/0.89          = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ (k2_struct_0 @ sk_A)))
% 0.68/0.89        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['0', '81'])).
% 0.68/0.89  thf(dt_k2_subset_1, axiom,
% 0.68/0.89    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.68/0.89  thf('83', plain,
% 0.68/0.89      (![X15 : $i]: (m1_subset_1 @ (k2_subset_1 @ X15) @ (k1_zfmisc_1 @ X15))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.68/0.89  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.68/0.89  thf('84', plain, (![X14 : $i]: ((k2_subset_1 @ X14) = (X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.68/0.89  thf('85', plain, (![X15 : $i]: (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))),
% 0.68/0.89      inference('demod', [status(thm)], ['83', '84'])).
% 0.68/0.89  thf('86', plain,
% 0.68/0.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.89         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 0.68/0.89          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.68/0.89      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.68/0.89  thf('87', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['85', '86'])).
% 0.68/0.89  thf('88', plain,
% 0.68/0.89      (![X31 : $i]:
% 0.68/0.89         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.89  thf(d3_tarski, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.89  thf('89', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('90', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('91', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t4_subset, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.68/0.89       ( m1_subset_1 @ A @ C ) ))).
% 0.68/0.89  thf('92', plain,
% 0.68/0.89      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X25 @ X26)
% 0.68/0.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.68/0.89          | (m1_subset_1 @ X25 @ X27))),
% 0.68/0.89      inference('cnf', [status(esa)], [t4_subset])).
% 0.68/0.89  thf('93', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.68/0.89      inference('sup-', [status(thm)], ['91', '92'])).
% 0.68/0.89  thf('94', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r1_tarski @ sk_B @ X0)
% 0.68/0.89          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['90', '93'])).
% 0.68/0.89  thf(t2_subset, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ A @ B ) =>
% 0.68/0.89       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.68/0.89  thf('95', plain,
% 0.68/0.89      (![X23 : $i, X24 : $i]:
% 0.68/0.89         ((r2_hidden @ X23 @ X24)
% 0.68/0.89          | (v1_xboole_0 @ X24)
% 0.68/0.89          | ~ (m1_subset_1 @ X23 @ X24))),
% 0.68/0.89      inference('cnf', [status(esa)], [t2_subset])).
% 0.68/0.89  thf('96', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r1_tarski @ sk_B @ X0)
% 0.68/0.89          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.89          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['94', '95'])).
% 0.68/0.89  thf('97', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('98', plain,
% 0.68/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.89        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.68/0.89        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['96', '97'])).
% 0.68/0.89  thf('99', plain,
% 0.68/0.89      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.68/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['98'])).
% 0.68/0.89  thf('100', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.89          | (r2_hidden @ X0 @ X2)
% 0.68/0.89          | ~ (r1_tarski @ X1 @ X2))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('101', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.89          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.89          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.68/0.89      inference('sup-', [status(thm)], ['99', '100'])).
% 0.68/0.89  thf('102', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t5_subset, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.68/0.89          ( v1_xboole_0 @ C ) ) ))).
% 0.68/0.89  thf('103', plain,
% 0.68/0.89      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X28 @ X29)
% 0.68/0.89          | ~ (v1_xboole_0 @ X30)
% 0.68/0.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t5_subset])).
% 0.68/0.89  thf('104', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.68/0.89      inference('sup-', [status(thm)], ['102', '103'])).
% 0.68/0.89  thf('105', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('clc', [status(thm)], ['101', '104'])).
% 0.68/0.89  thf('106', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r1_tarski @ sk_B @ X0)
% 0.68/0.89          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['89', '105'])).
% 0.68/0.89  thf('107', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('108', plain,
% 0.68/0.89      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.68/0.89        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['106', '107'])).
% 0.68/0.89  thf('109', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.89      inference('simplify', [status(thm)], ['108'])).
% 0.68/0.89  thf('110', plain,
% 0.68/0.89      (![X7 : $i, X8 : $i]:
% 0.68/0.89         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.68/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.89  thf('111', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.68/0.89      inference('sup-', [status(thm)], ['109', '110'])).
% 0.68/0.89  thf('112', plain,
% 0.68/0.89      ((((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (sk_B))
% 0.68/0.89        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['88', '111'])).
% 0.68/0.89  thf('113', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.89  thf('114', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 0.68/0.89      inference('demod', [status(thm)], ['112', '113'])).
% 0.68/0.89  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.89  thf('116', plain, (((k2_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.68/0.89      inference('demod', [status(thm)], ['82', '87', '114', '115'])).
% 0.68/0.89  thf('117', plain,
% 0.68/0.89      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.68/0.89         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.68/0.89      inference('split', [status(esa)], ['54'])).
% 0.68/0.89  thf('118', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.68/0.89      inference('sat_resolution*', [status(thm)], ['55', '73'])).
% 0.68/0.89  thf('119', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.68/0.89      inference('simpl_trail', [status(thm)], ['117', '118'])).
% 0.68/0.89  thf('120', plain, ($false),
% 0.68/0.89      inference('simplify_reflect-', [status(thm)], ['116', '119'])).
% 0.68/0.89  
% 0.68/0.89  % SZS output end Refutation
% 0.68/0.89  
% 0.68/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
