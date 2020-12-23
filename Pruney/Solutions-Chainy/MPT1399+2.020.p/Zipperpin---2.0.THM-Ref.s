%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pd0r7Hc6eF

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:05 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 201 expanded)
%              Number of leaves         :   29 (  69 expanded)
%              Depth                    :   25
%              Number of atoms          :  773 (2134 expanded)
%              Number of equality atoms :   13 (  65 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X60: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X60 ) @ X60 )
      | ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('7',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('8',plain,(
    ! [X59: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X59 ) @ X59 )
      | ~ ( l1_pre_topc @ X59 )
      | ~ ( v2_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('9',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X37 )
      | ( X37
       != ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r2_hidden @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( m1_subset_1 @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X61: $i] :
      ( ~ ( v3_pre_topc @ X61 @ sk_A )
      | ~ ( v4_pre_topc @ X61 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X61 )
      | ( r2_hidden @ X61 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X57: $i] :
      ( ( l1_struct_0 @ X57 )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('30',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('39',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ~ ( r1_tarski @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X6: $i] :
      ( r1_tarski @ sk_C_1 @ X6 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('48',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( m1_subset_1 @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('53',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_xboole_0 @ X42 )
      | ( m1_subset_1 @ X42 @ X41 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('54',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( m1_subset_1 @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( m1_subset_1 @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['58'])).

thf('60',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( m1_subset_1 @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X42 @ X41 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('72',plain,(
    ! [X58: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X58 ) )
      | ~ ( l1_struct_0 @ X58 )
      | ( v2_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('77',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pd0r7Hc6eF
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 316 iterations in 0.189s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.64  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.64  thf(t28_connsp_2, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( m1_subset_1 @
% 0.45/0.64                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64               ( ~( ( ![D:$i]:
% 0.45/0.64                      ( ( m1_subset_1 @
% 0.45/0.64                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64                        ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.64                          ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.64                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.64                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.64            ( l1_pre_topc @ A ) ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.64              ( ![C:$i]:
% 0.45/0.64                ( ( m1_subset_1 @
% 0.45/0.64                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64                  ( ~( ( ![D:$i]:
% 0.45/0.64                         ( ( m1_subset_1 @
% 0.45/0.64                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64                           ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.64                             ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.64                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.64                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.45/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(d3_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X56 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X56 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(d2_subset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.64         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.64       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.64         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X40 : $i, X41 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X40 @ X41)
% 0.45/0.64          | (r2_hidden @ X40 @ X41)
% 0.45/0.64          | (v1_xboole_0 @ X41))),
% 0.45/0.64      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf(fc10_tops_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X60 : $i]:
% 0.45/0.64         ((v3_pre_topc @ (k2_struct_0 @ X60) @ X60)
% 0.45/0.64          | ~ (l1_pre_topc @ X60)
% 0.45/0.64          | ~ (v2_pre_topc @ X60))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X56 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf(fc4_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X59 : $i]:
% 0.45/0.64         ((v4_pre_topc @ (k2_struct_0 @ X59) @ X59)
% 0.45/0.64          | ~ (l1_pre_topc @ X59)
% 0.45/0.64          | ~ (v2_pre_topc @ X59))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X56 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf(d10_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.64  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.64      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.64  thf(d1_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.45/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X35 @ X36)
% 0.45/0.64          | (r2_hidden @ X35 @ X37)
% 0.45/0.64          | ((X37) != (k1_zfmisc_1 @ X36)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X35 : $i, X36 : $i]:
% 0.45/0.64         ((r2_hidden @ X35 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X35 @ X36))),
% 0.45/0.64      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.64  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '13'])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X40 : $i, X41 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X40 @ X41)
% 0.45/0.64          | (m1_subset_1 @ X40 @ X41)
% 0.45/0.64          | (v1_xboole_0 @ X41))),
% 0.45/0.64      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X61 : $i]:
% 0.45/0.64         (~ (v3_pre_topc @ X61 @ sk_A)
% 0.45/0.64          | ~ (v4_pre_topc @ X61 @ sk_A)
% 0.45/0.64          | ~ (r2_hidden @ sk_B @ X61)
% 0.45/0.64          | (r2_hidden @ X61 @ sk_C_1)
% 0.45/0.64          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['9', '18'])).
% 0.45/0.64  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(dt_l1_pre_topc, axiom,
% 0.45/0.64    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X57 : $i]: ((l1_struct_0 @ X57) | ~ (l1_pre_topc @ X57))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.64  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.64      inference('demod', [status(thm)], ['19', '22'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['8', '23'])).
% 0.45/0.64  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '27'])).
% 0.45/0.64  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.64      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['6', '30'])).
% 0.45/0.64  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['5', '34'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['2', '35'])).
% 0.45/0.64  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.64  thf(t7_ordinal1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X54 : $i, X55 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X54 @ X55) | ~ (r1_tarski @ X55 @ X54))),
% 0.45/0.64      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.64        | ~ (r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.64  thf('41', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('42', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('43', plain, (![X6 : $i]: (r1_tarski @ sk_C_1 @ X6)),
% 0.45/0.64      inference('demod', [status(thm)], ['41', '42'])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.45/0.64      inference('demod', [status(thm)], ['40', '43'])).
% 0.45/0.64  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '13'])).
% 0.45/0.64  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '13'])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf(t4_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.64       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X51 @ X52)
% 0.45/0.64          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 0.45/0.64          | (m1_subset_1 @ X51 @ X53))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (m1_subset_1 @ X1 @ X0)
% 0.45/0.64          | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '49'])).
% 0.45/0.64  thf('51', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '13'])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '49'])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (![X41 : $i, X42 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ X42)
% 0.45/0.64          | (m1_subset_1 @ X42 @ X41)
% 0.45/0.64          | ~ (v1_xboole_0 @ X41))),
% 0.45/0.64      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X51 @ X52)
% 0.45/0.64          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 0.45/0.64          | (m1_subset_1 @ X51 @ X53))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.64  thf('55', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | ~ (v1_xboole_0 @ X1)
% 0.45/0.64          | (m1_subset_1 @ X2 @ X0)
% 0.45/0.64          | ~ (r2_hidden @ X2 @ X1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('56', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | ~ (r2_hidden @ X2 @ X1)
% 0.45/0.64          | (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | ~ (v1_xboole_0 @ X1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['52', '55'])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['51', '56'])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | (m1_subset_1 @ (k1_zfmisc_1 @ X0) @ (k1_zfmisc_1 @ X1)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '57'])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (k1_zfmisc_1 @ X0) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.45/0.65          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.65      inference('eq_fact', [status(thm)], ['58'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X51 @ X52)
% 0.45/0.65          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 0.45/0.65          | (m1_subset_1 @ X51 @ X53))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.65          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.65          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.65          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['45', '61'])).
% 0.45/0.65  thf('63', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['62'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      (![X41 : $i, X42 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X42 @ X41)
% 0.45/0.65          | (v1_xboole_0 @ X42)
% 0.45/0.65          | ~ (v1_xboole_0 @ X41))),
% 0.45/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (![X0 : $i]: (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['63', '64'])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['44', '65'])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.65        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['1', '66'])).
% 0.45/0.65  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.45/0.65        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.65  thf('70', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.45/0.65      inference('simplify', [status(thm)], ['69'])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      (![X56 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf(fc2_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.65  thf('72', plain,
% 0.45/0.65      (![X58 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X58))
% 0.45/0.65          | ~ (l1_struct_0 @ X58)
% 0.45/0.65          | (v2_struct_0 @ X58))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.65          | ~ (l1_struct_0 @ X0)
% 0.45/0.65          | (v2_struct_0 @ X0)
% 0.45/0.65          | ~ (l1_struct_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.65  thf('74', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ X0)
% 0.45/0.65          | ~ (l1_struct_0 @ X0)
% 0.45/0.65          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['73'])).
% 0.45/0.65  thf('75', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['70', '74'])).
% 0.45/0.65  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('77', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['75', '76'])).
% 0.45/0.65  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
