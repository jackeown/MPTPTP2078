%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d8u1iMCH6I

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 222 expanded)
%              Number of leaves         :   42 (  82 expanded)
%              Depth                    :   22
%              Number of atoms          :  798 (3001 expanded)
%              Number of equality atoms :   39 ( 117 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('3',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t50_subset_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( r2_hidden @ X39 @ X37 )
      | ( r2_hidden @ X39 @ ( k3_subset_1 @ X38 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ X38 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('6',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( r2_hidden @ X39 @ X37 )
      | ( r2_hidden @ X39 @ ( k3_subset_1 @ X38 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ X38 )
      | ( X38 = sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ sk_C ) )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = ( k5_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ sk_C )
      = X4 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C )
      = X0 ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('26',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( v4_pre_topc @ X49 @ X50 )
      | ~ ( v1_xboole_0 @ X49 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ sk_C )
      | ( v4_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('33',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( v4_pre_topc @ X55 @ X56 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 ) @ X56 )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_C ) @ X0 )
      | ~ ( v4_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C )
      = X0 ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('39',plain,(
    ! [X53: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X53 ) @ X53 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('40',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X35 ) @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('42',plain,(
    ! [X32: $i] :
      ( ( k2_subset_1 @ X32 )
      = X32 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('43',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X57: $i] :
      ( ~ ( v3_pre_topc @ X57 @ sk_A )
      | ~ ( v4_pre_topc @ X57 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X57 )
      | ( r2_hidden @ X57 @ sk_C )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('48',plain,(
    ! [X52: $i] :
      ( ( l1_struct_0 @ X52 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['24','58'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('60',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r1_tarski @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('61',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('62',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_C @ X3 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r1_tarski @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('67',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_C @ X3 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['67','68'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('70',plain,(
    ! [X54: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X54 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 )
      | ( v2_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('71',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X40 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_xboole_0 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X54: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X54 ) )
      | ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 )
      | ( v2_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['0','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d8u1iMCH6I
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 162 iterations in 0.069s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(t28_connsp_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @
% 0.20/0.52                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52               ( ~( ( ![D:$i]:
% 0.20/0.52                      ( ( m1_subset_1 @
% 0.20/0.52                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                        ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52                          ( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.52                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.20/0.52                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( m1_subset_1 @
% 0.20/0.52                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52                  ( ~( ( ![D:$i]:
% 0.20/0.52                         ( ( m1_subset_1 @
% 0.20/0.52                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                           ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52                             ( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.52                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.20/0.52                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.20/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t4_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.52  thf('3', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain, (![X36 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X36))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(t50_subset_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.52               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.20/0.52                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.20/0.52          | (r2_hidden @ X39 @ X37)
% 0.20/0.52          | (r2_hidden @ X39 @ (k3_subset_1 @ X38 @ X37))
% 0.20/0.52          | ~ (m1_subset_1 @ X39 @ X38)
% 0.20/0.52          | ((X38) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.20/0.52  thf('6', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.20/0.52          | (r2_hidden @ X39 @ X37)
% 0.20/0.52          | (r2_hidden @ X39 @ (k3_subset_1 @ X38 @ X37))
% 0.20/0.52          | ~ (m1_subset_1 @ X39 @ X38)
% 0.20/0.52          | ((X38) = (sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (sk_C))
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ sk_C))
% 0.20/0.52          | (r2_hidden @ X1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.52  thf('9', plain, (![X36 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X36))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(d5_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X33 : $i, X34 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.20/0.52          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf(t2_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.52  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ sk_C) = (sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (k5_xboole_0 @ X0 @ sk_C))),
% 0.20/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf(t5_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('18', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.52  thf('19', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ sk_C) = (X4))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.52  thf('22', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (sk_C))
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | (r2_hidden @ X1 @ X0)
% 0.20/0.52          | (r2_hidden @ X1 @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((r2_hidden @ sk_B_1 @ sk_C)
% 0.20/0.52        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '23'])).
% 0.20/0.52  thf('25', plain, (![X36 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X36))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(cc2_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X49 : $i, X50 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.20/0.52          | (v4_pre_topc @ X49 @ X50)
% 0.20/0.52          | ~ (v1_xboole_0 @ X49)
% 0.20/0.52          | ~ (l1_pre_topc @ X50)
% 0.20/0.52          | ~ (v2_pre_topc @ X50))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ sk_C)
% 0.20/0.52          | (v4_pre_topc @ sk_C @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.52  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.52  thf('29', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v4_pre_topc @ sk_C @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '30'])).
% 0.20/0.52  thf('32', plain, (![X36 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X36))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(t29_tops_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.52             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X55 : $i, X56 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.20/0.52          | ~ (v4_pre_topc @ X55 @ X56)
% 0.20/0.52          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X56) @ X55) @ X56)
% 0.20/0.52          | ~ (l1_pre_topc @ X56))),
% 0.20/0.52      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ sk_C) @ X0)
% 0.20/0.52          | ~ (v4_pre_topc @ sk_C @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '21'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.52          | ~ (v4_pre_topc @ sk_C @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.52  thf(fc4_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X53 : $i]:
% 0.20/0.52         ((v4_pre_topc @ (k2_struct_0 @ X53) @ X53)
% 0.20/0.52          | ~ (l1_pre_topc @ X53)
% 0.20/0.52          | ~ (v2_pre_topc @ X53))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.20/0.52  thf(d3_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X51 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf(dt_k2_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X35 : $i]: (m1_subset_1 @ (k2_subset_1 @ X35) @ (k1_zfmisc_1 @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.52  thf('42', plain, (![X32 : $i]: ((k2_subset_1 @ X32) = (X32))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.52  thf('43', plain, (![X35 : $i]: (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X35))),
% 0.20/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X57 : $i]:
% 0.20/0.52         (~ (v3_pre_topc @ X57 @ sk_A)
% 0.20/0.52          | ~ (v4_pre_topc @ X57 @ sk_A)
% 0.20/0.52          | ~ (r2_hidden @ sk_B_1 @ X57)
% 0.20/0.52          | (r2_hidden @ X57 @ sk_C)
% 0.20/0.52          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.52        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '45'])).
% 0.20/0.52  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_l1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X52 : $i]: ((l1_struct_0 @ X52) | ~ (l1_pre_topc @ X52))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.52  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['46', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '50'])).
% 0.20/0.52  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '54'])).
% 0.20/0.52  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      ((((u1_struct_0 @ sk_A) = (sk_C))
% 0.20/0.52        | (r2_hidden @ sk_B_1 @ sk_C)
% 0.20/0.52        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '58'])).
% 0.20/0.52  thf(t7_ordinal1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X47 : $i, X48 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X47 @ X48) | ~ (r1_tarski @ X48 @ X47))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (((r2_hidden @ sk_B_1 @ sk_C)
% 0.20/0.52        | ((u1_struct_0 @ sk_A) = (sk_C))
% 0.20/0.52        | ~ (r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('62', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('63', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('64', plain, (![X3 : $i]: (r1_tarski @ sk_C @ X3)),
% 0.20/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (((r2_hidden @ sk_B_1 @ sk_C) | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['61', '64'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (![X47 : $i, X48 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X47 @ X48) | ~ (r1_tarski @ X48 @ X47))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((((u1_struct_0 @ sk_A) = (sk_C)) | ~ (r1_tarski @ sk_C @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.52  thf('68', plain, (![X3 : $i]: (r1_tarski @ sk_C @ X3)),
% 0.20/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('69', plain, (((u1_struct_0 @ sk_A) = (sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.52  thf(rc3_tops_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ?[B:$i]:
% 0.20/0.52         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.20/0.52           ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (![X54 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_B @ X54) @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.20/0.52          | ~ (l1_pre_topc @ X54)
% 0.20/0.52          | ~ (v2_pre_topc @ X54)
% 0.20/0.52          | (v2_struct_0 @ X54))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.20/0.52  thf(cc1_subset_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (![X40 : $i, X41 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.20/0.52          | (v1_xboole_0 @ X40)
% 0.20/0.52          | ~ (v1_xboole_0 @ X41))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.52          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      ((~ (v1_xboole_0 @ sk_C)
% 0.20/0.52        | (v1_xboole_0 @ (sk_B @ sk_A))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['69', '72'])).
% 0.20/0.52  thf('74', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('77', plain, (((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.20/0.52  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('79', plain, ((v1_xboole_0 @ (sk_B @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (![X54 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (sk_B @ X54))
% 0.20/0.52          | ~ (l1_pre_topc @ X54)
% 0.20/0.52          | ~ (v2_pre_topc @ X54)
% 0.20/0.52          | (v2_struct_0 @ X54))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('84', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.20/0.52  thf('85', plain, ($false), inference('demod', [status(thm)], ['0', '84'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
