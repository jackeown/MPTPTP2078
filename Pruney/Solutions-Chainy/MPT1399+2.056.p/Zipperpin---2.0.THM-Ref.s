%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Eb4UpwGhpo

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 174 expanded)
%              Number of leaves         :   41 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  686 (2188 expanded)
%              Number of equality atoms :   43 (  87 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('3',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X40 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( r2_hidden @ X43 @ X41 )
      | ( r2_hidden @ X43 @ ( k3_subset_1 @ X42 @ X41 ) )
      | ~ ( m1_subset_1 @ X43 @ X42 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('6',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( r2_hidden @ X43 @ X41 )
      | ( r2_hidden @ X43 @ ( k3_subset_1 @ X42 @ X41 ) )
      | ~ ( m1_subset_1 @ X43 @ X42 )
      | ( X42 = sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ sk_C ) )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k4_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
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
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('25',plain,(
    ! [X55: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X55 ) @ X55 )
      | ~ ( l1_pre_topc @ X55 )
      | ~ ( v2_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('27',plain,(
    ! [X54: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X54 ) @ X54 )
      | ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('28',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X39 ) @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('30',plain,(
    ! [X36: $i] :
      ( ( k2_subset_1 @ X36 )
      = X36 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X56: $i] :
      ( ~ ( v3_pre_topc @ X56 @ sk_A )
      | ~ ( v4_pre_topc @ X56 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X56 )
      | ( r2_hidden @ X56 @ sk_C )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X52: $i] :
      ( ( l1_struct_0 @ X52 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('45',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['24','49'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('51',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( r1_tarski @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_C @ X3 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( r1_tarski @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('58',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_C @ X3 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('61',plain,(
    ! [X53: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X53 ) )
      | ~ ( l1_struct_0 @ X53 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('63',plain,(
    ! [X5: $i] :
      ( ( r1_xboole_0 @ X5 @ X5 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('64',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['64','65','66'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( r1_tarski @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_C @ X3 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('71',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('73',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['62','71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Eb4UpwGhpo
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 93 iterations in 0.048s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(t28_connsp_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @
% 0.21/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50               ( ~( ( ![D:$i]:
% 0.21/0.50                      ( ( m1_subset_1 @
% 0.21/0.50                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                        ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50                          ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.50                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.50                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50            ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m1_subset_1 @
% 0.21/0.50                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50                  ( ~( ( ![D:$i]:
% 0.21/0.50                         ( ( m1_subset_1 @
% 0.21/0.50                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                           ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50                             ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.50                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.50                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t4_subset_1, axiom,
% 0.21/0.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X40 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.50  thf('3', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('4', plain, (![X40 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X40))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(t50_subset_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.50               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.21/0.50                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.21/0.50          | (r2_hidden @ X43 @ X41)
% 0.21/0.50          | (r2_hidden @ X43 @ (k3_subset_1 @ X42 @ X41))
% 0.21/0.50          | ~ (m1_subset_1 @ X43 @ X42)
% 0.21/0.50          | ((X42) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.21/0.50  thf('6', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.21/0.50          | (r2_hidden @ X43 @ X41)
% 0.21/0.50          | (r2_hidden @ X43 @ (k3_subset_1 @ X42 @ X41))
% 0.21/0.50          | ~ (m1_subset_1 @ X43 @ X42)
% 0.21/0.50          | ((X42) = (sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((X0) = (sk_C))
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.50          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ sk_C))
% 0.21/0.50          | (r2_hidden @ X1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.50  thf('9', plain, (![X40 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X40))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(d5_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X37 : $i, X38 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))
% 0.21/0.50          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(t2_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.50  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ sk_C) = (sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.50  thf(t100_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (k5_xboole_0 @ X0 @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf(t5_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('18', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.50  thf('19', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ sk_C) = (X4))),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['17', '20'])).
% 0.21/0.50  thf('22', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((X0) = (sk_C))
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.50          | (r2_hidden @ X1 @ X0)
% 0.21/0.50          | (r2_hidden @ X1 @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ sk_C)
% 0.21/0.50        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '23'])).
% 0.21/0.50  thf(fc10_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X55 : $i]:
% 0.21/0.50         ((v3_pre_topc @ (k2_struct_0 @ X55) @ X55)
% 0.21/0.50          | ~ (l1_pre_topc @ X55)
% 0.21/0.50          | ~ (v2_pre_topc @ X55))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.21/0.50  thf(d3_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X51 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf(fc4_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X54 : $i]:
% 0.21/0.50         ((v4_pre_topc @ (k2_struct_0 @ X54) @ X54)
% 0.21/0.50          | ~ (l1_pre_topc @ X54)
% 0.21/0.50          | ~ (v2_pre_topc @ X54))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X51 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf(dt_k2_subset_1, axiom,
% 0.21/0.50    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X39 : $i]: (m1_subset_1 @ (k2_subset_1 @ X39) @ (k1_zfmisc_1 @ X39))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.50  thf('30', plain, (![X36 : $i]: ((k2_subset_1 @ X36) = (X36))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.50  thf('31', plain, (![X39 : $i]: (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X39))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X56 : $i]:
% 0.21/0.50         (~ (v3_pre_topc @ X56 @ sk_A)
% 0.21/0.50          | ~ (v4_pre_topc @ X56 @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ sk_B @ X56)
% 0.21/0.50          | (r2_hidden @ X56 @ sk_C)
% 0.21/0.50          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '33'])).
% 0.21/0.50  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X52 : $i]: ((l1_struct_0 @ X52) | ~ (l1_pre_topc @ X52))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '38'])).
% 0.21/0.50  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '42'])).
% 0.21/0.50  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '45'])).
% 0.21/0.50  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((((u1_struct_0 @ sk_A) = (sk_C))
% 0.21/0.50        | (r2_hidden @ sk_B @ sk_C)
% 0.21/0.50        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '49'])).
% 0.21/0.50  thf(t7_ordinal1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X49 : $i, X50 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X49 @ X50) | ~ (r1_tarski @ X50 @ X49))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ sk_C)
% 0.21/0.50        | ((u1_struct_0 @ sk_A) = (sk_C))
% 0.21/0.50        | ~ (r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('53', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('54', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain, (![X3 : $i]: (r1_tarski @ sk_C @ X3)),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ sk_C) | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '55'])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X49 : $i, X50 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X49 @ X50) | ~ (r1_tarski @ X50 @ X49))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      ((((u1_struct_0 @ sk_A) = (sk_C)) | ~ (r1_tarski @ sk_C @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain, (![X3 : $i]: (r1_tarski @ sk_C @ X3)),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('60', plain, (((u1_struct_0 @ sk_A) = (sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.50  thf(fc2_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (![X53 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X53))
% 0.21/0.50          | ~ (l1_struct_0 @ X53)
% 0.21/0.50          | (v2_struct_0 @ X53))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      ((~ (v1_xboole_0 @ sk_C) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.50  thf(t66_xboole_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.50       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (![X5 : $i]: ((r1_xboole_0 @ X5 @ X5) | ((X5) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.21/0.50  thf('64', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.50  thf('65', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('67', plain, ((r1_xboole_0 @ sk_C @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.50  thf(t69_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.50       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ X7 @ X8)
% 0.21/0.50          | ~ (r1_tarski @ X7 @ X8)
% 0.21/0.50          | (v1_xboole_0 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.50  thf('69', plain, (((v1_xboole_0 @ sk_C) | ~ (r1_tarski @ sk_C @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.50  thf('70', plain, (![X3 : $i]: (r1_tarski @ sk_C @ X3)),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('71', plain, ((v1_xboole_0 @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('73', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['62', '71', '72'])).
% 0.21/0.50  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
