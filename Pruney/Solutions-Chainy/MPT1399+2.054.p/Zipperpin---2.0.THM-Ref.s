%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.itvCYrbekm

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 159 expanded)
%              Number of leaves         :   39 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  639 (1988 expanded)
%              Number of equality atoms :   39 (  78 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('3',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X9 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ( r2_hidden @ X12 @ ( k3_subset_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('6',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ( r2_hidden @ X12 @ ( k3_subset_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( X11 = sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ sk_C ) )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
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
    ! [X24: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X24 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('27',plain,(
    ! [X23: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('28',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('30',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X25: $i] :
      ( ~ ( v3_pre_topc @ X25 @ sk_A )
      | ~ ( v4_pre_topc @ X25 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X25 )
      | ( r2_hidden @ X25 @ sk_C )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
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
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('67',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['62','65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.itvCYrbekm
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:59:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 78 iterations in 0.035s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(t28_connsp_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @
% 0.20/0.49                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49               ( ~( ( ![D:$i]:
% 0.20/0.49                      ( ( m1_subset_1 @
% 0.20/0.49                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                        ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49                          ( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.49                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.20/0.49                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( m1_subset_1 @
% 0.20/0.49                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49                  ( ~( ( ![D:$i]:
% 0.20/0.49                         ( ( m1_subset_1 @
% 0.20/0.49                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                           ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49                             ( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.49                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.20/0.49                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.20/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t4_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf('3', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain, (![X9 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X9))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(t50_subset_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.49               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.20/0.49                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.49          | (r2_hidden @ X12 @ X10)
% 0.20/0.49          | (r2_hidden @ X12 @ (k3_subset_1 @ X11 @ X10))
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ X11)
% 0.20/0.49          | ((X11) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.20/0.49  thf('6', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.49          | (r2_hidden @ X12 @ X10)
% 0.20/0.49          | (r2_hidden @ X12 @ (k3_subset_1 @ X11 @ X10))
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ X11)
% 0.20/0.49          | ((X11) = (sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) = (sk_C))
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.49          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ sk_C))
% 0.20/0.49          | (r2_hidden @ X1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.49  thf('9', plain, (![X9 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X9))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(d5_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.20/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ sk_C) = (sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.49  thf(t100_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.49           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (k5_xboole_0 @ X0 @ sk_C))),
% 0.20/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf(t5_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.49  thf('18', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.49  thf('19', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ sk_C) = (X4))),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.49  thf('22', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) = (sk_C))
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.49          | (r2_hidden @ X1 @ X0)
% 0.20/0.49          | (r2_hidden @ X1 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ sk_C)
% 0.20/0.49        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '23'])).
% 0.20/0.49  thf(fc10_tops_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X24 : $i]:
% 0.20/0.49         ((v3_pre_topc @ (k2_struct_0 @ X24) @ X24)
% 0.20/0.49          | ~ (l1_pre_topc @ X24)
% 0.20/0.49          | ~ (v2_pre_topc @ X24))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.20/0.49  thf(d3_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X20 : $i]:
% 0.20/0.49         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.49  thf(fc4_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X23 : $i]:
% 0.20/0.49         ((v4_pre_topc @ (k2_struct_0 @ X23) @ X23)
% 0.20/0.49          | ~ (l1_pre_topc @ X23)
% 0.20/0.49          | ~ (v2_pre_topc @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X20 : $i]:
% 0.20/0.49         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.49  thf(dt_k2_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.49  thf('30', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.49  thf('31', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X25 : $i]:
% 0.20/0.49         (~ (v3_pre_topc @ X25 @ sk_A)
% 0.20/0.49          | ~ (v4_pre_topc @ X25 @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ sk_B @ X25)
% 0.20/0.49          | (r2_hidden @ X25 @ sk_C)
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '33'])).
% 0.20/0.49  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_l1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['34', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '38'])).
% 0.20/0.49  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '42'])).
% 0.20/0.49  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '45'])).
% 0.20/0.49  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((((u1_struct_0 @ sk_A) = (sk_C))
% 0.20/0.49        | (r2_hidden @ sk_B @ sk_C)
% 0.20/0.49        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '49'])).
% 0.20/0.49  thf(t7_ordinal1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ sk_C)
% 0.20/0.49        | ((u1_struct_0 @ sk_A) = (sk_C))
% 0.20/0.49        | ~ (r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.49  thf('53', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.49  thf('54', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('55', plain, (![X3 : $i]: (r1_tarski @ sk_C @ X3)),
% 0.20/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ sk_C) | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['52', '55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      ((((u1_struct_0 @ sk_A) = (sk_C)) | ~ (r1_tarski @ sk_C @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.49  thf('59', plain, (![X3 : $i]: (r1_tarski @ sk_C @ X3)),
% 0.20/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('60', plain, (((u1_struct_0 @ sk_A) = (sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.49  thf(fc2_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (![X22 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 0.20/0.49          | ~ (l1_struct_0 @ X22)
% 0.20/0.49          | (v2_struct_0 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      ((~ (v1_xboole_0 @ sk_C) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('64', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('65', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('67', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['62', '65', '66'])).
% 0.20/0.49  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
