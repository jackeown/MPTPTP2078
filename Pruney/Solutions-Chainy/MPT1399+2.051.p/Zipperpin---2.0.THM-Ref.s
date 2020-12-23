%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XitF546Rqw

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:09 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 187 expanded)
%              Number of leaves         :   42 (  73 expanded)
%              Depth                    :   22
%              Number of atoms          :  751 (2480 expanded)
%              Number of equality atoms :   51 ( 102 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('6',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( X9 = sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('11',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('16',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('20',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = sk_C ) ),
    inference(demod,[status(thm)],['14','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['9','22'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X22: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X21: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('29',plain,(
    ! [X24: $i] :
      ( ~ ( v3_pre_topc @ X24 @ sk_A )
      | ~ ( v4_pre_topc @ X24 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X24 )
      | ( r2_hidden @ X24 @ sk_C )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('42',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('49',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['55','56'])).

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

thf('58',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X16 ) @ X15 )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( sk_B @ sk_A ) )
      = ( sk_B @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('62',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('63',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k6_relat_1 @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['62','63','64'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('66',plain,(
    ! [X14: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('67',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X14: $i] :
      ( ( k9_relat_1 @ sk_C @ X14 )
      = sk_C ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_C
      = ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','65','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_C
    = ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('76',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['76','79','80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XitF546Rqw
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:19:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 389 iterations in 0.096s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.53  thf(t28_connsp_2, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( m1_subset_1 @
% 0.19/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.53               ( ~( ( ![D:$i]:
% 0.19/0.53                      ( ( m1_subset_1 @
% 0.19/0.53                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53                        ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.53                          ( ( v3_pre_topc @ D @ A ) & 
% 0.19/0.53                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.19/0.53                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.53            ( l1_pre_topc @ A ) ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53              ( ![C:$i]:
% 0.19/0.53                ( ( m1_subset_1 @
% 0.19/0.53                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.53                  ( ~( ( ![D:$i]:
% 0.19/0.53                         ( ( m1_subset_1 @
% 0.19/0.53                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53                           ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.53                             ( ( v3_pre_topc @ D @ A ) & 
% 0.19/0.53                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.19/0.53                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.19/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(dt_k2_subset_1, axiom,
% 0.19/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.53  thf('3', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.53  thf('4', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.19/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.53  thf(t50_subset_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( m1_subset_1 @ C @ A ) =>
% 0.19/0.53               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.19/0.53                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.19/0.53          | (r2_hidden @ X10 @ X8)
% 0.19/0.53          | (r2_hidden @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.19/0.53          | ~ (m1_subset_1 @ X10 @ X9)
% 0.19/0.53          | ((X9) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.19/0.53  thf('6', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.19/0.53          | (r2_hidden @ X10 @ X8)
% 0.19/0.53          | (r2_hidden @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.19/0.53          | ~ (m1_subset_1 @ X10 @ X9)
% 0.19/0.53          | ((X9) = (sk_C)))),
% 0.19/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((X0) = (sk_C))
% 0.19/0.53          | ~ (m1_subset_1 @ X1 @ X0)
% 0.19/0.53          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))
% 0.19/0.53          | (r2_hidden @ X1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '7'])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (((r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ sk_B_1 @ 
% 0.19/0.53           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.19/0.53        | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '8'])).
% 0.19/0.53  thf(t4_subset_1, axiom,
% 0.19/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.53  thf('11', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('12', plain, (![X7 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X7))),
% 0.19/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X4 : $i, X5 : $i]:
% 0.19/0.53         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.19/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ sk_C)) = (sk_C))),
% 0.19/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.53  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.53  thf('15', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.53  thf('16', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('17', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.53  thf(t22_subset_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X6 : $i]:
% 0.19/0.53         ((k2_subset_1 @ X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.19/0.53  thf('19', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.19/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ sk_C))),
% 0.19/0.53      inference('sup+', [status(thm)], ['17', '20'])).
% 0.19/0.53  thf('22', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['14', '21'])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (((r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ sk_B_1 @ sk_C)
% 0.19/0.53        | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.19/0.53      inference('demod', [status(thm)], ['9', '22'])).
% 0.19/0.53  thf(fc10_tops_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X22 : $i]:
% 0.19/0.53         ((v3_pre_topc @ (k2_struct_0 @ X22) @ X22)
% 0.19/0.53          | ~ (l1_pre_topc @ X22)
% 0.19/0.53          | ~ (v2_pre_topc @ X22))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.19/0.53  thf(d3_struct_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X19 : $i]:
% 0.19/0.53         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.53  thf(fc4_pre_topc, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (![X21 : $i]:
% 0.19/0.53         ((v4_pre_topc @ (k2_struct_0 @ X21) @ X21)
% 0.19/0.53          | ~ (l1_pre_topc @ X21)
% 0.19/0.53          | ~ (v2_pre_topc @ X21))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (![X19 : $i]:
% 0.19/0.53         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.53  thf('28', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.19/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (![X24 : $i]:
% 0.19/0.53         (~ (v3_pre_topc @ X24 @ sk_A)
% 0.19/0.53          | ~ (v4_pre_topc @ X24 @ sk_A)
% 0.19/0.53          | ~ (r2_hidden @ sk_B_1 @ X24)
% 0.19/0.53          | (r2_hidden @ X24 @ sk_C)
% 0.19/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.19/0.53      inference('sup-', [status(thm)], ['27', '30'])).
% 0.19/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(dt_l1_pre_topc, axiom,
% 0.19/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.53  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['31', '34'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['26', '35'])).
% 0.19/0.53  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.19/0.53  thf('40', plain,
% 0.19/0.53      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.19/0.53      inference('sup-', [status(thm)], ['25', '39'])).
% 0.19/0.53  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.53  thf('42', plain,
% 0.19/0.53      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['24', '42'])).
% 0.19/0.53  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.53  thf('47', plain,
% 0.19/0.53      ((((u1_struct_0 @ sk_A) = (sk_C))
% 0.19/0.53        | (r2_hidden @ sk_B_1 @ sk_C)
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.19/0.53      inference('sup-', [status(thm)], ['23', '46'])).
% 0.19/0.53  thf(t7_ordinal1, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.53  thf('48', plain,
% 0.19/0.53      (![X17 : $i, X18 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.53  thf('49', plain,
% 0.19/0.53      (((r2_hidden @ sk_B_1 @ sk_C)
% 0.19/0.53        | ((u1_struct_0 @ sk_A) = (sk_C))
% 0.19/0.53        | ~ (r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.53  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.53  thf('51', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('52', plain, (![X0 : $i]: (r1_tarski @ sk_C @ X0)),
% 0.19/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.53  thf('53', plain,
% 0.19/0.53      (((r2_hidden @ sk_B_1 @ sk_C) | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.19/0.53      inference('demod', [status(thm)], ['49', '52'])).
% 0.19/0.53  thf('54', plain,
% 0.19/0.53      (![X17 : $i, X18 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.53  thf('55', plain,
% 0.19/0.53      ((((u1_struct_0 @ sk_A) = (sk_C)) | ~ (r1_tarski @ sk_C @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.53  thf('56', plain, (![X0 : $i]: (r1_tarski @ sk_C @ X0)),
% 0.19/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.53  thf('57', plain, (((u1_struct_0 @ sk_A) = (sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.19/0.53  thf(rc3_tops_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ?[B:$i]:
% 0.19/0.53         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.19/0.53           ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.53           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.53  thf('58', plain,
% 0.19/0.53      (![X23 : $i]:
% 0.19/0.53         ((m1_subset_1 @ (sk_B @ X23) @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.19/0.53          | ~ (l1_pre_topc @ X23)
% 0.19/0.53          | ~ (v2_pre_topc @ X23)
% 0.19/0.53          | (v2_struct_0 @ X23))),
% 0.19/0.53      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.19/0.53  thf(t162_funct_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.19/0.53  thf('59', plain,
% 0.19/0.53      (![X15 : $i, X16 : $i]:
% 0.19/0.53         (((k9_relat_1 @ (k6_relat_1 @ X16) @ X15) = (X15))
% 0.19/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.19/0.53  thf('60', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v2_struct_0 @ X0)
% 0.19/0.53          | ~ (v2_pre_topc @ X0)
% 0.19/0.53          | ~ (l1_pre_topc @ X0)
% 0.19/0.53          | ((k9_relat_1 @ (k6_relat_1 @ (u1_struct_0 @ X0)) @ (sk_B @ X0))
% 0.19/0.53              = (sk_B @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.53  thf('61', plain,
% 0.19/0.53      ((((k9_relat_1 @ (k6_relat_1 @ sk_C) @ (sk_B @ sk_A)) = (sk_B @ sk_A))
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | (v2_struct_0 @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['57', '60'])).
% 0.19/0.53  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.19/0.53  thf('62', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.19/0.53  thf('63', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('64', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('65', plain, (((k6_relat_1 @ sk_C) = (sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.19/0.53  thf(t150_relat_1, axiom,
% 0.19/0.53    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.53  thf('66', plain,
% 0.19/0.53      (![X14 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.19/0.53  thf('67', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('68', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('69', plain, (![X14 : $i]: ((k9_relat_1 @ sk_C @ X14) = (sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.19/0.53  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('72', plain, ((((sk_C) = (sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['61', '65', '69', '70', '71'])).
% 0.19/0.53  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('74', plain, (((sk_C) = (sk_B @ sk_A))),
% 0.19/0.53      inference('clc', [status(thm)], ['72', '73'])).
% 0.19/0.53  thf('75', plain,
% 0.19/0.53      (![X23 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ (sk_B @ X23))
% 0.19/0.53          | ~ (l1_pre_topc @ X23)
% 0.19/0.53          | ~ (v2_pre_topc @ X23)
% 0.19/0.53          | (v2_struct_0 @ X23))),
% 0.19/0.53      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.19/0.53  thf('76', plain,
% 0.19/0.53      ((~ (v1_xboole_0 @ sk_C)
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['74', '75'])).
% 0.19/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.53  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.53  thf('78', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('79', plain, ((v1_xboole_0 @ sk_C)),
% 0.19/0.53      inference('demod', [status(thm)], ['77', '78'])).
% 0.19/0.53  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('82', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('demod', [status(thm)], ['76', '79', '80', '81'])).
% 0.19/0.53  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
