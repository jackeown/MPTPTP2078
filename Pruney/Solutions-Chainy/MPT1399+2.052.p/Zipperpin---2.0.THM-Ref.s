%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I8zQ2ZZJXS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:09 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 182 expanded)
%              Number of leaves         :   41 (  71 expanded)
%              Depth                    :   23
%              Number of atoms          :  753 (2345 expanded)
%              Number of equality atoms :   40 (  88 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('2',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X19: $i] :
      ( ( X19 = sk_C )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t50_subset_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('9',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( X9 = sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('14',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('19',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = sk_C ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = sk_C ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['12','25'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('27',plain,(
    ! [X28: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('29',plain,(
    ! [X27: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('30',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('32',plain,(
    ! [X30: $i] :
      ( ~ ( v3_pre_topc @ X30 @ sk_A )
      | ~ ( v4_pre_topc @ X30 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X30 )
      | ( r2_hidden @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('45',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ( r2_hidden @ sk_B_2 @ sk_C )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','49'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,
    ( ( r2_hidden @ sk_B_2 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_B_2 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('58',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['58','59'])).

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

thf('61',plain,(
    ! [X29: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B_1 @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['3','72'])).

thf('74',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('75',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I8zQ2ZZJXS
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 400 iterations in 0.163s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.40/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.61  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.40/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.40/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.61  thf(t28_connsp_2, conjecture,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.61           ( ![C:$i]:
% 0.40/0.61             ( ( m1_subset_1 @
% 0.40/0.61                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.61               ( ~( ( ![D:$i]:
% 0.40/0.61                      ( ( m1_subset_1 @
% 0.40/0.61                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61                        ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.61                          ( ( v3_pre_topc @ D @ A ) & 
% 0.40/0.61                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.40/0.61                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i]:
% 0.40/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.61            ( l1_pre_topc @ A ) ) =>
% 0.40/0.61          ( ![B:$i]:
% 0.40/0.61            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.61              ( ![C:$i]:
% 0.40/0.61                ( ( m1_subset_1 @
% 0.40/0.61                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.61                  ( ~( ( ![D:$i]:
% 0.40/0.61                         ( ( m1_subset_1 @
% 0.40/0.61                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61                           ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.61                             ( ( v3_pre_topc @ D @ A ) & 
% 0.40/0.61                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.40/0.61                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.40/0.61  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(t6_mcart_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.61          ( ![B:$i]:
% 0.40/0.61            ( ~( ( r2_hidden @ B @ A ) & 
% 0.40/0.61                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.40/0.61                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.40/0.61                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.40/0.61                       ( r2_hidden @ G @ B ) ) =>
% 0.40/0.61                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (![X19 : $i]:
% 0.40/0.61         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 0.40/0.61      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.40/0.61  thf('2', plain, (((sk_C) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X19 : $i]: (((X19) = (sk_C)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 0.40/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.40/0.61  thf('4', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(dt_k2_subset_1, axiom,
% 0.40/0.61    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.40/0.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.40/0.61  thf('6', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.61  thf('7', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf(t50_subset_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.61           ( ![C:$i]:
% 0.40/0.61             ( ( m1_subset_1 @ C @ A ) =>
% 0.40/0.61               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.40/0.61                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.40/0.61          | (r2_hidden @ X10 @ X8)
% 0.40/0.61          | (r2_hidden @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.40/0.61          | ~ (m1_subset_1 @ X10 @ X9)
% 0.40/0.61          | ((X9) = (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.40/0.61  thf('9', plain, (((sk_C) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.40/0.61          | (r2_hidden @ X10 @ X8)
% 0.40/0.61          | (r2_hidden @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.40/0.61          | ~ (m1_subset_1 @ X10 @ X9)
% 0.40/0.61          | ((X9) = (sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((X0) = (sk_C))
% 0.40/0.61          | ~ (m1_subset_1 @ X1 @ X0)
% 0.40/0.61          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))
% 0.40/0.61          | (r2_hidden @ X1 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['7', '10'])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (((r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | (r2_hidden @ sk_B_2 @ 
% 0.40/0.61           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.40/0.61        | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['4', '11'])).
% 0.40/0.61  thf(t4_subset_1, axiom,
% 0.40/0.61    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.61  thf('14', plain, (((sk_C) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('15', plain, (![X7 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X7))),
% 0.40/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.61  thf(involutiveness_k3_subset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.61       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X4 : $i, X5 : $i]:
% 0.40/0.61         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.40/0.61          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ sk_C)) = (sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.61  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.61  thf('18', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.40/0.61  thf('19', plain, (((sk_C) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('20', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (sk_C))),
% 0.40/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.61  thf(t22_subset_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X6 : $i]:
% 0.40/0.61         ((k2_subset_1 @ X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.40/0.61  thf('22', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.40/0.61      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.61  thf('24', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ sk_C))),
% 0.40/0.61      inference('sup+', [status(thm)], ['20', '23'])).
% 0.40/0.61  thf('25', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (sk_C))),
% 0.40/0.61      inference('demod', [status(thm)], ['17', '24'])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (((r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | (r2_hidden @ sk_B_2 @ sk_C)
% 0.40/0.61        | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['12', '25'])).
% 0.40/0.61  thf(fc10_tops_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X28 : $i]:
% 0.40/0.61         ((v3_pre_topc @ (k2_struct_0 @ X28) @ X28)
% 0.40/0.61          | ~ (l1_pre_topc @ X28)
% 0.40/0.61          | ~ (v2_pre_topc @ X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.40/0.61  thf(d3_struct_0, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      (![X25 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf(fc4_pre_topc, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X27 : $i]:
% 0.40/0.61         ((v4_pre_topc @ (k2_struct_0 @ X27) @ X27)
% 0.40/0.61          | ~ (l1_pre_topc @ X27)
% 0.40/0.61          | ~ (v2_pre_topc @ X27))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (![X25 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('31', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      (![X30 : $i]:
% 0.40/0.61         (~ (v3_pre_topc @ X30 @ sk_A)
% 0.40/0.61          | ~ (v4_pre_topc @ X30 @ sk_A)
% 0.40/0.61          | ~ (r2_hidden @ sk_B_2 @ X30)
% 0.40/0.61          | (r2_hidden @ X30 @ sk_C)
% 0.40/0.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.40/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.40/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.40/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['30', '33'])).
% 0.40/0.61  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(dt_l1_pre_topc, axiom,
% 0.40/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.40/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.40/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.40/0.61      inference('demod', [status(thm)], ['34', '37'])).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.40/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.40/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['29', '38'])).
% 0.40/0.61  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('42', plain,
% 0.40/0.61      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.40/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.40/0.61  thf('43', plain,
% 0.40/0.61      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['28', '42'])).
% 0.40/0.61  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.40/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.40/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.40/0.61  thf('46', plain,
% 0.40/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.40/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.40/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['27', '45'])).
% 0.40/0.61  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('49', plain,
% 0.40/0.61      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.40/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.40/0.61  thf('50', plain,
% 0.40/0.61      ((((u1_struct_0 @ sk_A) = (sk_C))
% 0.40/0.61        | (r2_hidden @ sk_B_2 @ sk_C)
% 0.40/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['26', '49'])).
% 0.40/0.61  thf(t7_ordinal1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.61  thf('51', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.40/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.61  thf('52', plain,
% 0.40/0.61      (((r2_hidden @ sk_B_2 @ sk_C)
% 0.40/0.61        | ((u1_struct_0 @ sk_A) = (sk_C))
% 0.40/0.61        | ~ (r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.61  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.61  thf('54', plain, (((sk_C) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('55', plain, (![X0 : $i]: (r1_tarski @ sk_C @ X0)),
% 0.40/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      (((r2_hidden @ sk_B_2 @ sk_C) | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['52', '55'])).
% 0.40/0.61  thf('57', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.40/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.61  thf('58', plain,
% 0.40/0.61      ((((u1_struct_0 @ sk_A) = (sk_C)) | ~ (r1_tarski @ sk_C @ sk_B_2))),
% 0.40/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.61  thf('59', plain, (![X0 : $i]: (r1_tarski @ sk_C @ X0)),
% 0.40/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.61  thf('60', plain, (((u1_struct_0 @ sk_A) = (sk_C))),
% 0.40/0.61      inference('demod', [status(thm)], ['58', '59'])).
% 0.40/0.61  thf(rc3_tops_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61       ( ?[B:$i]:
% 0.40/0.61         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.40/0.61           ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.61           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.40/0.61  thf('61', plain,
% 0.40/0.61      (![X29 : $i]:
% 0.40/0.61         ((m1_subset_1 @ (sk_B_1 @ X29) @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.40/0.61          | ~ (l1_pre_topc @ X29)
% 0.40/0.61          | ~ (v2_pre_topc @ X29)
% 0.40/0.61          | (v2_struct_0 @ X29))),
% 0.40/0.61      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.40/0.61  thf(t5_subset, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.40/0.61          ( v1_xboole_0 @ C ) ) ))).
% 0.40/0.61  thf('62', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X14 @ X15)
% 0.40/0.61          | ~ (v1_xboole_0 @ X16)
% 0.40/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.40/0.61  thf('63', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((v2_struct_0 @ X0)
% 0.40/0.61          | ~ (v2_pre_topc @ X0)
% 0.40/0.61          | ~ (l1_pre_topc @ X0)
% 0.40/0.61          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.40/0.61          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.40/0.61  thf('64', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ sk_C)
% 0.40/0.61          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))
% 0.40/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.61          | (v2_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['60', '63'])).
% 0.40/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.61  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.61  thf('66', plain, (((sk_C) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('67', plain, ((v1_xboole_0 @ sk_C)),
% 0.40/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.61  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('70', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['64', '67', '68', '69'])).
% 0.40/0.61  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('72', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))),
% 0.40/0.61      inference('clc', [status(thm)], ['70', '71'])).
% 0.40/0.61  thf('73', plain, (((sk_B_1 @ sk_A) = (sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['3', '72'])).
% 0.40/0.61  thf('74', plain,
% 0.40/0.61      (![X29 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ (sk_B_1 @ X29))
% 0.40/0.61          | ~ (l1_pre_topc @ X29)
% 0.40/0.61          | ~ (v2_pre_topc @ X29)
% 0.40/0.61          | (v2_struct_0 @ X29))),
% 0.40/0.61      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.40/0.61  thf('75', plain,
% 0.40/0.61      ((~ (v1_xboole_0 @ sk_C)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.40/0.61  thf('76', plain, ((v1_xboole_0 @ sk_C)),
% 0.40/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.61  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('79', plain, ((v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.40/0.61  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
