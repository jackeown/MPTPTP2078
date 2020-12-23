%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kcKHOl3ysA

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 166 expanded)
%              Number of leaves         :   41 (  68 expanded)
%              Depth                    :   18
%              Number of atoms          :  810 (1698 expanded)
%              Number of equality atoms :   22 (  53 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('4',plain,(
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

thf('5',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('8',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ( v3_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t9_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ C )
                            & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r2_hidden @ ( sk_C @ X25 @ X26 ) @ X25 )
      | ( v3_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('48',plain,(
    ! [X29: $i] :
      ( ~ ( v3_pre_topc @ X29 @ sk_A )
      | ~ ( v4_pre_topc @ X29 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X29 )
      | ( r2_hidden @ X29 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X29: $i] :
      ( ~ ( v3_pre_topc @ X29 @ sk_A )
      | ~ ( v4_pre_topc @ X29 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X29 )
      | ( r2_hidden @ X29 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('60',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','64'])).

thf('66',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('70',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('73',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kcKHOl3ysA
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 118 iterations in 0.062s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(t28_connsp_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @
% 0.21/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53               ( ~( ( ![D:$i]:
% 0.21/0.53                      ( ( m1_subset_1 @
% 0.21/0.53                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                        ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53                          ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.53                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.53                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( m1_subset_1 @
% 0.21/0.53                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53                  ( ~( ( ![D:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @
% 0.21/0.53                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                           ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53                             ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.53                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.53                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t2_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         ((r2_hidden @ X12 @ X13)
% 0.21/0.53          | (v1_xboole_0 @ X13)
% 0.21/0.53          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(fc10_tops_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X22 : $i]:
% 0.21/0.53         ((v3_pre_topc @ (k2_struct_0 @ X22) @ X22)
% 0.21/0.53          | ~ (l1_pre_topc @ X22)
% 0.21/0.53          | ~ (v2_pre_topc @ X22))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.21/0.53  thf(d3_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X19 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf(dt_k2_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.53  thf('7', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf('8', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf(t30_tops_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.53             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.53          | ~ (v3_pre_topc @ X23 @ X24)
% 0.21/0.53          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v4_pre_topc @ 
% 0.21/0.53             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf(d5_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.21/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v4_pre_topc @ 
% 0.21/0.53             (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0)
% 0.21/0.53          | (v4_pre_topc @ 
% 0.21/0.53             (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v4_pre_topc @ 
% 0.21/0.53             (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_struct_0 @ X0)
% 0.21/0.53          | (v4_pre_topc @ 
% 0.21/0.53             (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.53  thf('18', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.53          | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.21/0.53          | (v3_pre_topc @ X23 @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (v4_pre_topc @ 
% 0.21/0.53               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (v4_pre_topc @ 
% 0.21/0.53               (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0)
% 0.21/0.53          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.53  thf(t4_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf(t9_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.53             ( ![C:$i]:
% 0.21/0.53               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.53                      ( ![D:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @
% 0.21/0.53                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.21/0.53                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X25 : $i, X26 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.53          | (r2_hidden @ (sk_C @ X25 @ X26) @ X25)
% 0.21/0.53          | (v3_pre_topc @ X25 @ X26)
% 0.21/0.53          | ~ (l1_pre_topc @ X26)
% 0.21/0.53          | ~ (v2_pre_topc @ X26)
% 0.21/0.53          | (v2_struct_0 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf(t7_ordinal1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (r1_tarski @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.53  thf('30', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.53          | ~ (v3_pre_topc @ X23 @ X24)
% 0.21/0.53          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.21/0.53             X0)
% 0.21/0.53          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.21/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf(t2_boole, axiom,
% 0.21/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.53  thf(t100_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf(t5_boole, axiom,
% 0.21/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.53  thf('41', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.53  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.53  thf('43', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['37', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.53  thf('47', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X29 : $i]:
% 0.21/0.53         (~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.53          | ~ (v4_pre_topc @ X29 @ sk_A)
% 0.21/0.53          | ~ (r2_hidden @ sk_B @ X29)
% 0.21/0.53          | (r2_hidden @ X29 @ sk_C_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('49', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X29 : $i]:
% 0.21/0.53         (~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.53          | ~ (v4_pre_topc @ X29 @ sk_A)
% 0.21/0.53          | ~ (r2_hidden @ sk_B @ X29)
% 0.21/0.53          | (r2_hidden @ X29 @ k1_xboole_0)
% 0.21/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.53        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.53        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['46', '51'])).
% 0.21/0.53  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.53        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.53        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '55'])).
% 0.21/0.53  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_l1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.53        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['56', '57', '58', '61'])).
% 0.21/0.53  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      ((~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.53      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '64'])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.53  thf('68', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf('69', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.53  thf(fc2_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (![X21 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.21/0.53          | ~ (l1_struct_0 @ X21)
% 0.21/0.53          | (v2_struct_0 @ X21))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.53  thf('71', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.53  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.53  thf('73', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.53  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
