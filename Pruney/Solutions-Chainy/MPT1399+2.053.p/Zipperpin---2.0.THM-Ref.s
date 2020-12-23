%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XFAVGiFk1O

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 140 expanded)
%              Number of leaves         :   37 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  704 (1519 expanded)
%              Number of equality atoms :   14 (  39 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

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
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
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
    ! [X16: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('8',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ X18 )
      | ( v3_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
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

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( v3_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('32',plain,(
    ! [X4: $i] :
      ( X4
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X23: $i] :
      ( ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( v4_pre_topc @ X23 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X23 )
      | ( r2_hidden @ X23 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X23: $i] :
      ( ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( v4_pre_topc @ X23 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X23 )
      | ( r2_hidden @ X23 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('59',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('63',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XFAVGiFk1O
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 237 iterations in 0.059s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.55  thf(t28_connsp_2, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @
% 0.21/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.55               ( ~( ( ![D:$i]:
% 0.21/0.55                      ( ( m1_subset_1 @
% 0.21/0.55                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55                        ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55                          ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.55                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.55                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55            ( l1_pre_topc @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55              ( ![C:$i]:
% 0.21/0.55                ( ( m1_subset_1 @
% 0.21/0.55                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.55                  ( ~( ( ![D:$i]:
% 0.21/0.55                         ( ( m1_subset_1 @
% 0.21/0.55                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55                           ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55                             ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.55                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.55                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.21/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t2_subset, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]:
% 0.21/0.55         ((r2_hidden @ X6 @ X7)
% 0.21/0.55          | (v1_xboole_0 @ X7)
% 0.21/0.55          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf(fc10_tops_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X16 : $i]:
% 0.21/0.55         ((v3_pre_topc @ (k2_struct_0 @ X16) @ X16)
% 0.21/0.55          | ~ (l1_pre_topc @ X16)
% 0.21/0.55          | ~ (v2_pre_topc @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.21/0.55  thf(d3_struct_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X13 : $i]:
% 0.21/0.55         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.55  thf(dt_k2_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.55  thf('7', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.55  thf('8', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf(t30_tops_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.55             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.55          | ~ (v3_pre_topc @ X17 @ X18)
% 0.21/0.55          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17) @ X18)
% 0.21/0.55          | ~ (l1_pre_topc @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v4_pre_topc @ 
% 0.21/0.55             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.55          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v4_pre_topc @ 
% 0.21/0.55             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v4_pre_topc @ 
% 0.21/0.55             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v4_pre_topc @ 
% 0.21/0.55             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.55  thf('14', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.55          | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17) @ X18)
% 0.21/0.55          | (v3_pre_topc @ X17 @ X18)
% 0.21/0.55          | ~ (l1_pre_topc @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.55          | ~ (v4_pre_topc @ 
% 0.21/0.55               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.55  thf(t4_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.55  thf(t9_connsp_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.56             ( ![C:$i]:
% 0.21/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.56                      ( ![D:$i]:
% 0.21/0.56                        ( ( m1_subset_1 @
% 0.21/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.21/0.56                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.56          | (r2_hidden @ (sk_C @ X19 @ X20) @ X19)
% 0.21/0.56          | (v3_pre_topc @ X19 @ X20)
% 0.21/0.56          | ~ (l1_pre_topc @ X20)
% 0.21/0.56          | ~ (v2_pre_topc @ X20)
% 0.21/0.56          | (v2_struct_0 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X0)
% 0.21/0.56          | ~ (v2_pre_topc @ X0)
% 0.21/0.56          | ~ (l1_pre_topc @ X0)
% 0.21/0.56          | (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.56          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf(t7_ordinal1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.56          | ~ (l1_pre_topc @ X0)
% 0.21/0.56          | ~ (v2_pre_topc @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (r1_tarski @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.56  thf('24', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.56          | ~ (l1_pre_topc @ X0)
% 0.21/0.56          | ~ (v2_pre_topc @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56          | ~ (v3_pre_topc @ X17 @ X18)
% 0.21/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17) @ X18)
% 0.21/0.56          | ~ (l1_pre_topc @ X18))),
% 0.21/0.56      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X0)
% 0.21/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.21/0.56             X0)
% 0.21/0.56          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.56  thf('29', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.56  thf(t22_subset_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X4 : $i]:
% 0.21/0.56         ((k2_subset_1 @ X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.21/0.56  thf('31', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X4 : $i]: ((X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.21/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.56  thf('33', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['29', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X0)
% 0.21/0.56          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.56          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '33'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X0)
% 0.21/0.56          | ~ (v2_pre_topc @ X0)
% 0.21/0.56          | ~ (l1_pre_topc @ X0)
% 0.21/0.56          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.56          | ~ (l1_pre_topc @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '34'])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.56          | ~ (l1_pre_topc @ X0)
% 0.21/0.56          | ~ (v2_pre_topc @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.56  thf('37', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X23 : $i]:
% 0.21/0.56         (~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.56          | ~ (v4_pre_topc @ X23 @ sk_A)
% 0.21/0.56          | ~ (r2_hidden @ sk_B @ X23)
% 0.21/0.56          | (r2_hidden @ X23 @ sk_C_1)
% 0.21/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('39', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X23 : $i]:
% 0.21/0.56         (~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.56          | ~ (v4_pre_topc @ X23 @ sk_A)
% 0.21/0.56          | ~ (r2_hidden @ sk_B @ X23)
% 0.21/0.56          | (r2_hidden @ X23 @ k1_xboole_0)
% 0.21/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.56        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.56        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '41'])).
% 0.21/0.56  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.56        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.56        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '45'])).
% 0.21/0.56  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(dt_l1_pre_topc, axiom,
% 0.21/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.56        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['46', '47', '48', '51'])).
% 0.21/0.56  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.56      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '54'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.56  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf('59', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.56  thf(fc2_struct_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X15 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.21/0.56          | ~ (l1_struct_0 @ X15)
% 0.21/0.56          | (v2_struct_0 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.56  thf('61', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('63', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.56  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.41/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
