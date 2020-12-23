%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Co6RDQyMai

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:04 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 190 expanded)
%              Number of leaves         :   43 (  74 expanded)
%              Depth                    :   21
%              Number of atoms          :  734 (2168 expanded)
%              Number of equality atoms :   45 (  86 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X45: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('3',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X45 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( r2_hidden @ X48 @ X46 )
      | ( r2_hidden @ X48 @ ( k3_subset_1 @ X47 @ X46 ) )
      | ~ ( m1_subset_1 @ X48 @ X47 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('6',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( r2_hidden @ X48 @ X46 )
      | ( r2_hidden @ X48 @ ( k3_subset_1 @ X47 @ X46 ) )
      | ~ ( m1_subset_1 @ X48 @ X47 )
      | ( X47 = sk_C_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ sk_C_1 ) )
      | ( r2_hidden @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X43 @ X44 )
        = ( k4_xboole_0 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C_1 )
      = ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C_1 )
      = ( k5_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ sk_C_1 )
      = X10 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C_1 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C_1 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['8','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('29',plain,(
    ! [X62: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X62 ) @ X62 )
      | ~ ( l1_pre_topc @ X62 )
      | ~ ( v2_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X58: $i] :
      ( ( ( k2_struct_0 @ X58 )
        = ( u1_struct_0 @ X58 ) )
      | ~ ( l1_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('31',plain,(
    ! [X61: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X61 ) @ X61 )
      | ~ ( l1_pre_topc @ X61 )
      | ~ ( v2_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('32',plain,(
    ! [X58: $i] :
      ( ( ( k2_struct_0 @ X58 )
        = ( u1_struct_0 @ X58 ) )
      | ~ ( l1_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ X38 @ X39 )
      | ( r2_hidden @ X38 @ X40 )
      | ( X40
       != ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('36',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X38 @ X39 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X51: $i,X52: $i] :
      ( ( m1_subset_1 @ X51 @ X52 )
      | ~ ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X63: $i] :
      ( ~ ( v3_pre_topc @ X63 @ sk_A )
      | ~ ( v4_pre_topc @ X63 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X63 )
      | ( r2_hidden @ X63 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('44',plain,(
    ! [X59: $i] :
      ( ( l1_struct_0 @ X59 )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('53',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','57'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('61',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X9: $i] :
      ( r1_tarski @ sk_C_1 @ X9 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('65',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X56 @ X57 )
      | ~ ( r1_tarski @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('70',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['63','66'])).

thf('72',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['70','71'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('73',plain,(
    ! [X60: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X60 ) )
      | ~ ( l1_struct_0 @ X60 )
      | ( v2_struct_0 @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['63','66'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('77',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Co6RDQyMai
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:57:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 295 iterations in 0.198s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.65  thf(t28_connsp_2, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @
% 0.45/0.65                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65               ( ~( ( ![D:$i]:
% 0.45/0.65                      ( ( m1_subset_1 @
% 0.45/0.65                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65                        ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65                          ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.65                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.65                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.65            ( l1_pre_topc @ A ) ) =>
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65              ( ![C:$i]:
% 0.45/0.65                ( ( m1_subset_1 @
% 0.45/0.65                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65                  ( ~( ( ![D:$i]:
% 0.45/0.65                         ( ( m1_subset_1 @
% 0.45/0.65                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65                           ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65                             ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.65                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.65                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.45/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t4_subset_1, axiom,
% 0.45/0.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X45 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X45))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.65  thf('3', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('4', plain, (![X45 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X45))),
% 0.45/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(t50_subset_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @ C @ A ) =>
% 0.45/0.65               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.45/0.65                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.45/0.65          | (r2_hidden @ X48 @ X46)
% 0.45/0.65          | (r2_hidden @ X48 @ (k3_subset_1 @ X47 @ X46))
% 0.45/0.65          | ~ (m1_subset_1 @ X48 @ X47)
% 0.45/0.65          | ((X47) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.45/0.65  thf('6', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.45/0.65          | (r2_hidden @ X48 @ X46)
% 0.45/0.65          | (r2_hidden @ X48 @ (k3_subset_1 @ X47 @ X46))
% 0.45/0.65          | ~ (m1_subset_1 @ X48 @ X47)
% 0.45/0.65          | ((X47) = (sk_C_1)))),
% 0.45/0.65      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (sk_C_1))
% 0.45/0.65          | ~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.65          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ sk_C_1))
% 0.45/0.65          | (r2_hidden @ X1 @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '7'])).
% 0.45/0.65  thf('9', plain, (![X45 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X45))),
% 0.45/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(d5_subset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.65       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X43 : $i, X44 : $i]:
% 0.45/0.65         (((k3_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))
% 0.45/0.65          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C_1) = (k4_xboole_0 @ X0 @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf(t2_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.65  thf('13', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('14', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('15', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ sk_C_1) = (sk_C_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.45/0.65  thf(t12_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X49 : $i, X50 : $i]:
% 0.45/0.65         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X8 : $i]: ((k1_setfam_1 @ (k2_tarski @ X8 @ sk_C_1)) = (sk_C_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf(t100_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X6 @ X7)
% 0.45/0.65           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X49 : $i, X50 : $i]:
% 0.45/0.65         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X6 @ X7)
% 0.45/0.65           = (k5_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C_1) = (k5_xboole_0 @ X0 @ sk_C_1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['17', '20'])).
% 0.45/0.65  thf(t5_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.65  thf('22', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf('23', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('24', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ sk_C_1) = (X10))),
% 0.45/0.65      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.65  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C_1) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['21', '24'])).
% 0.45/0.65  thf('26', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C_1) = (X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['11', '25'])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (sk_C_1))
% 0.45/0.65          | ~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.65          | (r2_hidden @ X1 @ X0)
% 0.45/0.65          | (r2_hidden @ X1 @ sk_C_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['8', '26'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (((r2_hidden @ sk_B_1 @ sk_C_1)
% 0.45/0.65        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ((u1_struct_0 @ sk_A) = (sk_C_1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '27'])).
% 0.45/0.65  thf(fc10_tops_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X62 : $i]:
% 0.45/0.65         ((v3_pre_topc @ (k2_struct_0 @ X62) @ X62)
% 0.45/0.65          | ~ (l1_pre_topc @ X62)
% 0.45/0.65          | ~ (v2_pre_topc @ X62))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.45/0.65  thf(d3_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X58 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X58) = (u1_struct_0 @ X58)) | ~ (l1_struct_0 @ X58))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf(fc4_pre_topc, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X61 : $i]:
% 0.45/0.65         ((v4_pre_topc @ (k2_struct_0 @ X61) @ X61)
% 0.45/0.65          | ~ (l1_pre_topc @ X61)
% 0.45/0.65          | ~ (v2_pre_topc @ X61))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X58 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X58) = (u1_struct_0 @ X58)) | ~ (l1_struct_0 @ X58))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('34', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.45/0.65      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.65  thf(d1_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.45/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X38 @ X39)
% 0.45/0.65          | (r2_hidden @ X38 @ X40)
% 0.45/0.65          | ((X40) != (k1_zfmisc_1 @ X39)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X38 : $i, X39 : $i]:
% 0.45/0.65         ((r2_hidden @ X38 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X38 @ X39))),
% 0.45/0.65      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.65  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['34', '36'])).
% 0.45/0.65  thf(t1_subset, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X51 : $i, X52 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X51 @ X52) | ~ (r2_hidden @ X51 @ X52))),
% 0.45/0.65      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.65  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X63 : $i]:
% 0.45/0.65         (~ (v3_pre_topc @ X63 @ sk_A)
% 0.45/0.65          | ~ (v4_pre_topc @ X63 @ sk_A)
% 0.45/0.65          | ~ (r2_hidden @ sk_B_1 @ X63)
% 0.45/0.65          | (r2_hidden @ X63 @ sk_C_1)
% 0.45/0.65          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['32', '41'])).
% 0.45/0.65  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_l1_pre_topc, axiom,
% 0.45/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (![X59 : $i]: ((l1_struct_0 @ X59) | ~ (l1_pre_topc @ X59))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.65  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['42', '45'])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['31', '46'])).
% 0.45/0.65  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['30', '50'])).
% 0.45/0.65  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['29', '53'])).
% 0.45/0.65  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      ((((u1_struct_0 @ sk_A) = (sk_C_1))
% 0.45/0.65        | (r2_hidden @ sk_B_1 @ sk_C_1)
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['28', '57'])).
% 0.45/0.65  thf(d1_xboole_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (((r2_hidden @ sk_B_1 @ sk_C_1)
% 0.45/0.65        | ((u1_struct_0 @ sk_A) = (sk_C_1))
% 0.45/0.65        | ~ (v1_xboole_0 @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.65  thf('61', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.65  thf('62', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('63', plain, (![X9 : $i]: (r1_tarski @ sk_C_1 @ X9)),
% 0.45/0.65      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf(t7_ordinal1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (![X56 : $i, X57 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X56 @ X57) | ~ (r1_tarski @ X57 @ X56))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.65  thf('67', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['63', '66'])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      (((r2_hidden @ sk_B_1 @ sk_C_1) | ((u1_struct_0 @ sk_A) = (sk_C_1)))),
% 0.45/0.65      inference('demod', [status(thm)], ['60', '67'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('70', plain,
% 0.45/0.65      ((((u1_struct_0 @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.65  thf('71', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['63', '66'])).
% 0.45/0.65  thf('72', plain, (((u1_struct_0 @ sk_A) = (sk_C_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['70', '71'])).
% 0.45/0.65  thf(fc2_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      (![X60 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X60))
% 0.45/0.65          | ~ (l1_struct_0 @ X60)
% 0.45/0.65          | (v2_struct_0 @ X60))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.65  thf('74', plain,
% 0.45/0.65      ((~ (v1_xboole_0 @ sk_C_1)
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.65  thf('75', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['63', '66'])).
% 0.45/0.65  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('77', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.45/0.65  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
