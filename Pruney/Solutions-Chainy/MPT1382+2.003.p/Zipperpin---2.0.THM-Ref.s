%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kl76B30Vqq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:50 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 264 expanded)
%              Number of leaves         :   25 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  881 (4341 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t7_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( m1_connsp_2 @ C @ A @ B )
                    & ! [D: $i] :
                        ( ( ~ ( v1_xboole_0 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ B )
                            & ( v3_pre_topc @ D @ A )
                            & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_connsp_2])).

thf('0',plain,(
    m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ( r2_hidden @ X21 @ ( k1_tops_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ X27 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X27 @ sk_A )
      | ~ ( m1_connsp_2 @ X27 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('43',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','46','47'])).

thf('49',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('50',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_tops_1 @ X22 @ X23 ) )
      | ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('57',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( l1_pre_topc @ X17 )
        | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( v3_pre_topc @ X18 @ X17 )
        | ( ( k1_tops_1 @ X17 @ X18 )
          = X18 ) )
   <= ! [X17: $i,X18: $i] :
        ( ~ ( l1_pre_topc @ X17 )
        | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( v3_pre_topc @ X18 @ X17 )
        | ( ( k1_tops_1 @ X17 @ X18 )
          = X18 ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(split,[status(esa)],['56'])).

thf('60',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ~ ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( l1_pre_topc @ X17 )
        | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( v3_pre_topc @ X18 @ X17 )
        | ( ( k1_tops_1 @ X17 @ X18 )
          = X18 ) )
    | ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(split,[status(esa)],['56'])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 ) ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 ) ) ),
    inference(simpl_trail,[status(thm)],['57','65'])).

thf('67',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    = ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','70'])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['48','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['18','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kl76B30Vqq
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:23:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.71  % Solved by: fo/fo7.sh
% 0.47/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.71  % done 430 iterations in 0.248s
% 0.47/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.71  % SZS output start Refutation
% 0.47/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.47/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.71  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.47/0.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.71  thf(t7_connsp_2, conjecture,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.71           ( ![C:$i]:
% 0.47/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.47/0.71                    ( ![D:$i]:
% 0.47/0.71                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.47/0.71                          ( m1_subset_1 @
% 0.47/0.71                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.71                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.47/0.71                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.71    (~( ![A:$i]:
% 0.47/0.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.71            ( l1_pre_topc @ A ) ) =>
% 0.47/0.71          ( ![B:$i]:
% 0.47/0.71            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.71              ( ![C:$i]:
% 0.47/0.71                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.47/0.71                       ( ![D:$i]:
% 0.47/0.71                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.47/0.71                             ( m1_subset_1 @
% 0.47/0.71                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.71                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.47/0.71                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.71    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.47/0.71  thf('0', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('1', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(d1_connsp_2, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.71           ( ![C:$i]:
% 0.47/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.47/0.71                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.47/0.71  thf('2', plain,
% 0.47/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.47/0.71          | ~ (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.47/0.71          | (r2_hidden @ X21 @ (k1_tops_1 @ X22 @ X23))
% 0.47/0.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.47/0.71          | ~ (l1_pre_topc @ X22)
% 0.47/0.71          | ~ (v2_pre_topc @ X22)
% 0.47/0.71          | (v2_struct_0 @ X22))),
% 0.47/0.71      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.47/0.71  thf('3', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_A)
% 0.47/0.71          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.71          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.47/0.71          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.71  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('6', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_A)
% 0.47/0.71          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.47/0.71          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.47/0.71  thf('7', plain,
% 0.47/0.71      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.71        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.47/0.71        | (v2_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['0', '6'])).
% 0.47/0.71  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('9', plain,
% 0.47/0.71      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.47/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.71  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('11', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.47/0.71      inference('clc', [status(thm)], ['9', '10'])).
% 0.47/0.71  thf(d10_xboole_0, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.71  thf('12', plain,
% 0.47/0.71      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.47/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.71  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.47/0.71      inference('simplify', [status(thm)], ['12'])).
% 0.47/0.71  thf(t3_subset, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.71  thf('14', plain,
% 0.47/0.71      (![X7 : $i, X9 : $i]:
% 0.47/0.71         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.71  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.71  thf(t5_subset, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.47/0.71          ( v1_xboole_0 @ C ) ) ))).
% 0.47/0.71  thf('16', plain,
% 0.47/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.71         (~ (r2_hidden @ X10 @ X11)
% 0.47/0.71          | ~ (v1_xboole_0 @ X12)
% 0.47/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t5_subset])).
% 0.47/0.71  thf('17', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.71  thf('18', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['11', '17'])).
% 0.47/0.71  thf(d3_tarski, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.71  thf('19', plain,
% 0.47/0.71      (![X1 : $i, X3 : $i]:
% 0.47/0.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.71  thf('20', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t44_tops_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( l1_pre_topc @ A ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.47/0.71  thf('21', plain,
% 0.47/0.71      (![X15 : $i, X16 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.47/0.71          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ X15)
% 0.47/0.71          | ~ (l1_pre_topc @ X16))),
% 0.47/0.71      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.47/0.71  thf('22', plain,
% 0.47/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.71        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.71  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('24', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.47/0.71      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.71  thf('25', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.71         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.71          | (r2_hidden @ X0 @ X2)
% 0.47/0.71          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.71  thf('26', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((r2_hidden @ X0 @ sk_C_1)
% 0.47/0.71          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.71  thf('27', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.47/0.71          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['19', '26'])).
% 0.47/0.71  thf('28', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('29', plain,
% 0.47/0.71      (![X7 : $i, X8 : $i]:
% 0.47/0.71         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.71  thf('30', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.71  thf('31', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.71         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.71          | (r2_hidden @ X0 @ X2)
% 0.47/0.71          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.71  thf('32', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.71  thf('33', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.47/0.71          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.47/0.71             (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['27', '32'])).
% 0.47/0.71  thf('34', plain,
% 0.47/0.71      (![X1 : $i, X3 : $i]:
% 0.47/0.71         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.71  thf('35', plain,
% 0.47/0.71      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.47/0.71        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.71  thf('36', plain,
% 0.47/0.71      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('simplify', [status(thm)], ['35'])).
% 0.47/0.71  thf('37', plain,
% 0.47/0.71      (![X7 : $i, X9 : $i]:
% 0.47/0.71         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.71  thf('38', plain,
% 0.47/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.47/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.71  thf('39', plain,
% 0.47/0.71      (![X27 : $i]:
% 0.47/0.71         (~ (r1_tarski @ X27 @ sk_C_1)
% 0.47/0.71          | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.47/0.71          | ~ (m1_connsp_2 @ X27 @ sk_A @ sk_B)
% 0.47/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.71          | (v1_xboole_0 @ X27))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('40', plain,
% 0.47/0.71      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.47/0.71        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.47/0.71        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.47/0.71        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.47/0.71  thf('41', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(fc9_tops_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.47/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.71       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.47/0.71  thf('42', plain,
% 0.47/0.71      (![X13 : $i, X14 : $i]:
% 0.47/0.71         (~ (l1_pre_topc @ X13)
% 0.47/0.71          | ~ (v2_pre_topc @ X13)
% 0.47/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.47/0.71          | (v3_pre_topc @ (k1_tops_1 @ X13 @ X14) @ X13))),
% 0.47/0.71      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.47/0.71  thf('43', plain,
% 0.47/0.71      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.47/0.71        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.71  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('46', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.47/0.71      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.47/0.71  thf('47', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.47/0.71      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.71  thf('48', plain,
% 0.47/0.71      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.47/0.71        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['40', '46', '47'])).
% 0.47/0.71  thf('49', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.47/0.71      inference('clc', [status(thm)], ['9', '10'])).
% 0.47/0.71  thf('50', plain,
% 0.47/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.47/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.71  thf('51', plain,
% 0.47/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.47/0.71          | ~ (r2_hidden @ X21 @ (k1_tops_1 @ X22 @ X23))
% 0.47/0.71          | (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.47/0.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.47/0.71          | ~ (l1_pre_topc @ X22)
% 0.47/0.71          | ~ (v2_pre_topc @ X22)
% 0.47/0.71          | (v2_struct_0 @ X22))),
% 0.47/0.71      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.47/0.71  thf('52', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_A)
% 0.47/0.71          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.71          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.47/0.71          | ~ (r2_hidden @ X0 @ 
% 0.47/0.71               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.71  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('55', plain,
% 0.47/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.47/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.71  thf(t55_tops_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( l1_pre_topc @ B ) =>
% 0.47/0.71           ( ![C:$i]:
% 0.47/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71               ( ![D:$i]:
% 0.47/0.71                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.47/0.71                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.47/0.71                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.47/0.71                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.47/0.71                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.71  thf('56', plain,
% 0.47/0.71      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.71         (~ (l1_pre_topc @ X17)
% 0.47/0.71          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.71          | ~ (v3_pre_topc @ X18 @ X17)
% 0.47/0.71          | ((k1_tops_1 @ X17 @ X18) = (X18))
% 0.47/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.47/0.71          | ~ (l1_pre_topc @ X20)
% 0.47/0.71          | ~ (v2_pre_topc @ X20))),
% 0.47/0.71      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.47/0.71  thf('57', plain,
% 0.47/0.71      ((![X17 : $i, X18 : $i]:
% 0.47/0.71          (~ (l1_pre_topc @ X17)
% 0.47/0.71           | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.71           | ~ (v3_pre_topc @ X18 @ X17)
% 0.47/0.71           | ((k1_tops_1 @ X17 @ X18) = (X18))))
% 0.47/0.71         <= ((![X17 : $i, X18 : $i]:
% 0.47/0.71                (~ (l1_pre_topc @ X17)
% 0.47/0.71                 | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.71                 | ~ (v3_pre_topc @ X18 @ X17)
% 0.47/0.71                 | ((k1_tops_1 @ X17 @ X18) = (X18)))))),
% 0.47/0.71      inference('split', [status(esa)], ['56'])).
% 0.47/0.71  thf('58', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('59', plain,
% 0.47/0.71      ((![X19 : $i, X20 : $i]:
% 0.47/0.71          (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.47/0.71           | ~ (l1_pre_topc @ X20)
% 0.47/0.71           | ~ (v2_pre_topc @ X20)))
% 0.47/0.71         <= ((![X19 : $i, X20 : $i]:
% 0.47/0.71                (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.47/0.71                 | ~ (l1_pre_topc @ X20)
% 0.47/0.71                 | ~ (v2_pre_topc @ X20))))),
% 0.47/0.71      inference('split', [status(esa)], ['56'])).
% 0.47/0.71  thf('60', plain,
% 0.47/0.71      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.47/0.71         <= ((![X19 : $i, X20 : $i]:
% 0.47/0.71                (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.47/0.71                 | ~ (l1_pre_topc @ X20)
% 0.47/0.71                 | ~ (v2_pre_topc @ X20))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.71  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('63', plain,
% 0.47/0.71      (~
% 0.47/0.71       (![X19 : $i, X20 : $i]:
% 0.47/0.71          (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.47/0.71           | ~ (l1_pre_topc @ X20)
% 0.47/0.71           | ~ (v2_pre_topc @ X20)))),
% 0.47/0.71      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.47/0.71  thf('64', plain,
% 0.47/0.71      ((![X17 : $i, X18 : $i]:
% 0.47/0.71          (~ (l1_pre_topc @ X17)
% 0.47/0.71           | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.71           | ~ (v3_pre_topc @ X18 @ X17)
% 0.47/0.71           | ((k1_tops_1 @ X17 @ X18) = (X18)))) | 
% 0.47/0.71       (![X19 : $i, X20 : $i]:
% 0.47/0.71          (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.47/0.71           | ~ (l1_pre_topc @ X20)
% 0.47/0.71           | ~ (v2_pre_topc @ X20)))),
% 0.47/0.71      inference('split', [status(esa)], ['56'])).
% 0.47/0.71  thf('65', plain,
% 0.47/0.71      ((![X17 : $i, X18 : $i]:
% 0.47/0.71          (~ (l1_pre_topc @ X17)
% 0.47/0.71           | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.71           | ~ (v3_pre_topc @ X18 @ X17)
% 0.47/0.71           | ((k1_tops_1 @ X17 @ X18) = (X18))))),
% 0.47/0.71      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.47/0.71  thf('66', plain,
% 0.47/0.71      (![X17 : $i, X18 : $i]:
% 0.47/0.71         (~ (l1_pre_topc @ X17)
% 0.47/0.71          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.71          | ~ (v3_pre_topc @ X18 @ X17)
% 0.47/0.71          | ((k1_tops_1 @ X17 @ X18) = (X18)))),
% 0.47/0.71      inference('simpl_trail', [status(thm)], ['57', '65'])).
% 0.47/0.71  thf('67', plain,
% 0.47/0.71      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.47/0.71          = (k1_tops_1 @ sk_A @ sk_C_1))
% 0.47/0.71        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.47/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['55', '66'])).
% 0.47/0.71  thf('68', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.47/0.71      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.47/0.71  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('70', plain,
% 0.47/0.71      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.47/0.71         = (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.47/0.71      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.47/0.71  thf('71', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_A)
% 0.47/0.71          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.47/0.71          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('demod', [status(thm)], ['52', '53', '54', '70'])).
% 0.47/0.71  thf('72', plain,
% 0.47/0.71      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.71        | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.47/0.71        | (v2_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['49', '71'])).
% 0.47/0.71  thf('73', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('74', plain,
% 0.47/0.71      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.47/0.71        | (v2_struct_0 @ sk_A))),
% 0.47/0.71      inference('demod', [status(thm)], ['72', '73'])).
% 0.47/0.71  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('76', plain, ((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)),
% 0.47/0.71      inference('clc', [status(thm)], ['74', '75'])).
% 0.47/0.71  thf('77', plain, ((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.47/0.71      inference('demod', [status(thm)], ['48', '76'])).
% 0.47/0.71  thf('78', plain, ($false), inference('demod', [status(thm)], ['18', '77'])).
% 0.47/0.71  
% 0.47/0.71  % SZS output end Refutation
% 0.47/0.71  
% 0.47/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
