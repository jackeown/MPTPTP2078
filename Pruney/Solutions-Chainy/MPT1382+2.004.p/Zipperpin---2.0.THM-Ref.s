%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aqUgYFrUy6

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:50 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 264 expanded)
%              Number of leaves         :   25 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  881 (4341 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ ( k1_tops_1 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
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
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X34: $i] :
      ( ~ ( r1_tarski @ X34 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X34 @ sk_A )
      | ~ ( m1_connsp_2 @ X34 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X34 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X19 @ X20 ) @ X19 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r2_hidden @ X31 @ ( k1_tops_1 @ X32 @ X33 ) )
      | ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X28 )
        = X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('57',plain,
    ( ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( v3_pre_topc @ X28 @ X27 )
        | ( ( k1_tops_1 @ X27 @ X28 )
          = X28 ) )
   <= ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( v3_pre_topc @ X28 @ X27 )
        | ( ( k1_tops_1 @ X27 @ X28 )
          = X28 ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(split,[status(esa)],['56'])).

thf('60',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ~ ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( v3_pre_topc @ X28 @ X27 )
        | ( ( k1_tops_1 @ X27 @ X28 )
          = X28 ) )
    | ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(split,[status(esa)],['56'])).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X28 )
        = X28 ) ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X28 )
        = X28 ) ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aqUgYFrUy6
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.13/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.34  % Solved by: fo/fo7.sh
% 1.13/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.34  % done 842 iterations in 0.883s
% 1.13/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.34  % SZS output start Refutation
% 1.13/1.34  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 1.13/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.34  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.13/1.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.13/1.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.13/1.34  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.13/1.34  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.13/1.34  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.13/1.34  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.13/1.34  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.13/1.34  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.13/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.13/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.13/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.34  thf(t7_connsp_2, conjecture,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.34       ( ![B:$i]:
% 1.13/1.34         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.34           ( ![C:$i]:
% 1.13/1.34             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.34               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 1.13/1.34                    ( ![D:$i]:
% 1.13/1.34                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.13/1.34                          ( m1_subset_1 @
% 1.13/1.34                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.34                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 1.13/1.34                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.13/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.34    (~( ![A:$i]:
% 1.13/1.34        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.13/1.34            ( l1_pre_topc @ A ) ) =>
% 1.13/1.34          ( ![B:$i]:
% 1.13/1.34            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.34              ( ![C:$i]:
% 1.13/1.34                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.34                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 1.13/1.34                       ( ![D:$i]:
% 1.13/1.34                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.13/1.34                             ( m1_subset_1 @
% 1.13/1.34                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.34                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 1.13/1.34                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.13/1.34    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 1.13/1.34  thf('0', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('1', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf(d1_connsp_2, axiom,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.34       ( ![B:$i]:
% 1.13/1.34         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.34           ( ![C:$i]:
% 1.13/1.34             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.34               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 1.13/1.34                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.13/1.34  thf('2', plain,
% 1.13/1.34      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.13/1.34         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 1.13/1.34          | ~ (m1_connsp_2 @ X33 @ X32 @ X31)
% 1.13/1.34          | (r2_hidden @ X31 @ (k1_tops_1 @ X32 @ X33))
% 1.13/1.34          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.13/1.34          | ~ (l1_pre_topc @ X32)
% 1.13/1.34          | ~ (v2_pre_topc @ X32)
% 1.13/1.34          | (v2_struct_0 @ X32))),
% 1.13/1.34      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.13/1.34  thf('3', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((v2_struct_0 @ sk_A)
% 1.13/1.34          | ~ (v2_pre_topc @ sk_A)
% 1.13/1.34          | ~ (l1_pre_topc @ sk_A)
% 1.13/1.34          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.13/1.34          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['1', '2'])).
% 1.13/1.34  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('6', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((v2_struct_0 @ sk_A)
% 1.13/1.34          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.13/1.34          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.13/1.34  thf('7', plain,
% 1.13/1.34      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.13/1.34        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.13/1.34        | (v2_struct_0 @ sk_A))),
% 1.13/1.34      inference('sup-', [status(thm)], ['0', '6'])).
% 1.13/1.34  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('9', plain,
% 1.13/1.34      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 1.13/1.34      inference('demod', [status(thm)], ['7', '8'])).
% 1.13/1.34  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('11', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.13/1.34      inference('clc', [status(thm)], ['9', '10'])).
% 1.13/1.34  thf(d10_xboole_0, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.13/1.34  thf('12', plain,
% 1.13/1.34      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.13/1.34      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.13/1.34  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.13/1.34      inference('simplify', [status(thm)], ['12'])).
% 1.13/1.34  thf(t3_subset, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.13/1.34  thf('14', plain,
% 1.13/1.34      (![X10 : $i, X12 : $i]:
% 1.13/1.34         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.13/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.13/1.34  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['13', '14'])).
% 1.13/1.34  thf(t5_subset, axiom,
% 1.13/1.34    (![A:$i,B:$i,C:$i]:
% 1.13/1.34     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.13/1.34          ( v1_xboole_0 @ C ) ) ))).
% 1.13/1.34  thf('16', plain,
% 1.13/1.34      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.34         (~ (r2_hidden @ X16 @ X17)
% 1.13/1.34          | ~ (v1_xboole_0 @ X18)
% 1.13/1.34          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.13/1.34      inference('cnf', [status(esa)], [t5_subset])).
% 1.13/1.34  thf('17', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.13/1.34      inference('sup-', [status(thm)], ['15', '16'])).
% 1.13/1.34  thf('18', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['11', '17'])).
% 1.13/1.34  thf(d3_tarski, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( r1_tarski @ A @ B ) <=>
% 1.13/1.34       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.13/1.34  thf('19', plain,
% 1.13/1.34      (![X1 : $i, X3 : $i]:
% 1.13/1.34         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.13/1.34      inference('cnf', [status(esa)], [d3_tarski])).
% 1.13/1.34  thf('20', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf(t44_tops_1, axiom,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( l1_pre_topc @ A ) =>
% 1.13/1.34       ( ![B:$i]:
% 1.13/1.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.34           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.13/1.34  thf('21', plain,
% 1.13/1.34      (![X21 : $i, X22 : $i]:
% 1.13/1.34         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.13/1.34          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ X21)
% 1.13/1.34          | ~ (l1_pre_topc @ X22))),
% 1.13/1.34      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.13/1.34  thf('22', plain,
% 1.13/1.34      ((~ (l1_pre_topc @ sk_A)
% 1.13/1.34        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['20', '21'])).
% 1.13/1.34  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('24', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 1.13/1.34      inference('demod', [status(thm)], ['22', '23'])).
% 1.13/1.34  thf('25', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.34         (~ (r2_hidden @ X0 @ X1)
% 1.13/1.34          | (r2_hidden @ X0 @ X2)
% 1.13/1.34          | ~ (r1_tarski @ X1 @ X2))),
% 1.13/1.34      inference('cnf', [status(esa)], [d3_tarski])).
% 1.13/1.34  thf('26', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((r2_hidden @ X0 @ sk_C_1)
% 1.13/1.34          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['24', '25'])).
% 1.13/1.34  thf('27', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.13/1.34          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['19', '26'])).
% 1.13/1.34  thf('28', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('29', plain,
% 1.13/1.34      (![X10 : $i, X11 : $i]:
% 1.13/1.34         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.13/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.13/1.34  thf('30', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.13/1.34      inference('sup-', [status(thm)], ['28', '29'])).
% 1.13/1.34  thf('31', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.34         (~ (r2_hidden @ X0 @ X1)
% 1.13/1.34          | (r2_hidden @ X0 @ X2)
% 1.13/1.34          | ~ (r1_tarski @ X1 @ X2))),
% 1.13/1.34      inference('cnf', [status(esa)], [d3_tarski])).
% 1.13/1.34  thf('32', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['30', '31'])).
% 1.13/1.34  thf('33', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.13/1.34          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 1.13/1.34             (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['27', '32'])).
% 1.13/1.34  thf('34', plain,
% 1.13/1.34      (![X1 : $i, X3 : $i]:
% 1.13/1.34         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.13/1.34      inference('cnf', [status(esa)], [d3_tarski])).
% 1.13/1.34  thf('35', plain,
% 1.13/1.34      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 1.13/1.34        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['33', '34'])).
% 1.13/1.34  thf('36', plain,
% 1.13/1.34      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 1.13/1.34      inference('simplify', [status(thm)], ['35'])).
% 1.13/1.34  thf('37', plain,
% 1.13/1.34      (![X10 : $i, X12 : $i]:
% 1.13/1.34         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.13/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.13/1.34  thf('38', plain,
% 1.13/1.34      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.13/1.34        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['36', '37'])).
% 1.13/1.34  thf('39', plain,
% 1.13/1.34      (![X34 : $i]:
% 1.13/1.34         (~ (r1_tarski @ X34 @ sk_C_1)
% 1.13/1.34          | ~ (v3_pre_topc @ X34 @ sk_A)
% 1.13/1.34          | ~ (m1_connsp_2 @ X34 @ sk_A @ sk_B)
% 1.13/1.34          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.13/1.34          | (v1_xboole_0 @ X34))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('40', plain,
% 1.13/1.34      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.13/1.34        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 1.13/1.34        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.13/1.34        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 1.13/1.34      inference('sup-', [status(thm)], ['38', '39'])).
% 1.13/1.34  thf('41', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf(fc9_tops_1, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.13/1.34         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.34       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.13/1.34  thf('42', plain,
% 1.13/1.34      (![X19 : $i, X20 : $i]:
% 1.13/1.34         (~ (l1_pre_topc @ X19)
% 1.13/1.34          | ~ (v2_pre_topc @ X19)
% 1.13/1.34          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.13/1.34          | (v3_pre_topc @ (k1_tops_1 @ X19 @ X20) @ X19))),
% 1.13/1.34      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.13/1.34  thf('43', plain,
% 1.13/1.34      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.13/1.34        | ~ (v2_pre_topc @ sk_A)
% 1.13/1.34        | ~ (l1_pre_topc @ sk_A))),
% 1.13/1.34      inference('sup-', [status(thm)], ['41', '42'])).
% 1.13/1.34  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('46', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 1.13/1.34      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.13/1.34  thf('47', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 1.13/1.34      inference('demod', [status(thm)], ['22', '23'])).
% 1.13/1.34  thf('48', plain,
% 1.13/1.34      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.13/1.34        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B))),
% 1.13/1.34      inference('demod', [status(thm)], ['40', '46', '47'])).
% 1.13/1.34  thf('49', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.13/1.34      inference('clc', [status(thm)], ['9', '10'])).
% 1.13/1.34  thf('50', plain,
% 1.13/1.34      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.13/1.34        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['36', '37'])).
% 1.13/1.34  thf('51', plain,
% 1.13/1.34      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.13/1.34         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 1.13/1.34          | ~ (r2_hidden @ X31 @ (k1_tops_1 @ X32 @ X33))
% 1.13/1.34          | (m1_connsp_2 @ X33 @ X32 @ X31)
% 1.13/1.34          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.13/1.34          | ~ (l1_pre_topc @ X32)
% 1.13/1.34          | ~ (v2_pre_topc @ X32)
% 1.13/1.34          | (v2_struct_0 @ X32))),
% 1.13/1.34      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.13/1.34  thf('52', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((v2_struct_0 @ sk_A)
% 1.13/1.34          | ~ (v2_pre_topc @ sk_A)
% 1.13/1.34          | ~ (l1_pre_topc @ sk_A)
% 1.13/1.34          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 1.13/1.34          | ~ (r2_hidden @ X0 @ 
% 1.13/1.34               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['50', '51'])).
% 1.13/1.34  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('55', plain,
% 1.13/1.34      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.13/1.34        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['36', '37'])).
% 1.13/1.34  thf(t55_tops_1, axiom,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.34       ( ![B:$i]:
% 1.13/1.34         ( ( l1_pre_topc @ B ) =>
% 1.13/1.34           ( ![C:$i]:
% 1.13/1.34             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.34               ( ![D:$i]:
% 1.13/1.34                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.13/1.34                   ( ( ( v3_pre_topc @ D @ B ) =>
% 1.13/1.34                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 1.13/1.34                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 1.13/1.34                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 1.13/1.34  thf('56', plain,
% 1.13/1.34      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.13/1.34         (~ (l1_pre_topc @ X27)
% 1.13/1.34          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.13/1.34          | ~ (v3_pre_topc @ X28 @ X27)
% 1.13/1.34          | ((k1_tops_1 @ X27 @ X28) = (X28))
% 1.13/1.34          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.13/1.34          | ~ (l1_pre_topc @ X30)
% 1.13/1.34          | ~ (v2_pre_topc @ X30))),
% 1.13/1.34      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.13/1.34  thf('57', plain,
% 1.13/1.34      ((![X27 : $i, X28 : $i]:
% 1.13/1.34          (~ (l1_pre_topc @ X27)
% 1.13/1.34           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.13/1.34           | ~ (v3_pre_topc @ X28 @ X27)
% 1.13/1.34           | ((k1_tops_1 @ X27 @ X28) = (X28))))
% 1.13/1.34         <= ((![X27 : $i, X28 : $i]:
% 1.13/1.34                (~ (l1_pre_topc @ X27)
% 1.13/1.34                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.13/1.34                 | ~ (v3_pre_topc @ X28 @ X27)
% 1.13/1.34                 | ((k1_tops_1 @ X27 @ X28) = (X28)))))),
% 1.13/1.34      inference('split', [status(esa)], ['56'])).
% 1.13/1.34  thf('58', plain,
% 1.13/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('59', plain,
% 1.13/1.34      ((![X29 : $i, X30 : $i]:
% 1.13/1.34          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.13/1.34           | ~ (l1_pre_topc @ X30)
% 1.13/1.34           | ~ (v2_pre_topc @ X30)))
% 1.13/1.34         <= ((![X29 : $i, X30 : $i]:
% 1.13/1.34                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.13/1.34                 | ~ (l1_pre_topc @ X30)
% 1.13/1.34                 | ~ (v2_pre_topc @ X30))))),
% 1.13/1.34      inference('split', [status(esa)], ['56'])).
% 1.13/1.34  thf('60', plain,
% 1.13/1.34      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 1.13/1.34         <= ((![X29 : $i, X30 : $i]:
% 1.13/1.34                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.13/1.34                 | ~ (l1_pre_topc @ X30)
% 1.13/1.34                 | ~ (v2_pre_topc @ X30))))),
% 1.13/1.34      inference('sup-', [status(thm)], ['58', '59'])).
% 1.13/1.34  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('63', plain,
% 1.13/1.34      (~
% 1.13/1.34       (![X29 : $i, X30 : $i]:
% 1.13/1.34          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.13/1.34           | ~ (l1_pre_topc @ X30)
% 1.13/1.34           | ~ (v2_pre_topc @ X30)))),
% 1.13/1.34      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.13/1.34  thf('64', plain,
% 1.13/1.34      ((![X27 : $i, X28 : $i]:
% 1.13/1.34          (~ (l1_pre_topc @ X27)
% 1.13/1.34           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.13/1.34           | ~ (v3_pre_topc @ X28 @ X27)
% 1.13/1.34           | ((k1_tops_1 @ X27 @ X28) = (X28)))) | 
% 1.13/1.34       (![X29 : $i, X30 : $i]:
% 1.13/1.34          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.13/1.34           | ~ (l1_pre_topc @ X30)
% 1.13/1.34           | ~ (v2_pre_topc @ X30)))),
% 1.13/1.34      inference('split', [status(esa)], ['56'])).
% 1.13/1.34  thf('65', plain,
% 1.13/1.34      ((![X27 : $i, X28 : $i]:
% 1.13/1.34          (~ (l1_pre_topc @ X27)
% 1.13/1.34           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.13/1.34           | ~ (v3_pre_topc @ X28 @ X27)
% 1.13/1.34           | ((k1_tops_1 @ X27 @ X28) = (X28))))),
% 1.13/1.34      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 1.13/1.34  thf('66', plain,
% 1.13/1.34      (![X27 : $i, X28 : $i]:
% 1.13/1.34         (~ (l1_pre_topc @ X27)
% 1.13/1.34          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.13/1.34          | ~ (v3_pre_topc @ X28 @ X27)
% 1.13/1.34          | ((k1_tops_1 @ X27 @ X28) = (X28)))),
% 1.13/1.34      inference('simpl_trail', [status(thm)], ['57', '65'])).
% 1.13/1.34  thf('67', plain,
% 1.13/1.34      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.13/1.34          = (k1_tops_1 @ sk_A @ sk_C_1))
% 1.13/1.34        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.13/1.34        | ~ (l1_pre_topc @ sk_A))),
% 1.13/1.34      inference('sup-', [status(thm)], ['55', '66'])).
% 1.13/1.34  thf('68', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 1.13/1.34      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.13/1.34  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('70', plain,
% 1.13/1.34      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.13/1.34         = (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.13/1.34  thf('71', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         ((v2_struct_0 @ sk_A)
% 1.13/1.34          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 1.13/1.34          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.13/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.34      inference('demod', [status(thm)], ['52', '53', '54', '70'])).
% 1.13/1.34  thf('72', plain,
% 1.13/1.34      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.13/1.34        | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 1.13/1.34        | (v2_struct_0 @ sk_A))),
% 1.13/1.34      inference('sup-', [status(thm)], ['49', '71'])).
% 1.13/1.34  thf('73', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('74', plain,
% 1.13/1.34      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 1.13/1.34        | (v2_struct_0 @ sk_A))),
% 1.13/1.34      inference('demod', [status(thm)], ['72', '73'])).
% 1.13/1.34  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('76', plain, ((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)),
% 1.13/1.34      inference('clc', [status(thm)], ['74', '75'])).
% 1.13/1.34  thf('77', plain, ((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.13/1.34      inference('demod', [status(thm)], ['48', '76'])).
% 1.13/1.34  thf('78', plain, ($false), inference('demod', [status(thm)], ['18', '77'])).
% 1.13/1.34  
% 1.13/1.34  % SZS output end Refutation
% 1.13/1.34  
% 1.13/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
