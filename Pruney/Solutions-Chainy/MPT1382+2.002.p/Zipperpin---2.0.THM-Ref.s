%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kuMHqQc5Z2

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:49 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 227 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  976 (4104 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X29: $i] :
      ( ~ ( r1_tarski @ X29 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X29 @ sk_A )
      | ~ ( m1_connsp_2 @ X29 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('9',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','12'])).

thf('14',plain,(
    m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ( m1_connsp_2 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','37'])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['38','46'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('67',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_connsp_2 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['47','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kuMHqQc5Z2
% 0.14/0.37  % Computer   : n010.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 12:11:15 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.80/1.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.80/1.98  % Solved by: fo/fo7.sh
% 1.80/1.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/1.98  % done 1147 iterations in 1.503s
% 1.80/1.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.80/1.98  % SZS output start Refutation
% 1.80/1.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.80/1.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.80/1.98  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.80/1.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.80/1.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.80/1.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.80/1.98  thf(sk_A_type, type, sk_A: $i).
% 1.80/1.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.80/1.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.80/1.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.80/1.98  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.80/1.98  thf(sk_B_type, type, sk_B: $i).
% 1.80/1.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.80/1.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.80/1.98  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 1.80/1.98  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.80/1.98  thf(t7_connsp_2, conjecture,
% 1.80/1.98    (![A:$i]:
% 1.80/1.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.80/1.98       ( ![B:$i]:
% 1.80/1.98         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.80/1.98           ( ![C:$i]:
% 1.80/1.98             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/1.98               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 1.80/1.98                    ( ![D:$i]:
% 1.80/1.98                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.80/1.98                          ( m1_subset_1 @
% 1.80/1.98                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.80/1.98                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 1.80/1.98                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.80/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.80/1.98    (~( ![A:$i]:
% 1.80/1.98        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.80/1.98            ( l1_pre_topc @ A ) ) =>
% 1.80/1.98          ( ![B:$i]:
% 1.80/1.98            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.80/1.98              ( ![C:$i]:
% 1.80/1.98                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/1.98                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 1.80/1.98                       ( ![D:$i]:
% 1.80/1.98                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.80/1.98                             ( m1_subset_1 @
% 1.80/1.98                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.80/1.98                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 1.80/1.98                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.80/1.98    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 1.80/1.98  thf('0', plain,
% 1.80/1.98      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf(dt_k1_tops_1, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ( ( l1_pre_topc @ A ) & 
% 1.80/1.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.80/1.98       ( m1_subset_1 @
% 1.80/1.98         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.80/1.98  thf('1', plain,
% 1.80/1.98      (![X16 : $i, X17 : $i]:
% 1.80/1.98         (~ (l1_pre_topc @ X16)
% 1.80/1.98          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.80/1.98          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 1.80/1.98             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 1.80/1.98      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.80/1.98  thf('2', plain,
% 1.80/1.98      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.80/1.98         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.80/1.98        | ~ (l1_pre_topc @ sk_A))),
% 1.80/1.98      inference('sup-', [status(thm)], ['0', '1'])).
% 1.80/1.98  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('4', plain,
% 1.80/1.98      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.80/1.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('demod', [status(thm)], ['2', '3'])).
% 1.80/1.98  thf('5', plain,
% 1.80/1.98      (![X29 : $i]:
% 1.80/1.98         (~ (r1_tarski @ X29 @ sk_C_1)
% 1.80/1.98          | ~ (v3_pre_topc @ X29 @ sk_A)
% 1.80/1.98          | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_B)
% 1.80/1.98          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.80/1.98          | (v1_xboole_0 @ X29))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('6', plain,
% 1.80/1.98      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.80/1.98        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 1.80/1.98        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.80/1.98        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 1.80/1.98      inference('sup-', [status(thm)], ['4', '5'])).
% 1.80/1.98  thf('7', plain,
% 1.80/1.98      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf(fc9_tops_1, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.80/1.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.80/1.98       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.80/1.98  thf('8', plain,
% 1.80/1.98      (![X18 : $i, X19 : $i]:
% 1.80/1.98         (~ (l1_pre_topc @ X18)
% 1.80/1.98          | ~ (v2_pre_topc @ X18)
% 1.80/1.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.80/1.98          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 1.80/1.98      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.80/1.98  thf('9', plain,
% 1.80/1.98      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.80/1.98        | ~ (v2_pre_topc @ sk_A)
% 1.80/1.98        | ~ (l1_pre_topc @ sk_A))),
% 1.80/1.98      inference('sup-', [status(thm)], ['7', '8'])).
% 1.80/1.98  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('12', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 1.80/1.98      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.80/1.98  thf('13', plain,
% 1.80/1.98      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.80/1.98        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 1.80/1.98        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 1.80/1.98      inference('demod', [status(thm)], ['6', '12'])).
% 1.80/1.98  thf('14', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('15', plain,
% 1.80/1.98      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf(d1_connsp_2, axiom,
% 1.80/1.98    (![A:$i]:
% 1.80/1.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.80/1.98       ( ![B:$i]:
% 1.80/1.98         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.80/1.98           ( ![C:$i]:
% 1.80/1.98             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/1.98               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 1.80/1.98                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.80/1.98  thf('16', plain,
% 1.80/1.98      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.80/1.98         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.80/1.98          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 1.80/1.98          | (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 1.80/1.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.80/1.98          | ~ (l1_pre_topc @ X21)
% 1.80/1.98          | ~ (v2_pre_topc @ X21)
% 1.80/1.98          | (v2_struct_0 @ X21))),
% 1.80/1.98      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.80/1.98  thf('17', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((v2_struct_0 @ sk_A)
% 1.80/1.98          | ~ (v2_pre_topc @ sk_A)
% 1.80/1.98          | ~ (l1_pre_topc @ sk_A)
% 1.80/1.98          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.80/1.98          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 1.80/1.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['15', '16'])).
% 1.80/1.98  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('20', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((v2_struct_0 @ sk_A)
% 1.80/1.98          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.80/1.98          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 1.80/1.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.80/1.98  thf('21', plain,
% 1.80/1.98      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.80/1.98        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.80/1.98        | (v2_struct_0 @ sk_A))),
% 1.80/1.98      inference('sup-', [status(thm)], ['14', '20'])).
% 1.80/1.98  thf('22', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('23', plain,
% 1.80/1.98      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 1.80/1.98      inference('demod', [status(thm)], ['21', '22'])).
% 1.80/1.98  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('25', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.80/1.98      inference('clc', [status(thm)], ['23', '24'])).
% 1.80/1.98  thf('26', plain,
% 1.80/1.98      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.80/1.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('demod', [status(thm)], ['2', '3'])).
% 1.80/1.98  thf(t5_connsp_2, axiom,
% 1.80/1.98    (![A:$i]:
% 1.80/1.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.80/1.98       ( ![B:$i]:
% 1.80/1.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/1.98           ( ![C:$i]:
% 1.80/1.98             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.80/1.98               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 1.80/1.98                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 1.80/1.98  thf('27', plain,
% 1.80/1.98      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.80/1.98         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.80/1.98          | ~ (v3_pre_topc @ X23 @ X24)
% 1.80/1.98          | ~ (r2_hidden @ X25 @ X23)
% 1.80/1.98          | (m1_connsp_2 @ X23 @ X24 @ X25)
% 1.80/1.98          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 1.80/1.98          | ~ (l1_pre_topc @ X24)
% 1.80/1.98          | ~ (v2_pre_topc @ X24)
% 1.80/1.98          | (v2_struct_0 @ X24))),
% 1.80/1.98      inference('cnf', [status(esa)], [t5_connsp_2])).
% 1.80/1.98  thf('28', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((v2_struct_0 @ sk_A)
% 1.80/1.98          | ~ (v2_pre_topc @ sk_A)
% 1.80/1.98          | ~ (l1_pre_topc @ sk_A)
% 1.80/1.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.80/1.98          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 1.80/1.98          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.80/1.98          | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))),
% 1.80/1.98      inference('sup-', [status(thm)], ['26', '27'])).
% 1.80/1.98  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('31', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 1.80/1.98      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.80/1.98  thf('32', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((v2_struct_0 @ sk_A)
% 1.80/1.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.80/1.98          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 1.80/1.98          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.80/1.98      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 1.80/1.98  thf('33', plain,
% 1.80/1.98      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 1.80/1.98        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.80/1.98        | (v2_struct_0 @ sk_A))),
% 1.80/1.98      inference('sup-', [status(thm)], ['25', '32'])).
% 1.80/1.98  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('35', plain,
% 1.80/1.98      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 1.80/1.98        | (v2_struct_0 @ sk_A))),
% 1.80/1.98      inference('demod', [status(thm)], ['33', '34'])).
% 1.80/1.98  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('37', plain, ((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)),
% 1.80/1.98      inference('clc', [status(thm)], ['35', '36'])).
% 1.80/1.98  thf('38', plain,
% 1.80/1.98      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.80/1.98        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 1.80/1.98      inference('demod', [status(thm)], ['13', '37'])).
% 1.80/1.98  thf('39', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.80/1.98      inference('clc', [status(thm)], ['23', '24'])).
% 1.80/1.98  thf(d10_xboole_0, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.80/1.98  thf('40', plain,
% 1.80/1.98      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.80/1.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.80/1.98  thf('41', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.80/1.98      inference('simplify', [status(thm)], ['40'])).
% 1.80/1.98  thf(t3_subset, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.80/1.98  thf('42', plain,
% 1.80/1.98      (![X7 : $i, X9 : $i]:
% 1.80/1.98         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.80/1.98      inference('cnf', [status(esa)], [t3_subset])).
% 1.80/1.98  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.80/1.98      inference('sup-', [status(thm)], ['41', '42'])).
% 1.80/1.98  thf(t5_subset, axiom,
% 1.80/1.98    (![A:$i,B:$i,C:$i]:
% 1.80/1.98     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.80/1.98          ( v1_xboole_0 @ C ) ) ))).
% 1.80/1.98  thf('44', plain,
% 1.80/1.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.80/1.98         (~ (r2_hidden @ X13 @ X14)
% 1.80/1.98          | ~ (v1_xboole_0 @ X15)
% 1.80/1.98          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.80/1.98      inference('cnf', [status(esa)], [t5_subset])).
% 1.80/1.98  thf('45', plain,
% 1.80/1.98      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.80/1.98      inference('sup-', [status(thm)], ['43', '44'])).
% 1.80/1.98  thf('46', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.80/1.98      inference('sup-', [status(thm)], ['39', '45'])).
% 1.80/1.98  thf('47', plain, (~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 1.80/1.98      inference('clc', [status(thm)], ['38', '46'])).
% 1.80/1.98  thf(d3_tarski, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ( r1_tarski @ A @ B ) <=>
% 1.80/1.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.80/1.98  thf('48', plain,
% 1.80/1.98      (![X1 : $i, X3 : $i]:
% 1.80/1.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.80/1.98      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/1.98  thf('49', plain,
% 1.80/1.98      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.80/1.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('demod', [status(thm)], ['2', '3'])).
% 1.80/1.98  thf(t4_subset, axiom,
% 1.80/1.98    (![A:$i,B:$i,C:$i]:
% 1.80/1.98     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.80/1.98       ( m1_subset_1 @ A @ C ) ))).
% 1.80/1.98  thf('50', plain,
% 1.80/1.98      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.80/1.98         (~ (r2_hidden @ X10 @ X11)
% 1.80/1.98          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.80/1.98          | (m1_subset_1 @ X10 @ X12))),
% 1.80/1.98      inference('cnf', [status(esa)], [t4_subset])).
% 1.80/1.98  thf('51', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.80/1.98          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['49', '50'])).
% 1.80/1.98  thf('52', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.80/1.98          | (m1_subset_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 1.80/1.98             (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['48', '51'])).
% 1.80/1.98  thf('53', plain,
% 1.80/1.98      (![X1 : $i, X3 : $i]:
% 1.80/1.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.80/1.98      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/1.98  thf('54', plain,
% 1.80/1.98      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('55', plain,
% 1.80/1.98      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.80/1.98         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.80/1.98          | ~ (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 1.80/1.98          | (m1_connsp_2 @ X22 @ X21 @ X20)
% 1.80/1.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.80/1.98          | ~ (l1_pre_topc @ X21)
% 1.80/1.98          | ~ (v2_pre_topc @ X21)
% 1.80/1.98          | (v2_struct_0 @ X21))),
% 1.80/1.98      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.80/1.98  thf('56', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((v2_struct_0 @ sk_A)
% 1.80/1.98          | ~ (v2_pre_topc @ sk_A)
% 1.80/1.98          | ~ (l1_pre_topc @ sk_A)
% 1.80/1.98          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 1.80/1.98          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.80/1.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['54', '55'])).
% 1.80/1.98  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('59', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((v2_struct_0 @ sk_A)
% 1.80/1.98          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 1.80/1.98          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.80/1.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.80/1.98  thf('60', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.80/1.98          | ~ (m1_subset_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 1.80/1.98               (u1_struct_0 @ sk_A))
% 1.80/1.98          | (m1_connsp_2 @ sk_C_1 @ sk_A @ 
% 1.80/1.98             (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 1.80/1.98          | (v2_struct_0 @ sk_A))),
% 1.80/1.98      inference('sup-', [status(thm)], ['53', '59'])).
% 1.80/1.98  thf('61', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.80/1.98          | (v2_struct_0 @ sk_A)
% 1.80/1.98          | (m1_connsp_2 @ sk_C_1 @ sk_A @ 
% 1.80/1.98             (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 1.80/1.98          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0))),
% 1.80/1.98      inference('sup-', [status(thm)], ['52', '60'])).
% 1.80/1.98  thf('62', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((m1_connsp_2 @ sk_C_1 @ sk_A @ 
% 1.80/1.98           (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 1.80/1.98          | (v2_struct_0 @ sk_A)
% 1.80/1.98          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0))),
% 1.80/1.98      inference('simplify', [status(thm)], ['61'])).
% 1.80/1.98  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('64', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.80/1.98          | (m1_connsp_2 @ sk_C_1 @ sk_A @ 
% 1.80/1.98             (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 1.80/1.98      inference('clc', [status(thm)], ['62', '63'])).
% 1.80/1.98  thf('65', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.80/1.98          | (m1_subset_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 1.80/1.98             (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['48', '51'])).
% 1.80/1.98  thf('66', plain,
% 1.80/1.98      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf(t6_connsp_2, axiom,
% 1.80/1.98    (![A:$i]:
% 1.80/1.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.80/1.98       ( ![B:$i]:
% 1.80/1.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/1.98           ( ![C:$i]:
% 1.80/1.98             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.80/1.98               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.80/1.98  thf('67', plain,
% 1.80/1.98      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.80/1.98         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.80/1.98          | ~ (m1_connsp_2 @ X26 @ X27 @ X28)
% 1.80/1.98          | (r2_hidden @ X28 @ X26)
% 1.80/1.98          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 1.80/1.98          | ~ (l1_pre_topc @ X27)
% 1.80/1.98          | ~ (v2_pre_topc @ X27)
% 1.80/1.98          | (v2_struct_0 @ X27))),
% 1.80/1.98      inference('cnf', [status(esa)], [t6_connsp_2])).
% 1.80/1.98  thf('68', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((v2_struct_0 @ sk_A)
% 1.80/1.98          | ~ (v2_pre_topc @ sk_A)
% 1.80/1.98          | ~ (l1_pre_topc @ sk_A)
% 1.80/1.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.80/1.98          | (r2_hidden @ X0 @ sk_C_1)
% 1.80/1.98          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 1.80/1.98      inference('sup-', [status(thm)], ['66', '67'])).
% 1.80/1.98  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('71', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((v2_struct_0 @ sk_A)
% 1.80/1.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.80/1.98          | (r2_hidden @ X0 @ sk_C_1)
% 1.80/1.98          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 1.80/1.98      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.80/1.98  thf('72', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.80/1.98          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ 
% 1.80/1.98               (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 1.80/1.98          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1)
% 1.80/1.98          | (v2_struct_0 @ sk_A))),
% 1.80/1.98      inference('sup-', [status(thm)], ['65', '71'])).
% 1.80/1.98  thf('73', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.80/1.98          | (v2_struct_0 @ sk_A)
% 1.80/1.98          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1)
% 1.80/1.98          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0))),
% 1.80/1.98      inference('sup-', [status(thm)], ['64', '72'])).
% 1.80/1.98  thf('74', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1)
% 1.80/1.98          | (v2_struct_0 @ sk_A)
% 1.80/1.98          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0))),
% 1.80/1.98      inference('simplify', [status(thm)], ['73'])).
% 1.80/1.98  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('76', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 1.80/1.98          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1))),
% 1.80/1.98      inference('clc', [status(thm)], ['74', '75'])).
% 1.80/1.98  thf('77', plain,
% 1.80/1.98      (![X1 : $i, X3 : $i]:
% 1.80/1.98         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.80/1.98      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/1.98  thf('78', plain,
% 1.80/1.98      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 1.80/1.98        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 1.80/1.98      inference('sup-', [status(thm)], ['76', '77'])).
% 1.80/1.98  thf('79', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 1.80/1.98      inference('simplify', [status(thm)], ['78'])).
% 1.80/1.98  thf('80', plain, ($false), inference('demod', [status(thm)], ['47', '79'])).
% 1.80/1.98  
% 1.80/1.98  % SZS output end Refutation
% 1.80/1.98  
% 1.80/1.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
