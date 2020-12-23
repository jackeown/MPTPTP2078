%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.krqYxNgvqP

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:50 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 202 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  800 (3839 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X19: $i] :
      ( ~ ( r1_tarski @ X19 @ sk_C )
      | ~ ( v3_pre_topc @ X19 @ sk_A )
      | ~ ( m1_connsp_2 @ X19 @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('23',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X8 @ X7 ) @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X9 )
      | ( ( k1_tops_1 @ X9 @ X10 )
        = X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('42',plain,
    ( ! [X9: $i,X10: $i] :
        ( ~ ( l1_pre_topc @ X9 )
        | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
        | ~ ( v3_pre_topc @ X10 @ X9 )
        | ( ( k1_tops_1 @ X9 @ X10 )
          = X10 ) )
   <= ! [X9: $i,X10: $i] :
        ( ~ ( l1_pre_topc @ X9 )
        | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
        | ~ ( v3_pre_topc @ X10 @ X9 )
        | ( ( k1_tops_1 @ X9 @ X10 )
          = X10 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X11: $i,X12: $i] :
        ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
        | ~ ( l1_pre_topc @ X12 )
        | ~ ( v2_pre_topc @ X12 ) )
   <= ! [X11: $i,X12: $i] :
        ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
        | ~ ( l1_pre_topc @ X12 )
        | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('49',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X11: $i,X12: $i] :
        ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
        | ~ ( l1_pre_topc @ X12 )
        | ~ ( v2_pre_topc @ X12 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ! [X11: $i,X12: $i] :
        ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
        | ~ ( l1_pre_topc @ X12 )
        | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ! [X9: $i,X10: $i] :
        ( ~ ( l1_pre_topc @ X9 )
        | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
        | ~ ( v3_pre_topc @ X10 @ X9 )
        | ( ( k1_tops_1 @ X9 @ X10 )
          = X10 ) )
    | ! [X11: $i,X12: $i] :
        ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
        | ~ ( l1_pre_topc @ X12 )
        | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X9 )
      | ( ( k1_tops_1 @ X9 @ X10 )
        = X10 ) ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X9 )
      | ( ( k1_tops_1 @ X9 @ X10 )
        = X10 ) ) ),
    inference(simpl_trail,[status(thm)],['42','54'])).

thf('56',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','55'])).

thf('57',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['33','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['13','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.krqYxNgvqP
% 0.15/0.37  % Computer   : n006.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 18:54:53 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.25/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.52  % Solved by: fo/fo7.sh
% 0.25/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.52  % done 72 iterations in 0.035s
% 0.25/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.52  % SZS output start Refutation
% 0.25/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.25/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.52  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.25/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.25/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.25/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.25/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.52  thf(t7_connsp_2, conjecture,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.52       ( ![B:$i]:
% 0.25/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.52           ( ![C:$i]:
% 0.25/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.52               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.25/0.52                    ( ![D:$i]:
% 0.25/0.52                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.25/0.52                          ( m1_subset_1 @
% 0.25/0.52                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.25/0.52                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.25/0.52                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.52    (~( ![A:$i]:
% 0.25/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.52            ( l1_pre_topc @ A ) ) =>
% 0.25/0.52          ( ![B:$i]:
% 0.25/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.52              ( ![C:$i]:
% 0.25/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.52                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.25/0.52                       ( ![D:$i]:
% 0.25/0.52                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.25/0.52                             ( m1_subset_1 @
% 0.25/0.52                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.25/0.52                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.25/0.52                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.25/0.52    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.25/0.52  thf('0', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('1', plain,
% 0.25/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(d1_connsp_2, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.52       ( ![B:$i]:
% 0.25/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.52           ( ![C:$i]:
% 0.25/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.52               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.25/0.52                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.25/0.52  thf('2', plain,
% 0.25/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.25/0.52         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.25/0.52          | ~ (m1_connsp_2 @ X15 @ X14 @ X13)
% 0.25/0.52          | (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.25/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.25/0.52          | ~ (l1_pre_topc @ X14)
% 0.25/0.52          | ~ (v2_pre_topc @ X14)
% 0.25/0.52          | (v2_struct_0 @ X14))),
% 0.25/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.25/0.52  thf('3', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((v2_struct_0 @ sk_A)
% 0.25/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.25/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.52  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('6', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((v2_struct_0 @ sk_A)
% 0.25/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.25/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.25/0.52  thf('7', plain,
% 0.25/0.52      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.25/0.52        | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52        | (v2_struct_0 @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['0', '6'])).
% 0.25/0.52  thf('8', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('9', plain,
% 0.25/0.52      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.25/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.25/0.52  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('11', plain, ((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.25/0.52      inference('clc', [status(thm)], ['9', '10'])).
% 0.25/0.52  thf(d1_xboole_0, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.25/0.52  thf('12', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.25/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.25/0.52  thf('13', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.25/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.25/0.52  thf('14', plain,
% 0.25/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(dt_k1_tops_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.25/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.25/0.52       ( m1_subset_1 @
% 0.25/0.52         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.25/0.52  thf('15', plain,
% 0.25/0.52      (![X3 : $i, X4 : $i]:
% 0.25/0.52         (~ (l1_pre_topc @ X3)
% 0.25/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.25/0.52          | (m1_subset_1 @ (k1_tops_1 @ X3 @ X4) @ 
% 0.25/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.25/0.52      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.25/0.52  thf('16', plain,
% 0.25/0.52      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.25/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.52  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('18', plain,
% 0.25/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.25/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.25/0.52  thf('19', plain,
% 0.25/0.52      (![X19 : $i]:
% 0.25/0.52         (~ (r1_tarski @ X19 @ sk_C)
% 0.25/0.52          | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.25/0.52          | ~ (m1_connsp_2 @ X19 @ sk_A @ sk_B_1)
% 0.25/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.52          | (v1_xboole_0 @ X19))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('20', plain,
% 0.25/0.52      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1)
% 0.25/0.52        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.25/0.52        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.25/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.52  thf('21', plain,
% 0.25/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(fc9_tops_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.25/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.25/0.52       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.25/0.52  thf('22', plain,
% 0.25/0.52      (![X5 : $i, X6 : $i]:
% 0.25/0.52         (~ (l1_pre_topc @ X5)
% 0.25/0.52          | ~ (v2_pre_topc @ X5)
% 0.25/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.25/0.52          | (v3_pre_topc @ (k1_tops_1 @ X5 @ X6) @ X5))),
% 0.25/0.52      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.25/0.52  thf('23', plain,
% 0.25/0.52      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.25/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.52  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('26', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.25/0.52      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.25/0.52  thf('27', plain,
% 0.25/0.52      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1)
% 0.25/0.52        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.25/0.52      inference('demod', [status(thm)], ['20', '26'])).
% 0.25/0.52  thf('28', plain,
% 0.25/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(t44_tops_1, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( l1_pre_topc @ A ) =>
% 0.25/0.52       ( ![B:$i]:
% 0.25/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.52           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.25/0.52  thf('29', plain,
% 0.25/0.52      (![X7 : $i, X8 : $i]:
% 0.25/0.52         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.25/0.52          | (r1_tarski @ (k1_tops_1 @ X8 @ X7) @ X7)
% 0.25/0.52          | ~ (l1_pre_topc @ X8))),
% 0.25/0.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.25/0.52  thf('30', plain,
% 0.25/0.52      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.25/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.25/0.52  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('32', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.25/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.25/0.52  thf('33', plain,
% 0.25/0.52      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1))),
% 0.25/0.52      inference('demod', [status(thm)], ['27', '32'])).
% 0.25/0.52  thf('34', plain, ((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.25/0.52      inference('clc', [status(thm)], ['9', '10'])).
% 0.25/0.52  thf('35', plain,
% 0.25/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.25/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.25/0.52  thf('36', plain,
% 0.25/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.25/0.52         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.25/0.52          | ~ (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.25/0.52          | (m1_connsp_2 @ X15 @ X14 @ X13)
% 0.25/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.25/0.52          | ~ (l1_pre_topc @ X14)
% 0.25/0.52          | ~ (v2_pre_topc @ X14)
% 0.25/0.52          | (v2_struct_0 @ X14))),
% 0.25/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.25/0.52  thf('37', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((v2_struct_0 @ sk_A)
% 0.25/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.52          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.25/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.25/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.25/0.52  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('40', plain,
% 0.25/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.25/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.25/0.52  thf(t55_tops_1, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.52       ( ![B:$i]:
% 0.25/0.52         ( ( l1_pre_topc @ B ) =>
% 0.25/0.52           ( ![C:$i]:
% 0.25/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.52               ( ![D:$i]:
% 0.25/0.52                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.25/0.52                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.25/0.52                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.25/0.52                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.25/0.52                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.52  thf('41', plain,
% 0.25/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.25/0.52         (~ (l1_pre_topc @ X9)
% 0.25/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.25/0.52          | ~ (v3_pre_topc @ X10 @ X9)
% 0.25/0.52          | ((k1_tops_1 @ X9 @ X10) = (X10))
% 0.25/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.25/0.52          | ~ (l1_pre_topc @ X12)
% 0.25/0.52          | ~ (v2_pre_topc @ X12))),
% 0.25/0.52      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.25/0.52  thf('42', plain,
% 0.25/0.52      ((![X9 : $i, X10 : $i]:
% 0.25/0.52          (~ (l1_pre_topc @ X9)
% 0.25/0.52           | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.25/0.52           | ~ (v3_pre_topc @ X10 @ X9)
% 0.25/0.52           | ((k1_tops_1 @ X9 @ X10) = (X10))))
% 0.25/0.52         <= ((![X9 : $i, X10 : $i]:
% 0.25/0.52                (~ (l1_pre_topc @ X9)
% 0.25/0.52                 | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.25/0.52                 | ~ (v3_pre_topc @ X10 @ X9)
% 0.25/0.52                 | ((k1_tops_1 @ X9 @ X10) = (X10)))))),
% 0.25/0.52      inference('split', [status(esa)], ['41'])).
% 0.25/0.52  thf('43', plain,
% 0.25/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.25/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.25/0.52  thf('44', plain,
% 0.25/0.52      (![X3 : $i, X4 : $i]:
% 0.25/0.52         (~ (l1_pre_topc @ X3)
% 0.25/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.25/0.52          | (m1_subset_1 @ (k1_tops_1 @ X3 @ X4) @ 
% 0.25/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.25/0.52      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.25/0.52  thf('45', plain,
% 0.25/0.52      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.25/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.25/0.52  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('47', plain,
% 0.25/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.25/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.25/0.52  thf('48', plain,
% 0.25/0.52      ((![X11 : $i, X12 : $i]:
% 0.25/0.52          (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.25/0.52           | ~ (l1_pre_topc @ X12)
% 0.25/0.52           | ~ (v2_pre_topc @ X12)))
% 0.25/0.52         <= ((![X11 : $i, X12 : $i]:
% 0.25/0.52                (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.25/0.52                 | ~ (l1_pre_topc @ X12)
% 0.25/0.52                 | ~ (v2_pre_topc @ X12))))),
% 0.25/0.52      inference('split', [status(esa)], ['41'])).
% 0.25/0.52  thf('49', plain,
% 0.25/0.52      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.25/0.52         <= ((![X11 : $i, X12 : $i]:
% 0.25/0.52                (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.25/0.52                 | ~ (l1_pre_topc @ X12)
% 0.25/0.52                 | ~ (v2_pre_topc @ X12))))),
% 0.25/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.25/0.52  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('52', plain,
% 0.25/0.52      (~
% 0.25/0.52       (![X11 : $i, X12 : $i]:
% 0.25/0.52          (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.25/0.52           | ~ (l1_pre_topc @ X12)
% 0.25/0.52           | ~ (v2_pre_topc @ X12)))),
% 0.25/0.52      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.25/0.52  thf('53', plain,
% 0.25/0.52      ((![X9 : $i, X10 : $i]:
% 0.25/0.52          (~ (l1_pre_topc @ X9)
% 0.25/0.52           | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.25/0.52           | ~ (v3_pre_topc @ X10 @ X9)
% 0.25/0.52           | ((k1_tops_1 @ X9 @ X10) = (X10)))) | 
% 0.25/0.52       (![X11 : $i, X12 : $i]:
% 0.25/0.52          (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.25/0.52           | ~ (l1_pre_topc @ X12)
% 0.25/0.52           | ~ (v2_pre_topc @ X12)))),
% 0.25/0.52      inference('split', [status(esa)], ['41'])).
% 0.25/0.52  thf('54', plain,
% 0.25/0.52      ((![X9 : $i, X10 : $i]:
% 0.25/0.52          (~ (l1_pre_topc @ X9)
% 0.25/0.52           | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.25/0.52           | ~ (v3_pre_topc @ X10 @ X9)
% 0.25/0.52           | ((k1_tops_1 @ X9 @ X10) = (X10))))),
% 0.25/0.52      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.25/0.52  thf('55', plain,
% 0.25/0.52      (![X9 : $i, X10 : $i]:
% 0.25/0.52         (~ (l1_pre_topc @ X9)
% 0.25/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.25/0.52          | ~ (v3_pre_topc @ X10 @ X9)
% 0.25/0.52          | ((k1_tops_1 @ X9 @ X10) = (X10)))),
% 0.25/0.52      inference('simpl_trail', [status(thm)], ['42', '54'])).
% 0.25/0.52  thf('56', plain,
% 0.25/0.52      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52          = (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.25/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['40', '55'])).
% 0.25/0.52  thf('57', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.25/0.52      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.25/0.52  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('59', plain,
% 0.25/0.52      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52         = (k1_tops_1 @ sk_A @ sk_C))),
% 0.25/0.52      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.25/0.52  thf('60', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((v2_struct_0 @ sk_A)
% 0.25/0.52          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.25/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.25/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('demod', [status(thm)], ['37', '38', '39', '59'])).
% 0.25/0.52  thf('61', plain,
% 0.25/0.52      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.25/0.52        | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1)
% 0.25/0.52        | (v2_struct_0 @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['34', '60'])).
% 0.25/0.52  thf('62', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('63', plain,
% 0.25/0.52      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1)
% 0.25/0.52        | (v2_struct_0 @ sk_A))),
% 0.25/0.52      inference('demod', [status(thm)], ['61', '62'])).
% 0.25/0.52  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('65', plain, ((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1)),
% 0.25/0.52      inference('clc', [status(thm)], ['63', '64'])).
% 0.25/0.52  thf('66', plain, ((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.25/0.52      inference('demod', [status(thm)], ['33', '65'])).
% 0.25/0.52  thf('67', plain, ($false), inference('demod', [status(thm)], ['13', '66'])).
% 0.25/0.52  
% 0.25/0.52  % SZS output end Refutation
% 0.25/0.52  
% 0.25/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
