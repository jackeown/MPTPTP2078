%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xf7tCG9d54

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:50 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 204 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  685 (3297 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ( r2_hidden @ X23 @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ( m1_connsp_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X19 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('39',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','42'])).

thf('44',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('48',plain,(
    ! [X29: $i] :
      ( ~ ( r1_tarski @ X29 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X29 @ sk_A )
      | ~ ( m1_connsp_2 @ X29 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('51',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','60'])).

thf('62',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['46','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xf7tCG9d54
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.02  % Solved by: fo/fo7.sh
% 0.82/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.02  % done 574 iterations in 0.560s
% 0.82/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.02  % SZS output start Refutation
% 0.82/1.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.02  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.82/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.02  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.82/1.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.82/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.02  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.82/1.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.82/1.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.82/1.02  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.82/1.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.82/1.02  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.82/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.02  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.82/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.02  thf(t7_connsp_2, conjecture,
% 0.82/1.02    (![A:$i]:
% 0.82/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.82/1.02       ( ![B:$i]:
% 0.82/1.02         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.02           ( ![C:$i]:
% 0.82/1.02             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.02               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.82/1.02                    ( ![D:$i]:
% 0.82/1.02                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.82/1.02                          ( m1_subset_1 @
% 0.82/1.02                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.02                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.82/1.02                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.82/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.02    (~( ![A:$i]:
% 0.82/1.02        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.82/1.02            ( l1_pre_topc @ A ) ) =>
% 0.82/1.02          ( ![B:$i]:
% 0.82/1.02            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.02              ( ![C:$i]:
% 0.82/1.02                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.02                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.82/1.02                       ( ![D:$i]:
% 0.82/1.02                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.82/1.02                             ( m1_subset_1 @
% 0.82/1.02                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.02                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.82/1.02                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.82/1.02    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.82/1.02  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('1', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('2', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf(d1_connsp_2, axiom,
% 0.82/1.02    (![A:$i]:
% 0.82/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.82/1.02       ( ![B:$i]:
% 0.82/1.02         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.02           ( ![C:$i]:
% 0.82/1.02             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.02               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.82/1.02                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.82/1.02  thf('3', plain,
% 0.82/1.02      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.82/1.02          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.82/1.02          | (r2_hidden @ X23 @ (k1_tops_1 @ X24 @ X25))
% 0.82/1.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.82/1.02          | ~ (l1_pre_topc @ X24)
% 0.82/1.02          | ~ (v2_pre_topc @ X24)
% 0.82/1.02          | (v2_struct_0 @ X24))),
% 0.82/1.02      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.82/1.02  thf('4', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((v2_struct_0 @ sk_A)
% 0.82/1.02          | ~ (v2_pre_topc @ sk_A)
% 0.82/1.02          | ~ (l1_pre_topc @ sk_A)
% 0.82/1.02          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.82/1.02          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.82/1.02          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['2', '3'])).
% 0.82/1.02  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('7', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((v2_struct_0 @ sk_A)
% 0.82/1.02          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.82/1.02          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.82/1.02          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.82/1.02  thf('8', plain,
% 0.82/1.02      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.82/1.02        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.82/1.02        | (v2_struct_0 @ sk_A))),
% 0.82/1.02      inference('sup-', [status(thm)], ['1', '7'])).
% 0.82/1.02  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('10', plain,
% 0.82/1.02      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.82/1.02      inference('demod', [status(thm)], ['8', '9'])).
% 0.82/1.02  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.82/1.02      inference('clc', [status(thm)], ['10', '11'])).
% 0.82/1.02  thf(d3_tarski, axiom,
% 0.82/1.02    (![A:$i,B:$i]:
% 0.82/1.02     ( ( r1_tarski @ A @ B ) <=>
% 0.82/1.02       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.82/1.02  thf('13', plain,
% 0.82/1.02      (![X1 : $i, X3 : $i]:
% 0.82/1.02         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.82/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.02  thf('14', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf(t44_tops_1, axiom,
% 0.82/1.02    (![A:$i]:
% 0.82/1.02     ( ( l1_pre_topc @ A ) =>
% 0.82/1.02       ( ![B:$i]:
% 0.82/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.02           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.82/1.02  thf('15', plain,
% 0.82/1.02      (![X21 : $i, X22 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.82/1.02          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ X21)
% 0.82/1.02          | ~ (l1_pre_topc @ X22))),
% 0.82/1.02      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.82/1.02  thf('16', plain,
% 0.82/1.02      ((~ (l1_pre_topc @ sk_A)
% 0.82/1.02        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.82/1.02      inference('sup-', [status(thm)], ['14', '15'])).
% 0.82/1.02  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('18', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.82/1.02      inference('demod', [status(thm)], ['16', '17'])).
% 0.82/1.02  thf('19', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.02         (~ (r2_hidden @ X0 @ X1)
% 0.82/1.02          | (r2_hidden @ X0 @ X2)
% 0.82/1.02          | ~ (r1_tarski @ X1 @ X2))),
% 0.82/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.02  thf('20', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r2_hidden @ X0 @ sk_C_1)
% 0.82/1.02          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['18', '19'])).
% 0.82/1.02  thf('21', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.82/1.02          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1))),
% 0.82/1.02      inference('sup-', [status(thm)], ['13', '20'])).
% 0.82/1.02  thf('22', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf(t3_subset, axiom,
% 0.82/1.02    (![A:$i,B:$i]:
% 0.82/1.02     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.82/1.02  thf('23', plain,
% 0.82/1.02      (![X10 : $i, X11 : $i]:
% 0.82/1.02         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.82/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.82/1.02  thf('24', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.82/1.02      inference('sup-', [status(thm)], ['22', '23'])).
% 0.82/1.02  thf('25', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.02         (~ (r2_hidden @ X0 @ X1)
% 0.82/1.02          | (r2_hidden @ X0 @ X2)
% 0.82/1.02          | ~ (r1_tarski @ X1 @ X2))),
% 0.82/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.02  thf('26', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.82/1.02      inference('sup-', [status(thm)], ['24', '25'])).
% 0.82/1.02  thf('27', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.82/1.02          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.82/1.02             (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['21', '26'])).
% 0.82/1.02  thf('28', plain,
% 0.82/1.02      (![X1 : $i, X3 : $i]:
% 0.82/1.02         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.82/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.02  thf('29', plain,
% 0.82/1.02      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.82/1.02        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['27', '28'])).
% 0.82/1.02  thf('30', plain,
% 0.82/1.02      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.82/1.02      inference('simplify', [status(thm)], ['29'])).
% 0.82/1.02  thf('31', plain,
% 0.82/1.02      (![X10 : $i, X12 : $i]:
% 0.82/1.02         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.82/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.82/1.02  thf('32', plain,
% 0.82/1.02      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.82/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['30', '31'])).
% 0.82/1.02  thf(t5_connsp_2, axiom,
% 0.82/1.02    (![A:$i]:
% 0.82/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.82/1.02       ( ![B:$i]:
% 0.82/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.02           ( ![C:$i]:
% 0.82/1.02             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.02               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.82/1.02                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.82/1.02  thf('33', plain,
% 0.82/1.02      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.82/1.02          | ~ (v3_pre_topc @ X26 @ X27)
% 0.82/1.02          | ~ (r2_hidden @ X28 @ X26)
% 0.82/1.02          | (m1_connsp_2 @ X26 @ X27 @ X28)
% 0.82/1.02          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.82/1.02          | ~ (l1_pre_topc @ X27)
% 0.82/1.02          | ~ (v2_pre_topc @ X27)
% 0.82/1.02          | (v2_struct_0 @ X27))),
% 0.82/1.02      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.82/1.02  thf('34', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((v2_struct_0 @ sk_A)
% 0.82/1.02          | ~ (v2_pre_topc @ sk_A)
% 0.82/1.02          | ~ (l1_pre_topc @ sk_A)
% 0.82/1.02          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.02          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.82/1.02          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.82/1.02          | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))),
% 0.82/1.02      inference('sup-', [status(thm)], ['32', '33'])).
% 0.82/1.02  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('37', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf(fc9_tops_1, axiom,
% 0.82/1.02    (![A:$i,B:$i]:
% 0.82/1.02     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.82/1.02         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.02       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.82/1.02  thf('38', plain,
% 0.82/1.02      (![X19 : $i, X20 : $i]:
% 0.82/1.02         (~ (l1_pre_topc @ X19)
% 0.82/1.02          | ~ (v2_pre_topc @ X19)
% 0.82/1.02          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.82/1.02          | (v3_pre_topc @ (k1_tops_1 @ X19 @ X20) @ X19))),
% 0.82/1.02      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.82/1.02  thf('39', plain,
% 0.82/1.02      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.82/1.02        | ~ (v2_pre_topc @ sk_A)
% 0.82/1.02        | ~ (l1_pre_topc @ sk_A))),
% 0.82/1.02      inference('sup-', [status(thm)], ['37', '38'])).
% 0.82/1.02  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('42', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.82/1.02      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.82/1.02  thf('43', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((v2_struct_0 @ sk_A)
% 0.82/1.02          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.82/1.02          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.82/1.02          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.82/1.02      inference('demod', [status(thm)], ['34', '35', '36', '42'])).
% 0.82/1.02  thf('44', plain,
% 0.82/1.02      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.82/1.02        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.82/1.02        | (v2_struct_0 @ sk_A))),
% 0.82/1.02      inference('sup-', [status(thm)], ['12', '43'])).
% 0.82/1.02  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('46', plain,
% 0.82/1.02      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.82/1.02        | (v2_struct_0 @ sk_A))),
% 0.82/1.02      inference('demod', [status(thm)], ['44', '45'])).
% 0.82/1.02  thf('47', plain,
% 0.82/1.02      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.82/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['30', '31'])).
% 0.82/1.02  thf('48', plain,
% 0.82/1.02      (![X29 : $i]:
% 0.82/1.02         (~ (r1_tarski @ X29 @ sk_C_1)
% 0.82/1.02          | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.82/1.02          | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_B)
% 0.82/1.02          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.02          | (v1_xboole_0 @ X29))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('49', plain,
% 0.82/1.02      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.82/1.02        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.82/1.02        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.82/1.02        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.82/1.02      inference('sup-', [status(thm)], ['47', '48'])).
% 0.82/1.02  thf('50', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.82/1.02      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.82/1.02  thf('51', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.82/1.02      inference('demod', [status(thm)], ['16', '17'])).
% 0.82/1.02  thf('52', plain,
% 0.82/1.02      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.82/1.02        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B))),
% 0.82/1.02      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.82/1.02  thf('53', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.82/1.02      inference('clc', [status(thm)], ['10', '11'])).
% 0.82/1.02  thf(d10_xboole_0, axiom,
% 0.82/1.02    (![A:$i,B:$i]:
% 0.82/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.82/1.02  thf('54', plain,
% 0.82/1.02      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.82/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.82/1.02  thf('55', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.82/1.02      inference('simplify', [status(thm)], ['54'])).
% 0.82/1.02  thf('56', plain,
% 0.82/1.02      (![X10 : $i, X12 : $i]:
% 0.82/1.02         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.82/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.82/1.02  thf('57', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.82/1.02      inference('sup-', [status(thm)], ['55', '56'])).
% 0.82/1.02  thf(t5_subset, axiom,
% 0.82/1.02    (![A:$i,B:$i,C:$i]:
% 0.82/1.02     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.82/1.02          ( v1_xboole_0 @ C ) ) ))).
% 0.82/1.02  thf('58', plain,
% 0.82/1.02      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.02         (~ (r2_hidden @ X16 @ X17)
% 0.82/1.02          | ~ (v1_xboole_0 @ X18)
% 0.82/1.02          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.82/1.02      inference('cnf', [status(esa)], [t5_subset])).
% 0.82/1.02  thf('59', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.82/1.02      inference('sup-', [status(thm)], ['57', '58'])).
% 0.82/1.02  thf('60', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.82/1.02      inference('sup-', [status(thm)], ['53', '59'])).
% 0.82/1.02  thf('61', plain,
% 0.82/1.02      (~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)),
% 0.82/1.02      inference('clc', [status(thm)], ['52', '60'])).
% 0.82/1.02  thf('62', plain, ((v2_struct_0 @ sk_A)),
% 0.82/1.02      inference('clc', [status(thm)], ['46', '61'])).
% 0.82/1.02  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.82/1.02  
% 0.82/1.02  % SZS output end Refutation
% 0.82/1.02  
% 0.82/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
