%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7rha00AXWK

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 207 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  692 (3322 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
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
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
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

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','62'])).

thf('64',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['46','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7rha00AXWK
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 135 iterations in 0.072s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.52  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.19/0.52  thf(t7_connsp_2, conjecture,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.52           ( ![C:$i]:
% 0.19/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.19/0.52                    ( ![D:$i]:
% 0.19/0.52                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.19/0.52                          ( m1_subset_1 @
% 0.19/0.52                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.52                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.19/0.52                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i]:
% 0.19/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.52            ( l1_pre_topc @ A ) ) =>
% 0.19/0.52          ( ![B:$i]:
% 0.19/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.52              ( ![C:$i]:
% 0.19/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.19/0.52                       ( ![D:$i]:
% 0.19/0.52                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.19/0.52                             ( m1_subset_1 @
% 0.19/0.52                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.52                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.19/0.52                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.19/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('1', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d1_connsp_2, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.52           ( ![C:$i]:
% 0.19/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.52                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.19/0.52          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.19/0.52          | (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 0.19/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.52          | ~ (l1_pre_topc @ X21)
% 0.19/0.52          | ~ (v2_pre_topc @ X21)
% 0.19/0.52          | (v2_struct_0 @ X21))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.52          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.52  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.52          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.52        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.52        | (v2_struct_0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['1', '7'])).
% 0.19/0.52  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.52  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.19/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.19/0.52  thf(d3_tarski, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      (![X1 : $i, X3 : $i]:
% 0.19/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t44_tops_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_pre_topc @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X18 : $i, X19 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.52          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 0.19/0.52          | ~ (l1_pre_topc @ X19))),
% 0.19/0.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.52  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('18', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.19/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.52          | (r2_hidden @ X0 @ X2)
% 0.19/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r2_hidden @ X0 @ sk_C_1)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.19/0.52          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['13', '20'])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t3_subset, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (![X7 : $i, X8 : $i]:
% 0.19/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.52  thf('24', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.52          | (r2_hidden @ X0 @ X2)
% 0.19/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.19/0.52          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.19/0.52             (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['21', '26'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (![X1 : $i, X3 : $i]:
% 0.19/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.19/0.52        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X7 : $i, X9 : $i]:
% 0.19/0.52         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.19/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.52  thf(t5_connsp_2, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ![C:$i]:
% 0.19/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.52               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.19/0.52                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.19/0.52          | ~ (v3_pre_topc @ X26 @ X27)
% 0.19/0.52          | ~ (r2_hidden @ X28 @ X26)
% 0.19/0.52          | (m1_connsp_2 @ X26 @ X27 @ X28)
% 0.19/0.52          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.19/0.52          | ~ (l1_pre_topc @ X27)
% 0.19/0.52          | ~ (v2_pre_topc @ X27)
% 0.19/0.52          | (v2_struct_0 @ X27))),
% 0.19/0.52      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.52          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.52          | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.52  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(fc9_tops_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.19/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.52       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      (![X16 : $i, X17 : $i]:
% 0.19/0.52         (~ (l1_pre_topc @ X16)
% 0.19/0.52          | ~ (v2_pre_topc @ X16)
% 0.19/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.52          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 0.19/0.52      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.19/0.52  thf('39', plain,
% 0.19/0.52      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.19/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.52  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('42', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.19/0.52      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.19/0.52  thf('43', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.52          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.19/0.52      inference('demod', [status(thm)], ['34', '35', '36', '42'])).
% 0.19/0.52  thf('44', plain,
% 0.19/0.52      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.19/0.52        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.52        | (v2_struct_0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['12', '43'])).
% 0.19/0.52  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('46', plain,
% 0.19/0.52      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.19/0.52        | (v2_struct_0 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.52  thf('47', plain,
% 0.19/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.52  thf('48', plain,
% 0.19/0.52      (![X29 : $i]:
% 0.19/0.52         (~ (r1_tarski @ X29 @ sk_C_1)
% 0.19/0.52          | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.19/0.52          | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_B)
% 0.19/0.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52          | (v1_xboole_0 @ X29))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('49', plain,
% 0.19/0.52      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.52        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.19/0.52        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.19/0.52        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.52  thf('50', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.19/0.52      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.19/0.52  thf('51', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.19/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.52  thf('52', plain,
% 0.19/0.52      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.52        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.19/0.52  thf('53', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.19/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.19/0.52  thf('54', plain,
% 0.19/0.52      (![X1 : $i, X3 : $i]:
% 0.19/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.52  thf('55', plain,
% 0.19/0.52      (![X1 : $i, X3 : $i]:
% 0.19/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.52  thf('56', plain,
% 0.19/0.52      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.19/0.52  thf('57', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.52      inference('simplify', [status(thm)], ['56'])).
% 0.19/0.52  thf('58', plain,
% 0.19/0.52      (![X7 : $i, X9 : $i]:
% 0.19/0.52         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.19/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.52  thf('59', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.52  thf(t5_subset, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.19/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.19/0.52  thf('60', plain,
% 0.19/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X13 @ X14)
% 0.19/0.52          | ~ (v1_xboole_0 @ X15)
% 0.19/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.52  thf('61', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.19/0.52  thf('62', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['53', '61'])).
% 0.19/0.52  thf('63', plain,
% 0.19/0.52      (~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)),
% 0.19/0.52      inference('clc', [status(thm)], ['52', '62'])).
% 0.19/0.52  thf('64', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('clc', [status(thm)], ['46', '63'])).
% 0.19/0.52  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
