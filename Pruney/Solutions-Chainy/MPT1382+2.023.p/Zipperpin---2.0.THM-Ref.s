%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6mI1xuXBoR

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:53 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 243 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  763 (4638 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_connsp_2 @ X14 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ ( k1_tops_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ( m1_connsp_2 @ X18 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X8 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('24',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','27'])).

thf('29',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_connsp_2 @ X14 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ ( k1_tops_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('53',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ X21 @ sk_C )
      | ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( m1_connsp_2 @ X21 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,(
    m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['31','32'])).

thf('64',plain,(
    v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','64'])).

thf('66',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['42','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6mI1xuXBoR
% 0.14/0.36  % Computer   : n010.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 18:27:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 80 iterations in 0.047s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.52  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.23/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.23/0.52  thf(t7_connsp_2, conjecture,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.52           ( ![C:$i]:
% 0.23/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.52               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.23/0.52                    ( ![D:$i]:
% 0.23/0.52                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.23/0.52                          ( m1_subset_1 @
% 0.23/0.52                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.52                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.23/0.52                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i]:
% 0.23/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.52            ( l1_pre_topc @ A ) ) =>
% 0.23/0.52          ( ![B:$i]:
% 0.23/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.52              ( ![C:$i]:
% 0.23/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.52                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.23/0.52                       ( ![D:$i]:
% 0.23/0.52                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.23/0.52                             ( m1_subset_1 @
% 0.23/0.52                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.52                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.23/0.52                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.23/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('1', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(d1_connsp_2, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.52           ( ![C:$i]:
% 0.23/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.52               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.23/0.52                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.23/0.52          | ~ (m1_connsp_2 @ X14 @ X13 @ X12)
% 0.23/0.52          | (r2_hidden @ X12 @ (k1_tops_1 @ X13 @ X14))
% 0.23/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.23/0.52          | ~ (l1_pre_topc @ X13)
% 0.23/0.52          | ~ (v2_pre_topc @ X13)
% 0.23/0.52          | (v2_struct_0 @ X13))),
% 0.23/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v2_struct_0 @ sk_A)
% 0.23/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.23/0.52          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.52  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v2_struct_0 @ sk_A)
% 0.23/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.23/0.52          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.52        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.23/0.52        | (v2_struct_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['1', '7'])).
% 0.23/0.52  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('10', plain,
% 0.23/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.23/0.52  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.23/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(dt_k1_tops_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.23/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.52       ( m1_subset_1 @
% 0.23/0.52         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (![X6 : $i, X7 : $i]:
% 0.23/0.52         (~ (l1_pre_topc @ X6)
% 0.23/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.23/0.52          | (m1_subset_1 @ (k1_tops_1 @ X6 @ X7) @ 
% 0.23/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.23/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.23/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.52  thf(t5_connsp_2, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.52           ( ![C:$i]:
% 0.23/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.52               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.23/0.52                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.23/0.52          | ~ (v3_pre_topc @ X18 @ X19)
% 0.23/0.52          | ~ (r2_hidden @ X20 @ X18)
% 0.23/0.52          | (m1_connsp_2 @ X18 @ X19 @ X20)
% 0.23/0.52          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.23/0.52          | ~ (l1_pre_topc @ X19)
% 0.23/0.52          | ~ (v2_pre_topc @ X19)
% 0.23/0.52          | (v2_struct_0 @ X19))),
% 0.23/0.52      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v2_struct_0 @ sk_A)
% 0.23/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.23/0.52          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.23/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.23/0.52          | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.52  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(fc9_tops_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.23/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.52       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      (![X8 : $i, X9 : $i]:
% 0.23/0.52         (~ (l1_pre_topc @ X8)
% 0.23/0.52          | ~ (v2_pre_topc @ X8)
% 0.23/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.23/0.52          | (v3_pre_topc @ (k1_tops_1 @ X8 @ X9) @ X8))),
% 0.23/0.52      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.23/0.52  thf('24', plain,
% 0.23/0.52      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.23/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.52  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('27', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.23/0.52      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.23/0.52  thf('28', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v2_struct_0 @ sk_A)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.23/0.52          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.23/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.23/0.52      inference('demod', [status(thm)], ['19', '20', '21', '27'])).
% 0.23/0.52  thf('29', plain,
% 0.23/0.52      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)
% 0.23/0.52        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.52        | (v2_struct_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['12', '28'])).
% 0.23/0.52  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('31', plain,
% 0.23/0.52      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)
% 0.23/0.52        | (v2_struct_0 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.23/0.52  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('33', plain, ((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)),
% 0.23/0.52      inference('clc', [status(thm)], ['31', '32'])).
% 0.23/0.52  thf('34', plain,
% 0.23/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.23/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.52  thf('35', plain,
% 0.23/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.23/0.52          | ~ (m1_connsp_2 @ X14 @ X13 @ X12)
% 0.23/0.52          | (r2_hidden @ X12 @ (k1_tops_1 @ X13 @ X14))
% 0.23/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.23/0.52          | ~ (l1_pre_topc @ X13)
% 0.23/0.52          | ~ (v2_pre_topc @ X13)
% 0.23/0.52          | (v2_struct_0 @ X13))),
% 0.23/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.23/0.52  thf('36', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v2_struct_0 @ sk_A)
% 0.23/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.23/0.52          | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.23/0.52  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('39', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v2_struct_0 @ sk_A)
% 0.23/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.23/0.52          | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.23/0.52  thf('40', plain,
% 0.23/0.52      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.52        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.23/0.52        | (v2_struct_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['33', '39'])).
% 0.23/0.52  thf('41', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('42', plain,
% 0.23/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.23/0.52        | (v2_struct_0 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.23/0.52  thf('43', plain,
% 0.23/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.23/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.52  thf(t44_tops_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( l1_pre_topc @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.52           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.23/0.52  thf('44', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.52          | (r1_tarski @ (k1_tops_1 @ X11 @ X10) @ X10)
% 0.23/0.52          | ~ (l1_pre_topc @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.23/0.52  thf('45', plain,
% 0.23/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.52        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.23/0.52           (k1_tops_1 @ sk_A @ sk_C)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.23/0.52  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('47', plain,
% 0.23/0.52      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.23/0.52        (k1_tops_1 @ sk_A @ sk_C))),
% 0.23/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.23/0.52  thf(t3_subset, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.52  thf('48', plain,
% 0.23/0.52      (![X0 : $i, X2 : $i]:
% 0.23/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.52  thf('49', plain,
% 0.23/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.23/0.52        (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.23/0.52  thf(t5_subset, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.23/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.23/0.52  thf('50', plain,
% 0.23/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X3 @ X4)
% 0.23/0.52          | ~ (v1_xboole_0 @ X5)
% 0.23/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.23/0.52  thf('51', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.23/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.23/0.52  thf('52', plain,
% 0.23/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.23/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.52  thf('53', plain,
% 0.23/0.52      (![X21 : $i]:
% 0.23/0.52         (~ (r1_tarski @ X21 @ sk_C)
% 0.23/0.52          | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.23/0.52          | ~ (m1_connsp_2 @ X21 @ sk_A @ sk_B)
% 0.23/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.52          | (v1_xboole_0 @ X21))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('54', plain,
% 0.23/0.52      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.23/0.52        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)
% 0.23/0.52        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.23/0.52        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.23/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.23/0.52  thf('55', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.23/0.52      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.23/0.52  thf('56', plain,
% 0.23/0.52      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.23/0.52        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)
% 0.23/0.52        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.23/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.23/0.52  thf('57', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('58', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.52          | (r1_tarski @ (k1_tops_1 @ X11 @ X10) @ X10)
% 0.23/0.52          | ~ (l1_pre_topc @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.23/0.52  thf('59', plain,
% 0.23/0.52      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.23/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.23/0.52  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('61', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['59', '60'])).
% 0.23/0.52  thf('62', plain,
% 0.23/0.52      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.23/0.52        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['56', '61'])).
% 0.23/0.52  thf('63', plain, ((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)),
% 0.23/0.52      inference('clc', [status(thm)], ['31', '32'])).
% 0.23/0.52  thf('64', plain, ((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.23/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.23/0.52  thf('65', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.23/0.52      inference('demod', [status(thm)], ['51', '64'])).
% 0.23/0.52  thf('66', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('clc', [status(thm)], ['42', '65'])).
% 0.23/0.52  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
