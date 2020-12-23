%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GM3OGnRAhf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 236 expanded)
%              Number of leaves         :   22 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  761 (4464 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_connsp_2 @ X13 @ X12 @ X11 )
      | ( r2_hidden @ X11 @ ( k1_tops_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
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

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_hidden @ X11 @ ( k1_tops_1 @ X12 @ X13 ) )
      | ( m1_connsp_2 @ X13 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k1_tops_1 @ X7 @ ( k1_tops_1 @ X7 @ X8 ) )
        = ( k1_tops_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('24',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','26'])).

thf('28',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i] :
      ( ~ ( r1_tarski @ X14 @ sk_C )
      | ~ ( v3_pre_topc @ X14 @ sk_A )
      | ~ ( m1_connsp_2 @ X14 @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_A @ sk_B_1 )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('44',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_A @ sk_B_1 )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['41','47'])).

thf('49',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('50',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('52',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('53',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('54',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X10 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','53','54','59'])).

thf('61',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['60','63'])).

thf('65',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['30','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GM3OGnRAhf
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:42:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 58 iterations in 0.029s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(t7_connsp_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.20/0.48                    ( ![D:$i]:
% 0.20/0.48                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.20/0.48                          ( m1_subset_1 @
% 0.20/0.48                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.20/0.48                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48            ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.20/0.48                       ( ![D:$i]:
% 0.20/0.48                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.20/0.48                             ( m1_subset_1 @
% 0.20/0.48                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.20/0.48                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.20/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d1_connsp_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.48                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.20/0.48          | ~ (m1_connsp_2 @ X13 @ X12 @ X11)
% 0.20/0.48          | (r2_hidden @ X11 @ (k1_tops_1 @ X12 @ X13))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.48          | ~ (l1_pre_topc @ X12)
% 0.20/0.48          | ~ (v2_pre_topc @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.48  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain, ((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k1_tops_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X3)
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48          | (m1_subset_1 @ (k1_tops_1 @ X3 @ X4) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.20/0.48          | ~ (r2_hidden @ X11 @ (k1_tops_1 @ X12 @ X13))
% 0.20/0.48          | (m1_connsp_2 @ X13 @ X12 @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.48          | ~ (l1_pre_topc @ X12)
% 0.20/0.48          | ~ (v2_pre_topc @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(projectivity_k1_tops_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ((k1_tops_1 @ X7 @ (k1_tops_1 @ X7 @ X8)) = (k1_tops_1 @ X7 @ X8)))),
% 0.20/0.48      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48          = (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48         = (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '20', '21', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '27'])).
% 0.20/0.48  thf('29', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X3)
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48          | (m1_subset_1 @ (k1_tops_1 @ X3 @ X4) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X3)
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48          | (m1_subset_1 @ (k1_tops_1 @ X3 @ X4) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((m1_subset_1 @ 
% 0.20/0.48         (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((m1_subset_1 @ 
% 0.20/0.48        (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X14 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X14 @ sk_C)
% 0.20/0.48          | ~ (v3_pre_topc @ X14 @ sk_A)
% 0.20/0.48          | ~ (m1_connsp_2 @ X14 @ sk_A @ sk_B_1)
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v1_xboole_0 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (((v1_xboole_0 @ 
% 0.20/0.48         (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.20/0.48        | ~ (m1_connsp_2 @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.20/0.48             sk_A @ sk_B_1)
% 0.20/0.48        | ~ (v3_pre_topc @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48        | ~ (r1_tarski @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.20/0.48             sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf(fc9_tops_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X5)
% 0.20/0.48          | ~ (v2_pre_topc @ X5)
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.48          | (v3_pre_topc @ (k1_tops_1 @ X5 @ X6) @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (((v3_pre_topc @ 
% 0.20/0.48         (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.20/0.48         sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((v3_pre_topc @ 
% 0.20/0.48        (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.20/0.48        sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (((v1_xboole_0 @ 
% 0.20/0.48         (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.20/0.48        | ~ (m1_connsp_2 @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.20/0.48             sk_A @ sk_B_1)
% 0.20/0.48        | ~ (r1_tarski @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.20/0.48             sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48         = (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48         = (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48         = (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48         = (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48         = (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48         = (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t44_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.48          | (r1_tarski @ (k1_tops_1 @ X10 @ X9) @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('59', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.48        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('demod', [status(thm)],
% 0.20/0.48                ['48', '49', '50', '51', '52', '53', '54', '59'])).
% 0.20/0.48  thf('61', plain, ((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('63', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B_1)),
% 0.20/0.48      inference('clc', [status(thm)], ['60', '63'])).
% 0.20/0.48  thf('65', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['30', '64'])).
% 0.20/0.48  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
