%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rvyaryIlsI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:47 EST 2020

% Result     : Theorem 30.44s
% Output     : Refutation 30.44s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 266 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  908 (5329 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t3_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( m1_connsp_2 @ C @ A @ B )
                      & ( m1_connsp_2 @ D @ A @ B ) )
                   => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( m1_connsp_2 @ C @ A @ B )
                        & ( m1_connsp_2 @ D @ A @ B ) )
                     => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k1_tops_1 @ X10 @ X9 ) )
      | ( r2_hidden @ X11 @ ( sk_D @ X9 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r2_hidden @ sk_B @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k1_tops_1 @ X10 @ X9 ) )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X11 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X4 @ X3 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k4_subset_1 @ X7 @ X6 @ X8 )
        = ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X9 )
      | ~ ( v3_pre_topc @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r2_hidden @ X11 @ ( k1_tops_1 @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','43'])).

thf('45',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('46',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k1_tops_1 @ X10 @ X9 ) )
      | ( r1_tarski @ ( sk_D @ X9 @ X11 @ X10 ) @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    r1_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['45','51'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('56',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k1_tops_1 @ X10 @ X9 ) )
      | ( v3_pre_topc @ ( sk_D @ X9 @ X11 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    v3_pre_topc @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ) ) ),
    inference(demod,[status(thm)],['44','54','62'])).

thf('64',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('76',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['73','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rvyaryIlsI
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 30.44/30.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 30.44/30.69  % Solved by: fo/fo7.sh
% 30.44/30.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.44/30.69  % done 4327 iterations in 30.223s
% 30.44/30.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 30.44/30.69  % SZS output start Refutation
% 30.44/30.69  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 30.44/30.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 30.44/30.69  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 30.44/30.69  thf(sk_C_type, type, sk_C: $i).
% 30.44/30.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 30.44/30.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 30.44/30.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 30.44/30.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 30.44/30.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 30.44/30.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 30.44/30.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 30.44/30.69  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 30.44/30.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 30.44/30.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 30.44/30.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 30.44/30.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 30.44/30.69  thf(sk_B_type, type, sk_B: $i).
% 30.44/30.69  thf(sk_A_type, type, sk_A: $i).
% 30.44/30.69  thf(t3_connsp_2, conjecture,
% 30.44/30.69    (![A:$i]:
% 30.44/30.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 30.44/30.69       ( ![B:$i]:
% 30.44/30.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 30.44/30.69           ( ![C:$i]:
% 30.44/30.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 30.44/30.69               ( ![D:$i]:
% 30.44/30.69                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 30.44/30.69                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 30.44/30.69                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 30.44/30.69                     ( m1_connsp_2 @
% 30.44/30.69                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 30.44/30.69  thf(zf_stmt_0, negated_conjecture,
% 30.44/30.69    (~( ![A:$i]:
% 30.44/30.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 30.44/30.69            ( l1_pre_topc @ A ) ) =>
% 30.44/30.69          ( ![B:$i]:
% 30.44/30.69            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 30.44/30.69              ( ![C:$i]:
% 30.44/30.69                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 30.44/30.69                  ( ![D:$i]:
% 30.44/30.69                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 30.44/30.69                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 30.44/30.69                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 30.44/30.69                        ( m1_connsp_2 @
% 30.44/30.69                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 30.44/30.69    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 30.44/30.69  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('1', plain, ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('2', plain,
% 30.44/30.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf(d1_connsp_2, axiom,
% 30.44/30.69    (![A:$i]:
% 30.44/30.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 30.44/30.69       ( ![B:$i]:
% 30.44/30.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 30.44/30.69           ( ![C:$i]:
% 30.44/30.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 30.44/30.69               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 30.44/30.69                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 30.44/30.69  thf('3', plain,
% 30.44/30.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 30.44/30.69         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 30.44/30.69          | ~ (m1_connsp_2 @ X15 @ X14 @ X13)
% 30.44/30.69          | (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 30.44/30.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 30.44/30.69          | ~ (l1_pre_topc @ X14)
% 30.44/30.69          | ~ (v2_pre_topc @ X14)
% 30.44/30.69          | (v2_struct_0 @ X14))),
% 30.44/30.69      inference('cnf', [status(esa)], [d1_connsp_2])).
% 30.44/30.69  thf('4', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         ((v2_struct_0 @ sk_A)
% 30.44/30.69          | ~ (v2_pre_topc @ sk_A)
% 30.44/30.69          | ~ (l1_pre_topc @ sk_A)
% 30.44/30.69          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 30.44/30.69          | ~ (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 30.44/30.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('sup-', [status(thm)], ['2', '3'])).
% 30.44/30.69  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('7', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         ((v2_struct_0 @ sk_A)
% 30.44/30.69          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 30.44/30.69          | ~ (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 30.44/30.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('demod', [status(thm)], ['4', '5', '6'])).
% 30.44/30.69  thf('8', plain,
% 30.44/30.69      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 30.44/30.69        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1))
% 30.44/30.69        | (v2_struct_0 @ sk_A))),
% 30.44/30.69      inference('sup-', [status(thm)], ['1', '7'])).
% 30.44/30.69  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('10', plain,
% 30.44/30.69      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1)) | (v2_struct_0 @ sk_A))),
% 30.44/30.69      inference('demod', [status(thm)], ['8', '9'])).
% 30.44/30.69  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1))),
% 30.44/30.69      inference('clc', [status(thm)], ['10', '11'])).
% 30.44/30.69  thf('13', plain,
% 30.44/30.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf(t54_tops_1, axiom,
% 30.44/30.69    (![A:$i]:
% 30.44/30.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 30.44/30.69       ( ![B:$i,C:$i]:
% 30.44/30.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 30.44/30.69           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 30.44/30.69             ( ?[D:$i]:
% 30.44/30.69               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 30.44/30.69                 ( v3_pre_topc @ D @ A ) & 
% 30.44/30.69                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 30.44/30.69  thf('14', plain,
% 30.44/30.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 30.44/30.69         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 30.44/30.69          | ~ (r2_hidden @ X11 @ (k1_tops_1 @ X10 @ X9))
% 30.44/30.69          | (r2_hidden @ X11 @ (sk_D @ X9 @ X11 @ X10))
% 30.44/30.69          | ~ (l1_pre_topc @ X10)
% 30.44/30.69          | ~ (v2_pre_topc @ X10))),
% 30.44/30.69      inference('cnf', [status(esa)], [t54_tops_1])).
% 30.44/30.69  thf('15', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         (~ (v2_pre_topc @ sk_A)
% 30.44/30.69          | ~ (l1_pre_topc @ sk_A)
% 30.44/30.69          | (r2_hidden @ X0 @ (sk_D @ sk_D_1 @ X0 @ sk_A))
% 30.44/30.69          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 30.44/30.69      inference('sup-', [status(thm)], ['13', '14'])).
% 30.44/30.69  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('18', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         ((r2_hidden @ X0 @ (sk_D @ sk_D_1 @ X0 @ sk_A))
% 30.44/30.69          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 30.44/30.69      inference('demod', [status(thm)], ['15', '16', '17'])).
% 30.44/30.69  thf('19', plain, ((r2_hidden @ sk_B @ (sk_D @ sk_D_1 @ sk_B @ sk_A))),
% 30.44/30.69      inference('sup-', [status(thm)], ['12', '18'])).
% 30.44/30.69  thf('20', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1))),
% 30.44/30.69      inference('clc', [status(thm)], ['10', '11'])).
% 30.44/30.69  thf('21', plain,
% 30.44/30.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('22', plain,
% 30.44/30.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 30.44/30.69         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 30.44/30.69          | ~ (r2_hidden @ X11 @ (k1_tops_1 @ X10 @ X9))
% 30.44/30.69          | (m1_subset_1 @ (sk_D @ X9 @ X11 @ X10) @ 
% 30.44/30.69             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 30.44/30.69          | ~ (l1_pre_topc @ X10)
% 30.44/30.69          | ~ (v2_pre_topc @ X10))),
% 30.44/30.69      inference('cnf', [status(esa)], [t54_tops_1])).
% 30.44/30.69  thf('23', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         (~ (v2_pre_topc @ sk_A)
% 30.44/30.69          | ~ (l1_pre_topc @ sk_A)
% 30.44/30.69          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_A) @ 
% 30.44/30.69             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 30.44/30.69          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 30.44/30.69      inference('sup-', [status(thm)], ['21', '22'])).
% 30.44/30.69  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('26', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         ((m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_A) @ 
% 30.44/30.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 30.44/30.69          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 30.44/30.69      inference('demod', [status(thm)], ['23', '24', '25'])).
% 30.44/30.69  thf('27', plain,
% 30.44/30.69      ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ 
% 30.44/30.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('sup-', [status(thm)], ['20', '26'])).
% 30.44/30.69  thf('28', plain,
% 30.44/30.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('29', plain,
% 30.44/30.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf(dt_k4_subset_1, axiom,
% 30.44/30.69    (![A:$i,B:$i,C:$i]:
% 30.44/30.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 30.44/30.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 30.44/30.69       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 30.44/30.69  thf('30', plain,
% 30.44/30.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 30.44/30.69         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 30.44/30.69          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4))
% 30.44/30.69          | (m1_subset_1 @ (k4_subset_1 @ X4 @ X3 @ X5) @ (k1_zfmisc_1 @ X4)))),
% 30.44/30.69      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 30.44/30.69  thf('31', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 30.44/30.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 30.44/30.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 30.44/30.69      inference('sup-', [status(thm)], ['29', '30'])).
% 30.44/30.69  thf('32', plain,
% 30.44/30.69      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 30.44/30.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('sup-', [status(thm)], ['28', '31'])).
% 30.44/30.69  thf('33', plain,
% 30.44/30.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('34', plain,
% 30.44/30.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf(redefinition_k4_subset_1, axiom,
% 30.44/30.69    (![A:$i,B:$i,C:$i]:
% 30.44/30.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 30.44/30.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 30.44/30.69       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 30.44/30.69  thf('35', plain,
% 30.44/30.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 30.44/30.69         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 30.44/30.69          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 30.44/30.69          | ((k4_subset_1 @ X7 @ X6 @ X8) = (k2_xboole_0 @ X6 @ X8)))),
% 30.44/30.69      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 30.44/30.69  thf('36', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 30.44/30.69            = (k2_xboole_0 @ sk_C @ X0))
% 30.44/30.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 30.44/30.69      inference('sup-', [status(thm)], ['34', '35'])).
% 30.44/30.69  thf('37', plain,
% 30.44/30.69      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)
% 30.44/30.69         = (k2_xboole_0 @ sk_C @ sk_D_1))),
% 30.44/30.69      inference('sup-', [status(thm)], ['33', '36'])).
% 30.44/30.69  thf('38', plain,
% 30.44/30.69      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 30.44/30.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('demod', [status(thm)], ['32', '37'])).
% 30.44/30.69  thf('39', plain,
% 30.44/30.69      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 30.44/30.69         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 30.44/30.69          | ~ (r2_hidden @ X11 @ X12)
% 30.44/30.69          | ~ (r1_tarski @ X12 @ X9)
% 30.44/30.69          | ~ (v3_pre_topc @ X12 @ X10)
% 30.44/30.69          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 30.44/30.69          | (r2_hidden @ X11 @ (k1_tops_1 @ X10 @ X9))
% 30.44/30.69          | ~ (l1_pre_topc @ X10)
% 30.44/30.69          | ~ (v2_pre_topc @ X10))),
% 30.44/30.69      inference('cnf', [status(esa)], [t54_tops_1])).
% 30.44/30.69  thf('40', plain,
% 30.44/30.69      (![X0 : $i, X1 : $i]:
% 30.44/30.69         (~ (v2_pre_topc @ sk_A)
% 30.44/30.69          | ~ (l1_pre_topc @ sk_A)
% 30.44/30.69          | (r2_hidden @ X0 @ 
% 30.44/30.69             (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 30.44/30.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 30.44/30.69          | ~ (v3_pre_topc @ X1 @ sk_A)
% 30.44/30.69          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 30.44/30.69          | ~ (r2_hidden @ X0 @ X1))),
% 30.44/30.69      inference('sup-', [status(thm)], ['38', '39'])).
% 30.44/30.69  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('43', plain,
% 30.44/30.69      (![X0 : $i, X1 : $i]:
% 30.44/30.69         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 30.44/30.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 30.44/30.69          | ~ (v3_pre_topc @ X1 @ sk_A)
% 30.44/30.69          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 30.44/30.69          | ~ (r2_hidden @ X0 @ X1))),
% 30.44/30.69      inference('demod', [status(thm)], ['40', '41', '42'])).
% 30.44/30.69  thf('44', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         (~ (r2_hidden @ X0 @ (sk_D @ sk_D_1 @ sk_B @ sk_A))
% 30.44/30.69          | ~ (r1_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ 
% 30.44/30.69               (k2_xboole_0 @ sk_C @ sk_D_1))
% 30.44/30.69          | ~ (v3_pre_topc @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A)
% 30.44/30.69          | (r2_hidden @ X0 @ 
% 30.44/30.69             (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1))))),
% 30.44/30.69      inference('sup-', [status(thm)], ['27', '43'])).
% 30.44/30.69  thf('45', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1))),
% 30.44/30.69      inference('clc', [status(thm)], ['10', '11'])).
% 30.44/30.69  thf('46', plain,
% 30.44/30.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('47', plain,
% 30.44/30.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 30.44/30.69         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 30.44/30.69          | ~ (r2_hidden @ X11 @ (k1_tops_1 @ X10 @ X9))
% 30.44/30.69          | (r1_tarski @ (sk_D @ X9 @ X11 @ X10) @ X9)
% 30.44/30.69          | ~ (l1_pre_topc @ X10)
% 30.44/30.69          | ~ (v2_pre_topc @ X10))),
% 30.44/30.69      inference('cnf', [status(esa)], [t54_tops_1])).
% 30.44/30.69  thf('48', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         (~ (v2_pre_topc @ sk_A)
% 30.44/30.69          | ~ (l1_pre_topc @ sk_A)
% 30.44/30.69          | (r1_tarski @ (sk_D @ sk_D_1 @ X0 @ sk_A) @ sk_D_1)
% 30.44/30.69          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 30.44/30.69      inference('sup-', [status(thm)], ['46', '47'])).
% 30.44/30.69  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('51', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         ((r1_tarski @ (sk_D @ sk_D_1 @ X0 @ sk_A) @ sk_D_1)
% 30.44/30.69          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 30.44/30.69      inference('demod', [status(thm)], ['48', '49', '50'])).
% 30.44/30.69  thf('52', plain, ((r1_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_D_1)),
% 30.44/30.69      inference('sup-', [status(thm)], ['45', '51'])).
% 30.44/30.69  thf(t10_xboole_1, axiom,
% 30.44/30.69    (![A:$i,B:$i,C:$i]:
% 30.44/30.69     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 30.44/30.69  thf('53', plain,
% 30.44/30.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.44/30.69         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 30.44/30.69      inference('cnf', [status(esa)], [t10_xboole_1])).
% 30.44/30.69  thf('54', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         (r1_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ 
% 30.44/30.69          (k2_xboole_0 @ X0 @ sk_D_1))),
% 30.44/30.69      inference('sup-', [status(thm)], ['52', '53'])).
% 30.44/30.69  thf('55', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1))),
% 30.44/30.69      inference('clc', [status(thm)], ['10', '11'])).
% 30.44/30.69  thf('56', plain,
% 30.44/30.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('57', plain,
% 30.44/30.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 30.44/30.69         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 30.44/30.69          | ~ (r2_hidden @ X11 @ (k1_tops_1 @ X10 @ X9))
% 30.44/30.69          | (v3_pre_topc @ (sk_D @ X9 @ X11 @ X10) @ X10)
% 30.44/30.69          | ~ (l1_pre_topc @ X10)
% 30.44/30.69          | ~ (v2_pre_topc @ X10))),
% 30.44/30.69      inference('cnf', [status(esa)], [t54_tops_1])).
% 30.44/30.69  thf('58', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         (~ (v2_pre_topc @ sk_A)
% 30.44/30.69          | ~ (l1_pre_topc @ sk_A)
% 30.44/30.69          | (v3_pre_topc @ (sk_D @ sk_D_1 @ X0 @ sk_A) @ sk_A)
% 30.44/30.69          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 30.44/30.69      inference('sup-', [status(thm)], ['56', '57'])).
% 30.44/30.69  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('61', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         ((v3_pre_topc @ (sk_D @ sk_D_1 @ X0 @ sk_A) @ sk_A)
% 30.44/30.69          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 30.44/30.69      inference('demod', [status(thm)], ['58', '59', '60'])).
% 30.44/30.69  thf('62', plain, ((v3_pre_topc @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A)),
% 30.44/30.69      inference('sup-', [status(thm)], ['55', '61'])).
% 30.44/30.69  thf('63', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         (~ (r2_hidden @ X0 @ (sk_D @ sk_D_1 @ sk_B @ sk_A))
% 30.44/30.69          | (r2_hidden @ X0 @ 
% 30.44/30.69             (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1))))),
% 30.44/30.69      inference('demod', [status(thm)], ['44', '54', '62'])).
% 30.44/30.69  thf('64', plain,
% 30.44/30.69      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 30.44/30.69      inference('sup-', [status(thm)], ['19', '63'])).
% 30.44/30.69  thf('65', plain,
% 30.44/30.69      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 30.44/30.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('demod', [status(thm)], ['32', '37'])).
% 30.44/30.69  thf('66', plain,
% 30.44/30.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 30.44/30.69         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 30.44/30.69          | ~ (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 30.44/30.69          | (m1_connsp_2 @ X15 @ X14 @ X13)
% 30.44/30.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 30.44/30.69          | ~ (l1_pre_topc @ X14)
% 30.44/30.69          | ~ (v2_pre_topc @ X14)
% 30.44/30.69          | (v2_struct_0 @ X14))),
% 30.44/30.69      inference('cnf', [status(esa)], [d1_connsp_2])).
% 30.44/30.69  thf('67', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         ((v2_struct_0 @ sk_A)
% 30.44/30.69          | ~ (v2_pre_topc @ sk_A)
% 30.44/30.69          | ~ (l1_pre_topc @ sk_A)
% 30.44/30.69          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ X0)
% 30.44/30.69          | ~ (r2_hidden @ X0 @ 
% 30.44/30.69               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 30.44/30.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('sup-', [status(thm)], ['65', '66'])).
% 30.44/30.69  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('70', plain,
% 30.44/30.69      (![X0 : $i]:
% 30.44/30.69         ((v2_struct_0 @ sk_A)
% 30.44/30.69          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ X0)
% 30.44/30.69          | ~ (r2_hidden @ X0 @ 
% 30.44/30.69               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 30.44/30.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 30.44/30.69      inference('demod', [status(thm)], ['67', '68', '69'])).
% 30.44/30.69  thf('71', plain,
% 30.44/30.69      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 30.44/30.69        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 30.44/30.69        | (v2_struct_0 @ sk_A))),
% 30.44/30.69      inference('sup-', [status(thm)], ['64', '70'])).
% 30.44/30.69  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('73', plain,
% 30.44/30.69      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 30.44/30.69        | (v2_struct_0 @ sk_A))),
% 30.44/30.69      inference('demod', [status(thm)], ['71', '72'])).
% 30.44/30.69  thf('74', plain,
% 30.44/30.69      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 30.44/30.69          sk_A @ sk_B)),
% 30.44/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.44/30.69  thf('75', plain,
% 30.44/30.69      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)
% 30.44/30.69         = (k2_xboole_0 @ sk_C @ sk_D_1))),
% 30.44/30.69      inference('sup-', [status(thm)], ['33', '36'])).
% 30.44/30.69  thf('76', plain,
% 30.44/30.69      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)),
% 30.44/30.69      inference('demod', [status(thm)], ['74', '75'])).
% 30.44/30.69  thf('77', plain, ((v2_struct_0 @ sk_A)),
% 30.44/30.69      inference('clc', [status(thm)], ['73', '76'])).
% 30.44/30.69  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 30.44/30.69  
% 30.44/30.69  % SZS output end Refutation
% 30.44/30.69  
% 30.44/30.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
