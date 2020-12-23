%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uIF5oUMuKy

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:23 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 241 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  778 (4059 expanded)
%              Number of equality atoms :   10 (  34 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t23_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( v2_tops_2 @ B @ A )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( ( v2_tops_2 @ B @ A )
                    & ( v2_tops_2 @ C @ A ) )
                 => ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(d2_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('17',plain,(
    ~ ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v2_tops_2 @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( v4_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B )
    | ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ X12 @ X13 ) @ X13 )
      | ( v2_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('34',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['25','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X12 @ X13 ) @ X12 )
      | ( v2_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_hidden @ ( sk_C @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('44',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('45',plain,(
    r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('46',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('47',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    m1_subset_1 @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v2_tops_2 @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( v4_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v2_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_C_1 )
    | ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('58',plain,(
    ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['48','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['35','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uIF5oUMuKy
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 216 iterations in 0.184s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.46/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(t23_tops_2, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @
% 0.46/0.63             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @
% 0.46/0.63                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63               ( ( ( v2_tops_2 @ B @ A ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.46/0.63                 ( v2_tops_2 @
% 0.46/0.63                   ( k4_subset_1 @
% 0.46/0.63                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.46/0.63                   A ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( l1_pre_topc @ A ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( m1_subset_1 @
% 0.46/0.63                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63              ( ![C:$i]:
% 0.46/0.63                ( ( m1_subset_1 @
% 0.46/0.63                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63                  ( ( ( v2_tops_2 @ B @ A ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.46/0.63                    ( v2_tops_2 @
% 0.46/0.63                      ( k4_subset_1 @
% 0.46/0.63                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.46/0.63                      A ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t23_tops_2])).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_k4_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.63       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.46/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 0.46/0.63          | (m1_subset_1 @ (k4_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((m1_subset_1 @ 
% 0.46/0.63           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ 
% 0.46/0.63               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      ((m1_subset_1 @ 
% 0.46/0.63        (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '3'])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k4_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.63       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.46/0.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 0.46/0.63          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.46/0.63            = (k2_xboole_0 @ sk_B @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ 
% 0.46/0.63               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1)
% 0.46/0.63         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '8'])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['4', '9'])).
% 0.46/0.63  thf(d2_tops_2, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @
% 0.46/0.63             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63           ( ( v2_tops_2 @ B @ A ) <=>
% 0.46/0.63             ( ![C:$i]:
% 0.46/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X12 @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.46/0.63          | (m1_subset_1 @ (sk_C @ X12 @ X13) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.46/0.63          | (v2_tops_2 @ X12 @ X13)
% 0.46/0.63          | ~ (l1_pre_topc @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 0.46/0.63        | (m1_subset_1 @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (((v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 0.46/0.63        | (m1_subset_1 @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (~ (v2_tops_2 @ 
% 0.46/0.63          (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63          sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1)
% 0.46/0.63         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '8'])).
% 0.46/0.63  thf('17', plain, (~ (v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      ((m1_subset_1 @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('clc', [status(thm)], ['14', '17'])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X12 @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.46/0.63          | ~ (v2_tops_2 @ X12 @ X13)
% 0.46/0.63          | ~ (r2_hidden @ X14 @ X12)
% 0.46/0.63          | (v4_pre_topc @ X14 @ X13)
% 0.46/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.46/0.63          | ~ (l1_pre_topc @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ sk_A)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ X0 @ sk_B)
% 0.46/0.63          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.63  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('23', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      ((~ (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_B)
% 0.46/0.63        | (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['18', '24'])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      ((m1_subset_1 @ 
% 0.46/0.63        (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '3'])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X12 @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.46/0.63          | ~ (v4_pre_topc @ (sk_C @ X12 @ X13) @ X13)
% 0.46/0.63          | (v2_tops_2 @ X12 @ X13)
% 0.46/0.63          | ~ (l1_pre_topc @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (v2_tops_2 @ 
% 0.46/0.63           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63           sk_A)
% 0.46/0.63        | ~ (v4_pre_topc @ 
% 0.46/0.63             (sk_C @ 
% 0.46/0.63              (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 0.46/0.63               sk_C_1) @ 
% 0.46/0.63              sk_A) @ 
% 0.46/0.63             sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.63  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      (((v2_tops_2 @ 
% 0.46/0.63         (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63         sk_A)
% 0.46/0.63        | ~ (v4_pre_topc @ 
% 0.46/0.63             (sk_C @ 
% 0.46/0.63              (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 0.46/0.63               sk_C_1) @ 
% 0.46/0.63              sk_A) @ 
% 0.46/0.63             sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (~ (v2_tops_2 @ 
% 0.46/0.63          (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63          sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      (~ (v4_pre_topc @ 
% 0.46/0.63          (sk_C @ 
% 0.46/0.63           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63           sk_A) @ 
% 0.46/0.63          sk_A)),
% 0.46/0.63      inference('clc', [status(thm)], ['30', '31'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1)
% 0.46/0.63         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '8'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (~ (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (~ (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_B)),
% 0.46/0.63      inference('clc', [status(thm)], ['25', '34'])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      ((m1_subset_1 @ 
% 0.46/0.63        (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '3'])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X12 @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.46/0.63          | (r2_hidden @ (sk_C @ X12 @ X13) @ X12)
% 0.46/0.63          | (v2_tops_2 @ X12 @ X13)
% 0.46/0.63          | ~ (l1_pre_topc @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (v2_tops_2 @ 
% 0.46/0.63           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63           sk_A)
% 0.46/0.63        | (r2_hidden @ 
% 0.46/0.63           (sk_C @ 
% 0.46/0.63            (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63            sk_A) @ 
% 0.46/0.63           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.63  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (((v2_tops_2 @ 
% 0.46/0.63         (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63         sk_A)
% 0.46/0.63        | (r2_hidden @ 
% 0.46/0.63           (sk_C @ 
% 0.46/0.63            (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63            sk_A) @ 
% 0.46/0.63           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1)))),
% 0.46/0.63      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      (~ (v2_tops_2 @ 
% 0.46/0.63          (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63          sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      ((r2_hidden @ 
% 0.46/0.63        (sk_C @ 
% 0.46/0.63         (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.46/0.63         sk_A) @ 
% 0.46/0.63        (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1))),
% 0.46/0.63      inference('clc', [status(thm)], ['40', '41'])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1)
% 0.46/0.63         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '8'])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1)
% 0.46/0.63         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '8'])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      ((r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 0.46/0.63        (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.63      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.46/0.63  thf(d3_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.46/0.63       ( ![D:$i]:
% 0.46/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.63           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.63          | (r2_hidden @ X4 @ X3)
% 0.46/0.63          | (r2_hidden @ X4 @ X1)
% 0.46/0.63          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.46/0.63         ((r2_hidden @ X4 @ X1)
% 0.46/0.63          | (r2_hidden @ X4 @ X3)
% 0.46/0.63          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (((r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_B)
% 0.46/0.63        | (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_C_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['45', '47'])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      ((m1_subset_1 @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('clc', [status(thm)], ['14', '17'])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X12 @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.46/0.63          | ~ (v2_tops_2 @ X12 @ X13)
% 0.46/0.63          | ~ (r2_hidden @ X14 @ X12)
% 0.46/0.63          | (v4_pre_topc @ X14 @ X13)
% 0.46/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.46/0.63          | ~ (l1_pre_topc @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ sk_A)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.46/0.63          | ~ (v2_tops_2 @ sk_C_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.63  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('54', plain, ((v2_tops_2 @ sk_C_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.46/0.63      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.46/0.63  thf('56', plain,
% 0.46/0.63      ((~ (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_C_1)
% 0.46/0.63        | (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['49', '55'])).
% 0.46/0.63  thf('57', plain,
% 0.46/0.63      (~ (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      (~ (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_C_1)),
% 0.46/0.63      inference('clc', [status(thm)], ['56', '57'])).
% 0.46/0.63  thf('59', plain,
% 0.46/0.63      ((r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['48', '58'])).
% 0.46/0.63  thf('60', plain, ($false), inference('demod', [status(thm)], ['35', '59'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
