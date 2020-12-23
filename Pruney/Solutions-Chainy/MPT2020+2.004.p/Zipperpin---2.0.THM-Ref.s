%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gBJbYz5kp8

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 229 expanded)
%              Number of leaves         :   22 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  656 (4039 expanded)
%              Number of equality atoms :    9 ( 175 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(t19_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( C = D )
                      & ( v1_tops_2 @ C @ A ) )
                   => ( v1_tops_2 @ D @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                   => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                        & ( C = D )
                        & ( v1_tops_2 @ C @ A ) )
                     => ( v1_tops_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_waybel_9])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X9 @ X10 ) @ X10 )
      | ( v1_tops_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v1_tops_2 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( ( m1_pre_topc @ X16 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ( m1_pre_topc @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_tops_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('29',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ X14 @ X15 )
      | ( X14 != X12 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ( v3_pre_topc @ X12 @ X15 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ X0 )
      | ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf('42',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_tops_2 @ X9 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( v3_pre_topc @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v1_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X9 @ X10 ) @ X9 )
      | ( v1_tops_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('56',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['49','56'])).

thf('58',plain,(
    v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['39','40','41','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['10','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gBJbYz5kp8
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:31:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 50 iterations in 0.027s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.48  thf(t19_waybel_9, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( l1_pre_topc @ B ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @
% 0.20/0.48                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( m1_subset_1 @
% 0.20/0.48                     D @ 
% 0.20/0.48                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.48                   ( ( ( ( g1_pre_topc @
% 0.20/0.48                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.48                         ( g1_pre_topc @
% 0.20/0.48                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.48                       ( ( C ) = ( D ) ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.20/0.48                     ( v1_tops_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_pre_topc @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( l1_pre_topc @ B ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_subset_1 @
% 0.20/0.48                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48                  ( ![D:$i]:
% 0.20/0.48                    ( ( m1_subset_1 @
% 0.20/0.48                        D @ 
% 0.20/0.48                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.48                      ( ( ( ( g1_pre_topc @
% 0.20/0.48                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.48                            ( g1_pre_topc @
% 0.20/0.48                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.48                          ( ( C ) = ( D ) ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.20/0.48                        ( v1_tops_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t19_waybel_9])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, (((sk_C_1) = (sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(d1_tops_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @
% 0.20/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48           ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.48          | ~ (v3_pre_topc @ (sk_C @ X9 @ X10) @ X10)
% 0.20/0.48          | (v1_tops_2 @ X9 @ X10)
% 0.20/0.48          | ~ (l1_pre_topc @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.48        | (v1_tops_2 @ sk_C_1 @ sk_B)
% 0.20/0.48        | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (((v1_tops_2 @ sk_C_1 @ sk_B)
% 0.20/0.48        | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain, (~ (v1_tops_2 @ sk_D @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain, (((sk_C_1) = (sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain, (~ (v1_tops_2 @ sk_C_1 @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain, (~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.20/0.48      inference('clc', [status(thm)], ['6', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t2_tsep_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X16 : $i]: ((m1_pre_topc @ X16 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.48  thf(t65_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( l1_pre_topc @ B ) =>
% 0.20/0.48           ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.48             ( m1_pre_topc @
% 0.20/0.48               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (m1_pre_topc @ X8 @ X7)
% 0.20/0.48          | (m1_pre_topc @ X8 @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.20/0.48          | ~ (l1_pre_topc @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (m1_pre_topc @ X0 @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((m1_pre_topc @ X0 @ 
% 0.20/0.48           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_B @ 
% 0.20/0.48         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['11', '15'])).
% 0.20/0.48  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((m1_pre_topc @ sk_B @ 
% 0.20/0.48        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf(t59_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @
% 0.20/0.48             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.48           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X5 @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.20/0.48          | (m1_pre_topc @ X5 @ X6)
% 0.20/0.48          | ~ (l1_pre_topc @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.48  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ X9 @ X10) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.48          | (v1_tops_2 @ X9 @ X10)
% 0.20/0.48          | ~ (l1_pre_topc @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.48        | (v1_tops_2 @ sk_C_1 @ sk_B)
% 0.20/0.48        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((v1_tops_2 @ sk_C_1 @ sk_B)
% 0.20/0.48        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, (~ (v1_tops_2 @ sk_C_1 @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf(t39_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.48               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X2 @ X3)
% 0.20/0.48          | (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.48          | ~ (l1_pre_topc @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '31'])).
% 0.20/0.48  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf(t33_tops_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.48               ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.48                 ( ![D:$i]:
% 0.20/0.48                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.48                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.48          | ~ (v3_pre_topc @ X12 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.48          | (v3_pre_topc @ X14 @ X15)
% 0.20/0.48          | ((X14) != (X12))
% 0.20/0.48          | ~ (m1_pre_topc @ X15 @ X13)
% 0.20/0.48          | ~ (l1_pre_topc @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X13)
% 0.20/0.48          | ~ (m1_pre_topc @ X15 @ X13)
% 0.20/0.48          | (v3_pre_topc @ X12 @ X15)
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.48          | ~ (v3_pre_topc @ X12 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ X0)
% 0.20/0.48          | (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.48        | (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.20/0.48        | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '38'])).
% 0.20/0.48  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.48          | ~ (v1_tops_2 @ X9 @ X10)
% 0.20/0.48          | ~ (r2_hidden @ X11 @ X9)
% 0.20/0.48          | (v3_pre_topc @ X11 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.48          | ~ (l1_pre_topc @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.48          | ~ (v1_tops_2 @ sk_C_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain, ((v1_tops_2 @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      ((~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.20/0.48        | (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.48          | (r2_hidden @ (sk_C @ X9 @ X10) @ X9)
% 0.20/0.48          | (v1_tops_2 @ X9 @ X10)
% 0.20/0.48          | ~ (l1_pre_topc @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.48        | (v1_tops_2 @ sk_C_1 @ sk_B)
% 0.20/0.48        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (((v1_tops_2 @ sk_C_1 @ sk_B)
% 0.20/0.48        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.48  thf('55', plain, (~ (v1_tops_2 @ sk_C_1 @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('56', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.20/0.48      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.48  thf('57', plain, ((v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '56'])).
% 0.20/0.48  thf('58', plain, ((v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['39', '40', '41', '57'])).
% 0.20/0.48  thf('59', plain, ($false), inference('demod', [status(thm)], ['10', '58'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
