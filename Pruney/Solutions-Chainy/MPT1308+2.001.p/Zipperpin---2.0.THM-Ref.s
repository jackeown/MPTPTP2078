%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NWFYzaA9Yp

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:28 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 139 expanded)
%              Number of leaves         :   42 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  699 (1293 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t26_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
           => ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_tops_2 @ B @ A )
             => ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r2_hidden @ X39 @ ( u1_pre_topc @ X40 ) )
      | ( v3_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('17',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('22',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_tops_2 @ X41 @ X42 )
      | ~ ( r2_hidden @ X43 @ X41 )
      | ( v3_pre_topc @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v1_tops_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_tops_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ sk_B_2 )
      | ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('31',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v3_pre_topc @ X39 @ X40 )
      | ( r2_hidden @ X39 @ ( u1_pre_topc @ X40 ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf('40',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( u1_pre_topc @ X31 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ ( u1_pre_topc @ X31 ) )
      | ~ ( zip_tseitin_4 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,
    ( ~ ( zip_tseitin_4 @ sk_B_2 @ sk_A )
    | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
      | ( zip_tseitin_4 @ X33 @ X34 )
      | ~ ( zip_tseitin_5 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('44',plain,
    ( ~ ( zip_tseitin_5 @ sk_B_2 @ sk_A )
    | ( zip_tseitin_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('46',plain,(
    ! [X36: $i,X38: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ( zip_tseitin_5 @ X38 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    zip_tseitin_4 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['41','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['8','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NWFYzaA9Yp
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 228 iterations in 0.106s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.39/0.57  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.39/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.57  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.39/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.39/0.57  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.57  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.39/0.57  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.57  thf(t26_tops_2, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @
% 0.39/0.57             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.57           ( ( v1_tops_2 @ B @ A ) =>
% 0.39/0.57             ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( m1_subset_1 @
% 0.39/0.57                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.57              ( ( v1_tops_2 @ B @ A ) =>
% 0.39/0.57                ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t26_tops_2])).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B_2 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_k5_setfam_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.57       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k5_setfam_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.39/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.57  thf(d5_pre_topc, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57           ( ( v3_pre_topc @ B @ A ) <=>
% 0.39/0.57             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X39 : $i, X40 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.39/0.57          | ~ (r2_hidden @ X39 @ (u1_pre_topc @ X40))
% 0.39/0.57          | (v3_pre_topc @ X39 @ X40)
% 0.39/0.57          | ~ (l1_pre_topc @ X40))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.39/0.57        | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.57             (u1_pre_topc @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (((v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.39/0.57        | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.57             (u1_pre_topc @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (~ (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.57          (u1_pre_topc @ sk_A))),
% 0.39/0.57      inference('clc', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf(d3_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X1 : $i, X3 : $i]:
% 0.39/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B_2 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t3_subset, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i]:
% 0.39/0.57         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      ((r1_tarski @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.57          | (r2_hidden @ X0 @ X2)
% 0.39/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['9', '14'])).
% 0.39/0.57  thf(d1_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X7 @ X6)
% 0.39/0.57          | (r1_tarski @ X7 @ X5)
% 0.39/0.57          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X5 : $i, X7 : $i]:
% 0.39/0.57         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.57          | (r1_tarski @ (sk_C @ X0 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X11 : $i, X13 : $i]:
% 0.39/0.57         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.57          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_2) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B_2 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d1_tops_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @
% 0.39/0.57             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.57           ( ( v1_tops_2 @ B @ A ) <=>
% 0.39/0.57             ( ![C:$i]:
% 0.39/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X41 @ 
% 0.39/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42))))
% 0.39/0.57          | ~ (v1_tops_2 @ X41 @ X42)
% 0.39/0.57          | ~ (r2_hidden @ X43 @ X41)
% 0.39/0.57          | (v3_pre_topc @ X43 @ X42)
% 0.39/0.57          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.39/0.57          | ~ (l1_pre_topc @ X42))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (l1_pre_topc @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | (v3_pre_topc @ X0 @ sk_A)
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.39/0.57          | ~ (v1_tops_2 @ sk_B_2 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.57  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('25', plain, ((v1_tops_2 @ sk_B_2 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | (v3_pre_topc @ X0 @ sk_A)
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.57          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ sk_B_2)
% 0.39/0.57          | (v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['20', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X1 : $i, X3 : $i]:
% 0.39/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A)
% 0.39/0.57          | (r1_tarski @ sk_B_2 @ X0))),
% 0.39/0.57      inference('clc', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.57          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_2) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X39 : $i, X40 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.39/0.57          | ~ (v3_pre_topc @ X39 @ X40)
% 0.39/0.57          | (r2_hidden @ X39 @ (u1_pre_topc @ X40))
% 0.39/0.57          | ~ (l1_pre_topc @ X40))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.39/0.57          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.39/0.57          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.39/0.57          | (r1_tarski @ sk_B_2 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['29', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.39/0.57          | (r1_tarski @ sk_B_2 @ X0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['35'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X1 : $i, X3 : $i]:
% 0.39/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.39/0.57        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.57  thf('39', plain, ((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))),
% 0.39/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.39/0.57  thf(d1_pre_topc, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ( v2_pre_topc @ A ) <=>
% 0.39/0.57         ( ( ![B:$i]:
% 0.39/0.57             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57               ( ![C:$i]:
% 0.39/0.57                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.39/0.57                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.39/0.57                     ( r2_hidden @
% 0.39/0.57                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.39/0.57                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.39/0.57           ( ![B:$i]:
% 0.39/0.57             ( ( m1_subset_1 @
% 0.39/0.57                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.57               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.39/0.57                 ( r2_hidden @
% 0.39/0.57                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.39/0.57                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.39/0.57           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_1, axiom,
% 0.39/0.57    (![B:$i,A:$i]:
% 0.39/0.57     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.39/0.57       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.39/0.57         ( r2_hidden @
% 0.39/0.57           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (![X30 : $i, X31 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X30 @ (u1_pre_topc @ X31))
% 0.39/0.57          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X31) @ X30) @ 
% 0.39/0.57             (u1_pre_topc @ X31))
% 0.39/0.57          | ~ (zip_tseitin_4 @ X30 @ X31))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      ((~ (zip_tseitin_4 @ sk_B_2 @ sk_A)
% 0.39/0.57        | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.57           (u1_pre_topc @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B_2 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(zf_stmt_2, axiom,
% 0.39/0.57    (![B:$i,A:$i]:
% 0.39/0.57     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.39/0.57       ( ( m1_subset_1 @
% 0.39/0.57           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.57         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X33 : $i, X34 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X33 @ 
% 0.39/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))
% 0.39/0.57          | (zip_tseitin_4 @ X33 @ X34)
% 0.39/0.57          | ~ (zip_tseitin_5 @ X33 @ X34))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      ((~ (zip_tseitin_5 @ sk_B_2 @ sk_A) | (zip_tseitin_4 @ sk_B_2 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.57  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(zf_stmt_3, type, zip_tseitin_5 : $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_6, axiom,
% 0.39/0.57    (![B:$i,A:$i]:
% 0.39/0.57     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.39/0.57       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_8, axiom,
% 0.39/0.57    (![C:$i,B:$i,A:$i]:
% 0.39/0.57     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.39/0.57       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.39/0.57  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_10, axiom,
% 0.39/0.57    (![C:$i,B:$i,A:$i]:
% 0.39/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.39/0.57       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.39/0.57         ( r2_hidden @
% 0.39/0.57           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_12, axiom,
% 0.39/0.57    (![C:$i,B:$i,A:$i]:
% 0.39/0.57     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.39/0.57       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.39/0.57         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_13, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ( v2_pre_topc @ A ) <=>
% 0.39/0.57         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.39/0.57           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.39/0.57           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X36 : $i, X38 : $i]:
% 0.39/0.57         (~ (v2_pre_topc @ X36)
% 0.39/0.57          | (zip_tseitin_5 @ X38 @ X36)
% 0.39/0.57          | ~ (l1_pre_topc @ X36))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (![X0 : $i]: ((zip_tseitin_5 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.57  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('49', plain, (![X0 : $i]: (zip_tseitin_5 @ X0 @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.57  thf('50', plain, ((zip_tseitin_4 @ sk_B_2 @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['44', '49'])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      ((r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.57        (u1_pre_topc @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['41', '50'])).
% 0.39/0.57  thf('52', plain, ($false), inference('demod', [status(thm)], ['8', '51'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
