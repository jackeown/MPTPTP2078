%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jf0zcALqMv

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:17 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 142 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  639 (1550 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t48_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_pre_topc])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['9','10'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( v4_pre_topc @ D @ A )
                        & ( r1_tarski @ B @ D ) )
                     => ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ X11 @ ( sk_D_1 @ X13 @ X11 @ X12 ) )
      | ( r2_hidden @ X13 @ ( k2_pre_topc @ X12 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_B @ ( sk_D_1 @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( sk_D_1 @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( sk_D_1 @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_hidden @ X13 @ ( sk_D_1 @ X13 @ X11 @ X12 ) )
      | ( r2_hidden @ X13 @ ( k2_pre_topc @ X12 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jf0zcALqMv
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.72  % Solved by: fo/fo7.sh
% 0.50/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.72  % done 255 iterations in 0.272s
% 0.50/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.72  % SZS output start Refutation
% 0.50/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.72  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.50/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.50/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.72  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.50/0.72  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.50/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.72  thf(t48_pre_topc, conjecture,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( l1_pre_topc @ A ) =>
% 0.50/0.72       ( ![B:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.72           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.72    (~( ![A:$i]:
% 0.50/0.72        ( ( l1_pre_topc @ A ) =>
% 0.50/0.72          ( ![B:$i]:
% 0.50/0.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.72              ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ) )),
% 0.50/0.72    inference('cnf.neg', [status(esa)], [t48_pre_topc])).
% 0.50/0.72  thf('0', plain, (~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('1', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('2', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(dt_k2_pre_topc, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( ( l1_pre_topc @ A ) & 
% 0.50/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.72       ( m1_subset_1 @
% 0.50/0.72         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.50/0.72  thf('3', plain,
% 0.50/0.72      (![X9 : $i, X10 : $i]:
% 0.50/0.72         (~ (l1_pre_topc @ X9)
% 0.50/0.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.50/0.72          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 0.50/0.72             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.50/0.72      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.50/0.72  thf('4', plain,
% 0.50/0.72      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.50/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('6', plain,
% 0.50/0.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.50/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.72  thf(t7_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ![C:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72           ( ( ![D:$i]:
% 0.50/0.72               ( ( m1_subset_1 @ D @ A ) =>
% 0.50/0.72                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.50/0.72             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.50/0.72  thf('7', plain,
% 0.50/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.50/0.72          | (r1_tarski @ X5 @ X3)
% 0.50/0.72          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.50/0.72          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.50/0.72      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.50/0.72  thf('8', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.72          | (r2_hidden @ 
% 0.50/0.72             (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72             X0)
% 0.50/0.72          | (r1_tarski @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.72  thf('9', plain,
% 0.50/0.72      (((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72        | (r2_hidden @ 
% 0.50/0.72           (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72           sk_B))),
% 0.50/0.72      inference('sup-', [status(thm)], ['1', '8'])).
% 0.50/0.72  thf('10', plain, (~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('11', plain,
% 0.50/0.72      ((r2_hidden @ 
% 0.50/0.72        (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72        sk_B)),
% 0.50/0.72      inference('clc', [status(thm)], ['9', '10'])).
% 0.50/0.72  thf('12', plain,
% 0.50/0.72      ((r2_hidden @ 
% 0.50/0.72        (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72        sk_B)),
% 0.50/0.72      inference('clc', [status(thm)], ['9', '10'])).
% 0.50/0.72  thf('13', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(l3_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.50/0.72  thf('14', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.72          | (r2_hidden @ X0 @ X2)
% 0.50/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.50/0.72      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.50/0.72  thf('15', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.50/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.50/0.72  thf('16', plain,
% 0.50/0.72      ((r2_hidden @ 
% 0.50/0.72        (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72        (u1_struct_0 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['12', '15'])).
% 0.50/0.72  thf('17', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t45_pre_topc, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( l1_pre_topc @ A ) =>
% 0.50/0.72       ( ![B:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.72           ( ![C:$i]:
% 0.50/0.72             ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.72               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.50/0.72                 ( ![D:$i]:
% 0.50/0.72                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.72                     ( ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) =>
% 0.50/0.72                       ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.72  thf('18', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.50/0.72          | (r1_tarski @ X11 @ (sk_D_1 @ X13 @ X11 @ X12))
% 0.50/0.72          | (r2_hidden @ X13 @ (k2_pre_topc @ X12 @ X11))
% 0.50/0.72          | ~ (r2_hidden @ X13 @ (u1_struct_0 @ X12))
% 0.50/0.72          | ~ (l1_pre_topc @ X12))),
% 0.50/0.72      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.50/0.72  thf('19', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (~ (l1_pre_topc @ sk_A)
% 0.50/0.72          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.50/0.72          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72          | (r1_tarski @ sk_B @ (sk_D_1 @ X0 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.72  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('21', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.50/0.72          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72          | (r1_tarski @ sk_B @ (sk_D_1 @ X0 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['19', '20'])).
% 0.50/0.72  thf('22', plain,
% 0.50/0.72      (((r1_tarski @ sk_B @ 
% 0.50/0.72         (sk_D_1 @ 
% 0.50/0.72          (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72          sk_B @ sk_A))
% 0.50/0.72        | (r2_hidden @ 
% 0.50/0.72           (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72           (k2_pre_topc @ sk_A @ sk_B)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['16', '21'])).
% 0.50/0.72  thf(t3_subset, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.72  thf('23', plain,
% 0.50/0.72      (![X6 : $i, X8 : $i]:
% 0.50/0.72         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.50/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.72  thf('24', plain,
% 0.50/0.72      (((r2_hidden @ 
% 0.50/0.72         (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72         (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72        | (m1_subset_1 @ sk_B @ 
% 0.50/0.72           (k1_zfmisc_1 @ 
% 0.50/0.72            (sk_D_1 @ 
% 0.50/0.72             (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72             sk_B @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.50/0.72  thf('25', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.72          | (r2_hidden @ X0 @ X2)
% 0.50/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.50/0.72      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.50/0.72  thf('26', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ 
% 0.50/0.72           (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72           (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72          | (r2_hidden @ X0 @ 
% 0.50/0.72             (sk_D_1 @ 
% 0.50/0.72              (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72              sk_B @ sk_A))
% 0.50/0.72          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.50/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.72  thf('27', plain,
% 0.50/0.72      (((r2_hidden @ 
% 0.50/0.72         (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72         (sk_D_1 @ 
% 0.50/0.72          (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72          sk_B @ sk_A))
% 0.50/0.72        | (r2_hidden @ 
% 0.50/0.72           (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72           (k2_pre_topc @ sk_A @ sk_B)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['11', '26'])).
% 0.50/0.72  thf('28', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('29', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.50/0.72          | ~ (r2_hidden @ X13 @ (sk_D_1 @ X13 @ X11 @ X12))
% 0.50/0.72          | (r2_hidden @ X13 @ (k2_pre_topc @ X12 @ X11))
% 0.50/0.72          | ~ (r2_hidden @ X13 @ (u1_struct_0 @ X12))
% 0.50/0.72          | ~ (l1_pre_topc @ X12))),
% 0.50/0.72      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.50/0.72  thf('30', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (~ (l1_pre_topc @ sk_A)
% 0.50/0.72          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.50/0.72          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72          | ~ (r2_hidden @ X0 @ (sk_D_1 @ X0 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.72  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('32', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.50/0.72          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72          | ~ (r2_hidden @ X0 @ (sk_D_1 @ X0 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['30', '31'])).
% 0.50/0.72  thf('33', plain,
% 0.50/0.72      (((r2_hidden @ 
% 0.50/0.72         (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72         (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72        | (r2_hidden @ 
% 0.50/0.72           (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72           (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72        | ~ (r2_hidden @ 
% 0.50/0.72             (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72             (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['27', '32'])).
% 0.50/0.72  thf('34', plain,
% 0.50/0.72      ((r2_hidden @ 
% 0.50/0.72        (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72        (u1_struct_0 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['12', '15'])).
% 0.50/0.72  thf('35', plain,
% 0.50/0.72      (((r2_hidden @ 
% 0.50/0.72         (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72         (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72        | (r2_hidden @ 
% 0.50/0.72           (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72           (k2_pre_topc @ sk_A @ sk_B)))),
% 0.50/0.72      inference('demod', [status(thm)], ['33', '34'])).
% 0.50/0.72  thf('36', plain,
% 0.50/0.72      ((r2_hidden @ 
% 0.50/0.72        (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72        (k2_pre_topc @ sk_A @ sk_B))),
% 0.50/0.72      inference('simplify', [status(thm)], ['35'])).
% 0.50/0.72  thf('37', plain,
% 0.50/0.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.50/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.72  thf('38', plain,
% 0.50/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.50/0.72          | (r1_tarski @ X5 @ X3)
% 0.50/0.72          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.50/0.72          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.50/0.72      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.50/0.72  thf('39', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.72          | ~ (r2_hidden @ 
% 0.50/0.72               (sk_D @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.50/0.72               (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72          | (r1_tarski @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.72  thf('40', plain,
% 0.50/0.72      (((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 0.50/0.72        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['36', '39'])).
% 0.50/0.72  thf('41', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('42', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.50/0.72      inference('demod', [status(thm)], ['40', '41'])).
% 0.50/0.72  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.50/0.72  
% 0.50/0.72  % SZS output end Refutation
% 0.50/0.72  
% 0.50/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
