%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZU2mSabxVj

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 233 expanded)
%              Number of leaves         :   21 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  574 (3086 expanded)
%              Number of equality atoms :    8 (  97 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t35_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v1_tops_2 @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                   => ( ( D = B )
                     => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v1_tops_2 @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                     => ( ( D = B )
                       => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C_1 @ X13 @ X14 ) @ X14 )
      | ( v1_tops_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_C_2 )
    | ( v1_tops_2 @ sk_B @ sk_C_2 )
    | ~ ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_tops_2 @ sk_B @ sk_C_2 )
    | ~ ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ~ ( v1_tops_2 @ sk_D @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_D = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( v1_tops_2 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X14 ) @ X13 )
      | ( v1_tops_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_C_2 )
    | ( v1_tops_2 @ sk_B @ sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,
    ( ( v1_tops_2 @ sk_B @ sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_tops_2 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('21',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    r1_tarski @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('37',plain,(
    r1_tarski @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( u1_struct_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

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

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ X18 @ X19 )
      | ( X18 != X16 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v3_pre_topc @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ X0 )
      | ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_C_2 )
      | ~ ( m1_pre_topc @ sk_C_2 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_2 @ sk_A )
    | ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_C_2 )
    | ~ ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_tops_2 @ X13 @ X14 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ( v3_pre_topc @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
    | ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('55',plain,(
    v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_C_2 ),
    inference(demod,[status(thm)],['43','44','45','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['14','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZU2mSabxVj
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 116 iterations in 0.064s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.53  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(t35_tops_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @
% 0.21/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.53               ( ( v1_tops_2 @ B @ A ) =>
% 0.21/0.53                 ( ![D:$i]:
% 0.21/0.53                   ( ( m1_subset_1 @
% 0.21/0.53                       D @ 
% 0.21/0.53                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.21/0.53                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( l1_pre_topc @ A ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @
% 0.21/0.53                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.53                  ( ( v1_tops_2 @ B @ A ) =>
% 0.21/0.53                    ( ![D:$i]:
% 0.21/0.53                      ( ( m1_subset_1 @
% 0.21/0.53                          D @ 
% 0.21/0.53                          ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.21/0.53                        ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t35_tops_2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain, (((sk_D) = (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2))))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf(d1_tops_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @
% 0.21/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53           ( ( v1_tops_2 @ B @ A ) <=>
% 0.21/0.53             ( ![C:$i]:
% 0.21/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X13 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.21/0.53          | ~ (v3_pre_topc @ (sk_C_1 @ X13 @ X14) @ X14)
% 0.21/0.53          | (v1_tops_2 @ X13 @ X14)
% 0.21/0.53          | ~ (l1_pre_topc @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_C_2)
% 0.21/0.53        | (v1_tops_2 @ sk_B @ sk_C_2)
% 0.21/0.53        | ~ (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_C_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_m1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.53          | (l1_pre_topc @ X11)
% 0.21/0.53          | ~ (l1_pre_topc @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.53  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('9', plain, ((l1_pre_topc @ sk_C_2)),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (((v1_tops_2 @ sk_B @ sk_C_2)
% 0.21/0.53        | ~ (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_C_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '9'])).
% 0.21/0.53  thf('11', plain, (~ (v1_tops_2 @ sk_D @ sk_C_2)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain, (((sk_D) = (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain, (~ (v1_tops_2 @ sk_B @ sk_C_2)),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, (~ (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_C_2)),
% 0.21/0.53      inference('clc', [status(thm)], ['10', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2))))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X13 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.21/0.53          | (r2_hidden @ (sk_C_1 @ X13 @ X14) @ X13)
% 0.21/0.53          | (v1_tops_2 @ X13 @ X14)
% 0.21/0.53          | ~ (l1_pre_topc @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_C_2)
% 0.21/0.53        | (v1_tops_2 @ sk_B @ sk_C_2)
% 0.21/0.53        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, ((l1_pre_topc @ sk_C_2)),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (((v1_tops_2 @ sk_B @ sk_C_2)
% 0.21/0.53        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('20', plain, (~ (v1_tops_2 @ sk_B @ sk_C_2)),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('21', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(l3_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.53          | (r2_hidden @ X5 @ X7)
% 0.21/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.53  thf(d1_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X3 @ X2)
% 0.21/0.53          | (r1_tarski @ X3 @ X1)
% 0.21/0.53          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((r1_tarski @ (sk_C_1 @ sk_B @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X8 : $i, X10 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_C_2) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2))))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.53          | (r2_hidden @ X5 @ X7)
% 0.21/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((r1_tarski @ (sk_C_1 @ sk_B @ sk_C_2) @ (u1_struct_0 @ sk_C_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X8 : $i, X10 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_C_2) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf(t33_tops_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.54               ( ( v3_pre_topc @ B @ A ) =>
% 0.21/0.54                 ( ![D:$i]:
% 0.21/0.54                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.54                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.54          | ~ (v3_pre_topc @ X16 @ X17)
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.54          | (v3_pre_topc @ X18 @ X19)
% 0.21/0.54          | ((X18) != (X16))
% 0.21/0.54          | ~ (m1_pre_topc @ X19 @ X17)
% 0.21/0.54          | ~ (l1_pre_topc @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X17)
% 0.21/0.54          | ~ (m1_pre_topc @ X19 @ X17)
% 0.21/0.54          | (v3_pre_topc @ X16 @ X19)
% 0.21/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.54          | ~ (v3_pre_topc @ X16 @ X17)
% 0.21/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_C_2) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.54          | ~ (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ X0)
% 0.21/0.54          | (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_C_2)
% 0.21/0.54          | ~ (m1_pre_topc @ sk_C_2 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ~ (m1_pre_topc @ sk_C_2 @ sk_A)
% 0.21/0.54        | (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_C_2)
% 0.21/0.54        | ~ (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '42'])).
% 0.21/0.54  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_C_2) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X13 @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.21/0.54          | ~ (v1_tops_2 @ X13 @ X14)
% 0.21/0.54          | ~ (r2_hidden @ X15 @ X13)
% 0.21/0.54          | (v3_pre_topc @ X15 @ X14)
% 0.21/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.54          | ~ (l1_pre_topc @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (v3_pre_topc @ X0 @ sk_A)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.54          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.54  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('51', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (v3_pre_topc @ X0 @ sk_A)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 0.21/0.54        | (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['46', '52'])).
% 0.21/0.54  thf('54', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 0.21/0.54      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('55', plain, ((v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain, ((v3_pre_topc @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_C_2)),
% 0.21/0.54      inference('demod', [status(thm)], ['43', '44', '45', '55'])).
% 0.21/0.54  thf('57', plain, ($false), inference('demod', [status(thm)], ['14', '56'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
