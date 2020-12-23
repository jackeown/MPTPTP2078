%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3dz630rMle

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 181 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  490 (2491 expanded)
%              Number of equality atoms :    6 (  77 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X5 @ X6 ) @ X6 )
      | ( v1_tops_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( v1_tops_2 @ sk_B @ sk_C_1 )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_tops_2 @ sk_B @ sk_C_1 )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ~ ( v1_tops_2 @ sk_D @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_D = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( v1_tops_2 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ( v1_tops_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( v1_tops_2 @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,
    ( ( v1_tops_2 @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_tops_2 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('21',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

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

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ X10 @ X11 )
      | ( X10 != X8 )
      | ~ ( m1_pre_topc @ X11 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('32',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X11 @ X9 )
      | ( v3_pre_topc @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_C_1 ) @ X0 )
      | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_tops_2 @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( v3_pre_topc @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    v3_pre_topc @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    v3_pre_topc @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['14','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3dz630rMle
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 27 iterations in 0.017s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(t35_tops_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @
% 0.22/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.48               ( ( v1_tops_2 @ B @ A ) =>
% 0.22/0.48                 ( ![D:$i]:
% 0.22/0.48                   ( ( m1_subset_1 @
% 0.22/0.48                       D @ 
% 0.22/0.48                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.22/0.48                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( l1_pre_topc @ A ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @
% 0.22/0.48                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.48              ( ![C:$i]:
% 0.22/0.48                ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.48                  ( ( v1_tops_2 @ B @ A ) =>
% 0.22/0.48                    ( ![D:$i]:
% 0.22/0.48                      ( ( m1_subset_1 @
% 0.22/0.48                          D @ 
% 0.22/0.48                          ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.22/0.48                        ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t35_tops_2])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_D @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, (((sk_D) = (sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf(d1_tops_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @
% 0.22/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.48           ( ( v1_tops_2 @ B @ A ) <=>
% 0.22/0.48             ( ![C:$i]:
% 0.22/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X5 @ 
% 0.22/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))
% 0.22/0.48          | ~ (v3_pre_topc @ (sk_C @ X5 @ X6) @ X6)
% 0.22/0.48          | (v1_tops_2 @ X5 @ X6)
% 0.22/0.48          | ~ (l1_pre_topc @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.48        | (v1_tops_2 @ sk_B @ sk_C_1)
% 0.22/0.48        | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_m1_pre_topc, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.48  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('9', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (((v1_tops_2 @ sk_B @ sk_C_1)
% 0.22/0.48        | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '9'])).
% 0.22/0.48  thf('11', plain, (~ (v1_tops_2 @ sk_D @ sk_C_1)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('12', plain, (((sk_D) = (sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('13', plain, (~ (v1_tops_2 @ sk_B @ sk_C_1)),
% 0.22/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain, (~ (v3_pre_topc @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)),
% 0.22/0.48      inference('clc', [status(thm)], ['10', '13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X5 @ 
% 0.22/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))
% 0.22/0.48          | (r2_hidden @ (sk_C @ X5 @ X6) @ X5)
% 0.22/0.48          | (v1_tops_2 @ X5 @ X6)
% 0.22/0.48          | ~ (l1_pre_topc @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.48        | (v1_tops_2 @ sk_B @ sk_C_1)
% 0.22/0.48        | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (((v1_tops_2 @ sk_B @ sk_C_1)
% 0.22/0.48        | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf('20', plain, (~ (v1_tops_2 @ sk_B @ sk_C_1)),
% 0.22/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('21', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 0.22/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t4_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.48       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.22/0.48          | (m1_subset_1 @ X0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      ((m1_subset_1 @ (sk_C @ sk_B @ sk_C_1) @ 
% 0.22/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['21', '24'])).
% 0.22/0.48  thf('26', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 0.22/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.22/0.48          | (m1_subset_1 @ X0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      ((m1_subset_1 @ (sk_C @ sk_B @ sk_C_1) @ 
% 0.22/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.48  thf(t33_tops_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.48               ( ( v3_pre_topc @ B @ A ) =>
% 0.22/0.48                 ( ![D:$i]:
% 0.22/0.48                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.22/0.48                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.48          | ~ (v3_pre_topc @ X8 @ X9)
% 0.22/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.48          | (v3_pre_topc @ X10 @ X11)
% 0.22/0.48          | ((X10) != (X8))
% 0.22/0.48          | ~ (m1_pre_topc @ X11 @ X9)
% 0.22/0.48          | ~ (l1_pre_topc @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.22/0.48  thf('32', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X9)
% 0.22/0.48          | ~ (m1_pre_topc @ X11 @ X9)
% 0.22/0.48          | (v3_pre_topc @ X8 @ X11)
% 0.22/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.48          | ~ (v3_pre_topc @ X8 @ X9)
% 0.22/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.48  thf('33', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ (sk_C @ sk_B @ sk_C_1) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.48          | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_C_1) @ X0)
% 0.22/0.48          | (v3_pre_topc @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)
% 0.22/0.48          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.22/0.48          | ~ (l1_pre_topc @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['30', '32'])).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.22/0.48        | (v3_pre_topc @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)
% 0.22/0.48        | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_C_1) @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['25', '33'])).
% 0.22/0.48  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('36', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('37', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 0.22/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('39', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X5 @ 
% 0.22/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))
% 0.22/0.48          | ~ (v1_tops_2 @ X5 @ X6)
% 0.22/0.48          | ~ (r2_hidden @ X7 @ X5)
% 0.22/0.48          | (v3_pre_topc @ X7 @ X6)
% 0.22/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.48          | ~ (l1_pre_topc @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.22/0.48  thf('40', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (v3_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.48          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.48  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('42', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('43', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (v3_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.48  thf('44', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf('45', plain,
% 0.22/0.48      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (v3_pre_topc @ X0 @ sk_A))),
% 0.22/0.48      inference('clc', [status(thm)], ['43', '44'])).
% 0.22/0.48  thf('46', plain, ((v3_pre_topc @ (sk_C @ sk_B @ sk_C_1) @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['37', '45'])).
% 0.22/0.48  thf('47', plain, ((v3_pre_topc @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)),
% 0.22/0.48      inference('demod', [status(thm)], ['34', '35', '36', '46'])).
% 0.22/0.48  thf('48', plain, ($false), inference('demod', [status(thm)], ['14', '47'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
