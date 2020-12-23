%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ri1YgWXzH1

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:24 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 173 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  607 (3035 expanded)
%              Number of equality atoms :    9 ( 136 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t20_waybel_9,conjecture,(
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
                      & ( v2_tops_2 @ C @ A ) )
                   => ( v2_tops_2 @ D @ B ) ) ) ) ) ) )).

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
                        & ( v2_tops_2 @ C @ A ) )
                     => ( v2_tops_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_waybel_9])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ X7 @ X8 ) @ X8 )
      | ( v2_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v2_tops_2 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v2_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( v2_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('17',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['15','16'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t34_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v4_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ( X12 != X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_tops_2])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v4_pre_topc @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ X0 )
      | ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('33',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( u1_pre_topc @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ( m1_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['15','16'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v2_tops_2 @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( v4_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v2_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['30','31','43','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['10','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ri1YgWXzH1
% 0.16/0.36  % Computer   : n021.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 15:54:49 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 47 iterations in 0.025s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.50  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.23/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.23/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.50  thf(t20_waybel_9, conjecture,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( l1_pre_topc @ B ) =>
% 0.23/0.50           ( ![C:$i]:
% 0.23/0.50             ( ( m1_subset_1 @
% 0.23/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.50               ( ![D:$i]:
% 0.23/0.50                 ( ( m1_subset_1 @
% 0.23/0.50                     D @ 
% 0.23/0.50                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.23/0.50                   ( ( ( ( g1_pre_topc @
% 0.23/0.50                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.23/0.50                         ( g1_pre_topc @
% 0.23/0.50                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.23/0.50                       ( ( C ) = ( D ) ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.23/0.50                     ( v2_tops_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]:
% 0.23/0.50        ( ( l1_pre_topc @ A ) =>
% 0.23/0.50          ( ![B:$i]:
% 0.23/0.50            ( ( l1_pre_topc @ B ) =>
% 0.23/0.50              ( ![C:$i]:
% 0.23/0.50                ( ( m1_subset_1 @
% 0.23/0.50                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.50                  ( ![D:$i]:
% 0.23/0.50                    ( ( m1_subset_1 @
% 0.23/0.50                        D @ 
% 0.23/0.50                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.23/0.50                      ( ( ( ( g1_pre_topc @
% 0.23/0.50                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.23/0.50                            ( g1_pre_topc @
% 0.23/0.50                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.23/0.50                          ( ( C ) = ( D ) ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.23/0.50                        ( v2_tops_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t20_waybel_9])).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_D @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('1', plain, (((sk_C_1) = (sk_D))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf(d2_tops_2, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( m1_subset_1 @
% 0.23/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.50           ( ( v2_tops_2 @ B @ A ) <=>
% 0.23/0.50             ( ![C:$i]:
% 0.23/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.50                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X7 @ 
% 0.23/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.23/0.50          | ~ (v4_pre_topc @ (sk_C @ X7 @ X8) @ X8)
% 0.23/0.50          | (v2_tops_2 @ X7 @ X8)
% 0.23/0.50          | ~ (l1_pre_topc @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.23/0.50        | (v2_tops_2 @ sk_C_1 @ sk_B)
% 0.23/0.50        | ~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.50  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (((v2_tops_2 @ sk_C_1 @ sk_B)
% 0.23/0.50        | ~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.23/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.50  thf('7', plain, (~ (v2_tops_2 @ sk_D @ sk_B)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('8', plain, (((sk_C_1) = (sk_D))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('9', plain, (~ (v2_tops_2 @ sk_C_1 @ sk_B)),
% 0.23/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.50  thf('10', plain, (~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.23/0.50      inference('clc', [status(thm)], ['6', '9'])).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X7 @ 
% 0.23/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.23/0.50          | (r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.23/0.50          | (v2_tops_2 @ X7 @ X8)
% 0.23/0.50          | ~ (l1_pre_topc @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.23/0.50        | (v2_tops_2 @ sk_C_1 @ sk_B)
% 0.23/0.50        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.23/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.50  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (((v2_tops_2 @ sk_C_1 @ sk_B)
% 0.23/0.50        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.23/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.50  thf('16', plain, (~ (v2_tops_2 @ sk_C_1 @ sk_B)),
% 0.23/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.50  thf('17', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.23/0.50      inference('clc', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t4_subset, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.23/0.50       ( m1_subset_1 @ A @ C ) ))).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.23/0.50          | (m1_subset_1 @ X0 @ X2))),
% 0.23/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.50          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.23/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.50  thf('21', plain,
% 0.23/0.50      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.23/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['17', '20'])).
% 0.23/0.50  thf('22', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.23/0.50      inference('clc', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf('23', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf('24', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.23/0.50          | (m1_subset_1 @ X0 @ X2))),
% 0.23/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.23/0.50  thf('25', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.23/0.50          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.23/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.50  thf('26', plain,
% 0.23/0.50      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.23/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['22', '25'])).
% 0.23/0.50  thf(t34_tops_2, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.50           ( ![C:$i]:
% 0.23/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.23/0.50               ( ( v4_pre_topc @ B @ A ) =>
% 0.23/0.50                 ( ![D:$i]:
% 0.23/0.50                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.23/0.50                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.50  thf('27', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.50          | ~ (v4_pre_topc @ X10 @ X11)
% 0.23/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.23/0.50          | (v4_pre_topc @ X12 @ X13)
% 0.23/0.50          | ((X12) != (X10))
% 0.23/0.50          | ~ (m1_pre_topc @ X13 @ X11)
% 0.23/0.50          | ~ (l1_pre_topc @ X11))),
% 0.23/0.50      inference('cnf', [status(esa)], [t34_tops_2])).
% 0.23/0.50  thf('28', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.23/0.50         (~ (l1_pre_topc @ X11)
% 0.23/0.50          | ~ (m1_pre_topc @ X13 @ X11)
% 0.23/0.50          | (v4_pre_topc @ X10 @ X13)
% 0.23/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.23/0.50          | ~ (v4_pre_topc @ X10 @ X11)
% 0.23/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.23/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.50  thf('29', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.23/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.50          | ~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ X0)
% 0.23/0.50          | (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.23/0.50          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.23/0.50          | ~ (l1_pre_topc @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['26', '28'])).
% 0.23/0.50  thf('30', plain,
% 0.23/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.50        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.23/0.50        | (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.23/0.50        | ~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['21', '29'])).
% 0.23/0.50  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('32', plain,
% 0.23/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.23/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t2_tsep_1, axiom,
% 0.23/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.23/0.50  thf('33', plain,
% 0.23/0.50      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.23/0.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.23/0.50  thf(t65_pre_topc, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( l1_pre_topc @ B ) =>
% 0.23/0.50           ( ( m1_pre_topc @ A @ B ) <=>
% 0.23/0.50             ( m1_pre_topc @
% 0.23/0.50               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.23/0.50  thf('34', plain,
% 0.23/0.50      (![X5 : $i, X6 : $i]:
% 0.23/0.50         (~ (l1_pre_topc @ X5)
% 0.23/0.50          | ~ (m1_pre_topc @ X6 @ X5)
% 0.23/0.50          | (m1_pre_topc @ X6 @ 
% 0.23/0.50             (g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5)))
% 0.23/0.50          | ~ (l1_pre_topc @ X6))),
% 0.23/0.50      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.23/0.50  thf('35', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (l1_pre_topc @ X0)
% 0.23/0.50          | ~ (l1_pre_topc @ X0)
% 0.23/0.50          | (m1_pre_topc @ X0 @ 
% 0.23/0.50             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.23/0.50          | ~ (l1_pre_topc @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.50  thf('36', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((m1_pre_topc @ X0 @ 
% 0.23/0.50           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.23/0.50          | ~ (l1_pre_topc @ X0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['35'])).
% 0.23/0.50  thf('37', plain,
% 0.23/0.50      (((m1_pre_topc @ sk_B @ 
% 0.23/0.50         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.23/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.23/0.50      inference('sup+', [status(thm)], ['32', '36'])).
% 0.23/0.50  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('39', plain,
% 0.23/0.50      ((m1_pre_topc @ sk_B @ 
% 0.23/0.50        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.23/0.50  thf(t59_pre_topc, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( m1_pre_topc @
% 0.23/0.50             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.23/0.50           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.23/0.50  thf('40', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i]:
% 0.23/0.50         (~ (m1_pre_topc @ X3 @ 
% 0.23/0.50             (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.23/0.50          | (m1_pre_topc @ X3 @ X4)
% 0.23/0.50          | ~ (l1_pre_topc @ X4))),
% 0.23/0.50      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.23/0.50  thf('41', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.23/0.50  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.23/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.23/0.50  thf('44', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.23/0.50      inference('clc', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf('45', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('46', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X7 @ 
% 0.23/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.23/0.50          | ~ (v2_tops_2 @ X7 @ X8)
% 0.23/0.50          | ~ (r2_hidden @ X9 @ X7)
% 0.23/0.50          | (v4_pre_topc @ X9 @ X8)
% 0.23/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.23/0.50          | ~ (l1_pre_topc @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.23/0.50  thf('47', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (l1_pre_topc @ sk_A)
% 0.23/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.50          | (v4_pre_topc @ X0 @ sk_A)
% 0.23/0.50          | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.23/0.50          | ~ (v2_tops_2 @ sk_C_1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.23/0.50  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('49', plain, ((v2_tops_2 @ sk_C_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('50', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.50          | (v4_pre_topc @ X0 @ sk_A)
% 0.23/0.50          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.23/0.50      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.23/0.50  thf('51', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.50          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.23/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.50  thf('52', plain,
% 0.23/0.50      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_1) | (v4_pre_topc @ X0 @ sk_A))),
% 0.23/0.50      inference('clc', [status(thm)], ['50', '51'])).
% 0.23/0.50  thf('53', plain, ((v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)),
% 0.23/0.50      inference('sup-', [status(thm)], ['44', '52'])).
% 0.23/0.50  thf('54', plain, ((v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.23/0.50      inference('demod', [status(thm)], ['30', '31', '43', '53'])).
% 0.23/0.50  thf('55', plain, ($false), inference('demod', [status(thm)], ['10', '54'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
