%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QdwwcTiL6D

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 173 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  607 (3035 expanded)
%              Number of equality atoms :    9 ( 136 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X15 @ X16 ) @ X16 )
      | ( v1_tops_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ X15 )
      | ( v1_tops_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_tops_2 @ sk_C_1 @ sk_B ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

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

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ X20 @ X21 )
      | ( X20 != X18 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( v3_pre_topc @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ X0 )
      | ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
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
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_tops_2 @ X15 @ X16 )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ( v3_pre_topc @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v1_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
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
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['30','31','43','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['10','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QdwwcTiL6D
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:22:34 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 80 iterations in 0.037s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.48  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.19/0.48  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(t19_waybel_9, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( l1_pre_topc @ B ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @
% 0.19/0.48                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.48               ( ![D:$i]:
% 0.19/0.48                 ( ( m1_subset_1 @
% 0.19/0.48                     D @ 
% 0.19/0.48                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.19/0.48                   ( ( ( ( g1_pre_topc @
% 0.19/0.48                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.19/0.48                         ( g1_pre_topc @
% 0.19/0.48                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.19/0.48                       ( ( C ) = ( D ) ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.19/0.48                     ( v1_tops_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( l1_pre_topc @ A ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( l1_pre_topc @ B ) =>
% 0.19/0.48              ( ![C:$i]:
% 0.19/0.48                ( ( m1_subset_1 @
% 0.19/0.48                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.48                  ( ![D:$i]:
% 0.19/0.48                    ( ( m1_subset_1 @
% 0.19/0.48                        D @ 
% 0.19/0.48                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.19/0.48                      ( ( ( ( g1_pre_topc @
% 0.19/0.48                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.19/0.48                            ( g1_pre_topc @
% 0.19/0.48                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.19/0.48                          ( ( C ) = ( D ) ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.19/0.48                        ( v1_tops_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t19_waybel_9])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, (((sk_C_1) = (sk_D))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf(d1_tops_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @
% 0.19/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.48           ( ( v1_tops_2 @ B @ A ) <=>
% 0.19/0.48             ( ![C:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X15 @ 
% 0.19/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.19/0.48          | ~ (v3_pre_topc @ (sk_C @ X15 @ X16) @ X16)
% 0.19/0.48          | (v1_tops_2 @ X15 @ X16)
% 0.19/0.48          | ~ (l1_pre_topc @ X16))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_B)
% 0.19/0.48        | (v1_tops_2 @ sk_C_1 @ sk_B)
% 0.19/0.48        | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (((v1_tops_2 @ sk_C_1 @ sk_B)
% 0.19/0.48        | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf('7', plain, (~ (v1_tops_2 @ sk_D @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('8', plain, (((sk_C_1) = (sk_D))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain, (~ (v1_tops_2 @ sk_C_1 @ sk_B)),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain, (~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.19/0.48      inference('clc', [status(thm)], ['6', '9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X15 @ 
% 0.19/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.19/0.48          | (r2_hidden @ (sk_C @ X15 @ X16) @ X15)
% 0.19/0.48          | (v1_tops_2 @ X15 @ X16)
% 0.19/0.48          | ~ (l1_pre_topc @ X16))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_B)
% 0.19/0.48        | (v1_tops_2 @ sk_C_1 @ sk_B)
% 0.19/0.48        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (((v1_tops_2 @ sk_C_1 @ sk_B)
% 0.19/0.48        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain, (~ (v1_tops_2 @ sk_C_1 @ sk_B)),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('17', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.19/0.48      inference('clc', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t4_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.19/0.48       ( m1_subset_1 @ A @ C ) ))).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X6 @ X7)
% 0.19/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.19/0.48          | (m1_subset_1 @ X6 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.19/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '20'])).
% 0.19/0.48  thf('22', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.19/0.48      inference('clc', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X6 @ X7)
% 0.19/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.19/0.48          | (m1_subset_1 @ X6 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.19/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '25'])).
% 0.19/0.48  thf(t33_tops_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.48               ( ( v3_pre_topc @ B @ A ) =>
% 0.19/0.48                 ( ![D:$i]:
% 0.19/0.48                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.19/0.48                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.48          | ~ (v3_pre_topc @ X18 @ X19)
% 0.19/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.48          | (v3_pre_topc @ X20 @ X21)
% 0.19/0.48          | ((X20) != (X18))
% 0.19/0.48          | ~ (m1_pre_topc @ X21 @ X19)
% 0.19/0.48          | ~ (l1_pre_topc @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X19)
% 0.19/0.48          | ~ (m1_pre_topc @ X21 @ X19)
% 0.19/0.48          | (v3_pre_topc @ X18 @ X21)
% 0.19/0.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.48          | ~ (v3_pre_topc @ X18 @ X19)
% 0.19/0.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.19/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ X0)
% 0.19/0.48          | (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.19/0.48          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.19/0.48          | ~ (l1_pre_topc @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '28'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.19/0.48        | (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.19/0.48        | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['21', '29'])).
% 0.19/0.48  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.19/0.48         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t2_tsep_1, axiom,
% 0.19/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.19/0.48  thf(t65_pre_topc, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( l1_pre_topc @ B ) =>
% 0.19/0.48           ( ( m1_pre_topc @ A @ B ) <=>
% 0.19/0.48             ( m1_pre_topc @
% 0.19/0.48               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X13)
% 0.19/0.48          | ~ (m1_pre_topc @ X14 @ X13)
% 0.19/0.48          | (m1_pre_topc @ X14 @ 
% 0.19/0.48             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.19/0.48          | ~ (l1_pre_topc @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X0)
% 0.19/0.48          | ~ (l1_pre_topc @ X0)
% 0.19/0.48          | (m1_pre_topc @ X0 @ 
% 0.19/0.48             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.19/0.48          | ~ (l1_pre_topc @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_pre_topc @ X0 @ 
% 0.19/0.48           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.19/0.48          | ~ (l1_pre_topc @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (((m1_pre_topc @ sk_B @ 
% 0.19/0.48         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.19/0.48        | ~ (l1_pre_topc @ sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['32', '36'])).
% 0.19/0.48  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      ((m1_pre_topc @ sk_B @ 
% 0.19/0.48        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.48  thf(t59_pre_topc, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_pre_topc @
% 0.19/0.48             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.19/0.48           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (m1_pre_topc @ X11 @ 
% 0.19/0.48             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.19/0.48          | (m1_pre_topc @ X11 @ X12)
% 0.19/0.48          | ~ (l1_pre_topc @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.19/0.48  thf('41', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.48      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.48  thf('44', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.19/0.48      inference('clc', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X15 @ 
% 0.19/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.19/0.48          | ~ (v1_tops_2 @ X15 @ X16)
% 0.19/0.48          | ~ (r2_hidden @ X17 @ X15)
% 0.19/0.48          | (v3_pre_topc @ X17 @ X16)
% 0.19/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.48          | ~ (l1_pre_topc @ X16))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ sk_A)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.48          | (v3_pre_topc @ X0 @ sk_A)
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.19/0.48          | ~ (v1_tops_2 @ sk_C_1 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.48  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('49', plain, ((v1_tops_2 @ sk_C_1 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.48          | (v3_pre_topc @ X0 @ sk_A)
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_1) | (v3_pre_topc @ X0 @ sk_A))),
% 0.19/0.48      inference('clc', [status(thm)], ['50', '51'])).
% 0.19/0.48  thf('53', plain, ((v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)),
% 0.19/0.48      inference('sup-', [status(thm)], ['44', '52'])).
% 0.19/0.48  thf('54', plain, ((v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.19/0.48      inference('demod', [status(thm)], ['30', '31', '43', '53'])).
% 0.19/0.48  thf('55', plain, ($false), inference('demod', [status(thm)], ['10', '54'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
