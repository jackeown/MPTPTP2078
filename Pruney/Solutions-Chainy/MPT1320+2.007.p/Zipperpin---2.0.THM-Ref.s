%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TNH7PEaTzs

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:39 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  648 (1330 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t41_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                 => ( ( r2_hidden @ B @ D )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                   => ( ( r2_hidden @ B @ D )
                     => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_tops_2])).

thf('0',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) )
                 => ( ( D
                      = ( k1_tops_2 @ A @ B @ C ) )
                  <=> ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) )
                       => ( ( r2_hidden @ E @ D )
                        <=> ? [F: $i] :
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                              & ( r2_hidden @ F @ C )
                              & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B )
                                = E ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B )
          = E )
        & ( r2_hidden @ F @ C )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X5 ) @ X2 @ X3 )
       != X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( zip_tseitin_0 @ X2 @ ( k9_subset_1 @ ( u1_struct_0 @ X5 ) @ X2 @ X3 ) @ X4 @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ X1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_D @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X17 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_tops_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ( m1_subset_1 @ ( k1_tops_2 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) )
                 => ( ( D
                      = ( k1_tops_2 @ A @ B @ C ) )
                  <=> ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) )
                       => ( ( r2_hidden @ E @ D )
                        <=> ? [F: $i] :
                              ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) ) ) ) )
      | ( X8
       != ( k1_tops_2 @ X7 @ X6 @ X9 ) )
      | ( r2_hidden @ X11 @ X8 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X9 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) ) ) )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X9 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k1_tops_2 @ X7 @ X6 @ X9 ) )
      | ~ ( m1_subset_1 @ ( k1_tops_2 @ X7 @ X6 @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) ) ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_D @ sk_C @ sk_A )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ X0 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference('sup-',[status(thm)],['5','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TNH7PEaTzs
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 48 iterations in 0.039s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.54  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.35/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 0.35/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.54  thf(t41_tops_2, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54               ( ![D:$i]:
% 0.35/0.54                 ( ( m1_subset_1 @
% 0.35/0.54                     D @ 
% 0.35/0.54                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54                   ( ( r2_hidden @ B @ D ) =>
% 0.35/0.54                     ( r2_hidden @
% 0.35/0.54                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.35/0.54                       ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( l1_pre_topc @ A ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54              ( ![C:$i]:
% 0.35/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54                  ( ![D:$i]:
% 0.35/0.54                    ( ( m1_subset_1 @
% 0.35/0.54                        D @ 
% 0.35/0.54                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54                      ( ( r2_hidden @ B @ D ) =>
% 0.35/0.54                        ( r2_hidden @
% 0.35/0.54                          ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.35/0.54                          ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t41_tops_2])).
% 0.35/0.54  thf('0', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(d3_tops_2, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m1_subset_1 @
% 0.35/0.54                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54               ( ![D:$i]:
% 0.35/0.54                 ( ( m1_subset_1 @
% 0.35/0.54                     D @ 
% 0.35/0.54                     ( k1_zfmisc_1 @
% 0.35/0.54                       ( k1_zfmisc_1 @
% 0.35/0.54                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 0.35/0.54                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 0.35/0.54                     ( ![E:$i]:
% 0.35/0.54                       ( ( m1_subset_1 @
% 0.35/0.54                           E @ 
% 0.35/0.54                           ( k1_zfmisc_1 @
% 0.35/0.54                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 0.35/0.54                         ( ( r2_hidden @ E @ D ) <=>
% 0.35/0.54                           ( ?[F:$i]:
% 0.35/0.54                             ( ( m1_subset_1 @
% 0.35/0.54                                 F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.35/0.54                               ( r2_hidden @ F @ C ) & 
% 0.35/0.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) =
% 0.35/0.54                                 ( E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_1, axiom,
% 0.35/0.54    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.35/0.54       ( ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) = ( E ) ) & 
% 0.35/0.54         ( r2_hidden @ F @ C ) & 
% 0.35/0.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X2 @ X0 @ X4 @ X3 @ X5)
% 0.35/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.35/0.54          | ~ (r2_hidden @ X2 @ X4)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X5) @ X2 @ X3) != (X0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X2 @ X4)
% 0.35/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.35/0.54          | (zip_tseitin_0 @ X2 @ 
% 0.35/0.54             (k9_subset_1 @ (u1_struct_0 @ X5) @ X2 @ X3) @ X4 @ X3 @ X5))),
% 0.35/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ sk_B @ 
% 0.35/0.54           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ X1 @ X0 @ sk_A)
% 0.35/0.54          | ~ (r2_hidden @ sk_B @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (zip_tseitin_0 @ sk_B @ 
% 0.35/0.54          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ sk_D @ X0 @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['0', '4'])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t38_tops_2, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54               ( m1_subset_1 @
% 0.35/0.54                 ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.35/0.54                 ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X18) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X17 @ X18))))
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (l1_pre_topc @ X17))),
% 0.35/0.54      inference('cnf', [status(esa)], [t38_tops_2])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ sk_A)
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.54  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      ((m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '11'])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(dt_k1_tops_2, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.35/0.54         ( m1_subset_1 @
% 0.35/0.54           C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.35/0.54       ( m1_subset_1 @
% 0.35/0.54         ( k1_tops_2 @ A @ B @ C ) @ 
% 0.35/0.54         ( k1_zfmisc_1 @
% 0.35/0.54           ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ))).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.35/0.54          | ~ (l1_pre_topc @ X14)
% 0.35/0.54          | ~ (m1_subset_1 @ X15 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.35/0.54          | (m1_subset_1 @ (k1_tops_2 @ X14 @ X13 @ X15) @ 
% 0.35/0.54             (k1_zfmisc_1 @ 
% 0.35/0.54              (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X14 @ X13))))))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k1_tops_2])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D) @ 
% 0.35/0.54           (k1_zfmisc_1 @ 
% 0.35/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 0.35/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.54  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D) @ 
% 0.35/0.54           (k1_zfmisc_1 @ 
% 0.35/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['13', '18'])).
% 0.35/0.54  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_3, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m1_subset_1 @
% 0.35/0.54                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54               ( ![D:$i]:
% 0.35/0.54                 ( ( m1_subset_1 @
% 0.35/0.54                     D @ 
% 0.35/0.54                     ( k1_zfmisc_1 @
% 0.35/0.54                       ( k1_zfmisc_1 @
% 0.35/0.54                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 0.35/0.54                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 0.35/0.54                     ( ![E:$i]:
% 0.35/0.54                       ( ( m1_subset_1 @
% 0.35/0.54                           E @ 
% 0.35/0.54                           ( k1_zfmisc_1 @
% 0.35/0.54                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 0.35/0.54                         ( ( r2_hidden @ E @ D ) <=>
% 0.35/0.54                           ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.35/0.54          | ~ (m1_subset_1 @ X8 @ 
% 0.35/0.54               (k1_zfmisc_1 @ 
% 0.35/0.54                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X7 @ X6)))))
% 0.35/0.54          | ((X8) != (k1_tops_2 @ X7 @ X6 @ X9))
% 0.35/0.54          | (r2_hidden @ X11 @ X8)
% 0.35/0.54          | ~ (zip_tseitin_0 @ X12 @ X11 @ X9 @ X6 @ X7)
% 0.35/0.54          | ~ (m1_subset_1 @ X11 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X7 @ X6))))
% 0.35/0.54          | ~ (m1_subset_1 @ X9 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.35/0.54          | ~ (l1_pre_topc @ X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X7)
% 0.35/0.54          | ~ (m1_subset_1 @ X9 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.35/0.54          | ~ (m1_subset_1 @ X11 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X7 @ X6))))
% 0.35/0.54          | ~ (zip_tseitin_0 @ X12 @ X11 @ X9 @ X6 @ X7)
% 0.35/0.54          | (r2_hidden @ X11 @ (k1_tops_2 @ X7 @ X6 @ X9))
% 0.35/0.54          | ~ (m1_subset_1 @ (k1_tops_2 @ X7 @ X6 @ X9) @ 
% 0.35/0.54               (k1_zfmisc_1 @ 
% 0.35/0.54                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X7 @ X6)))))
% 0.35/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | (r2_hidden @ X0 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D))
% 0.35/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A)
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C))))
% 0.35/0.54          | ~ (m1_subset_1 @ sk_D @ 
% 0.35/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54          | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['19', '21'])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r2_hidden @ X0 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D))
% 0.35/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A)
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (zip_tseitin_0 @ X0 @ 
% 0.35/0.54             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_D @ 
% 0.35/0.54             sk_C @ sk_A)
% 0.35/0.54          | (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.35/0.54             (k1_tops_2 @ sk_A @ sk_C @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '26'])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (~ (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.35/0.54          (k1_tops_2 @ sk_A @ sk_C @ sk_D))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ~ (zip_tseitin_0 @ X0 @ 
% 0.35/0.54            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_D @ sk_C @ 
% 0.35/0.54            sk_A)),
% 0.35/0.54      inference('clc', [status(thm)], ['27', '28'])).
% 0.35/0.54  thf('30', plain, ($false), inference('sup-', [status(thm)], ['5', '29'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
