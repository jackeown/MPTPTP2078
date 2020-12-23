%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oJ2nhtWT0g

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:37 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 101 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  615 (1230 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(t63_setfam_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v3_setfam_1 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v3_setfam_1 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
             => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v3_setfam_1 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
           => ! [C: $i] :
                ( ( ( v3_setfam_1 @ C @ A )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
               => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v3_setfam_1 @ B @ A )
      <=> ~ ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_setfam_1 @ X20 @ X19 )
      | ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v3_setfam_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('11',plain,
    ( ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ X1 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ X1 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ X1 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_setfam_1 @ X20 @ X19 )
      | ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( v3_setfam_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_setfam_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['43','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['4','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oJ2nhtWT0g
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 183 iterations in 0.140s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 0.36/0.58  thf(t63_setfam_1, conjecture,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.36/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.36/0.58           ( ![C:$i]:
% 0.36/0.58             ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.36/0.58                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.36/0.58               ( v3_setfam_1 @
% 0.36/0.58                 ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i]:
% 0.36/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.58          ( ![B:$i]:
% 0.36/0.58            ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.36/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.36/0.58              ( ![C:$i]:
% 0.36/0.58                ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.36/0.58                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.36/0.58                  ( v3_setfam_1 @
% 0.36/0.58                    ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t63_setfam_1])).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(d13_setfam_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.58       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X19 : $i, X20 : $i]:
% 0.36/0.58         (~ (v3_setfam_1 @ X20 @ X19)
% 0.36/0.58          | ~ (r2_hidden @ X19 @ X20)
% 0.36/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.36/0.58      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (v3_setfam_1 @ sk_B @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf('3', plain, ((v3_setfam_1 @ sk_B @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('4', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.36/0.58      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(dt_k4_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.58       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.36/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.36/0.58          | (m1_subset_1 @ (k4_subset_1 @ X14 @ X13 @ X15) @ 
% 0.36/0.58             (k1_zfmisc_1 @ X14)))),
% 0.36/0.58      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0) @ 
% 0.36/0.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.36/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.36/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X19 : $i, X20 : $i]:
% 0.36/0.58         ((r2_hidden @ X19 @ X20)
% 0.36/0.58          | (v3_setfam_1 @ X20 @ X19)
% 0.36/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.36/0.58      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (((v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.36/0.58         sk_A)
% 0.36/0.58        | (r2_hidden @ sk_A @ 
% 0.36/0.58           (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (~ (v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.36/0.58          sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      ((r2_hidden @ sk_A @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C))),
% 0.36/0.58      inference('clc', [status(thm)], ['11', '12'])).
% 0.36/0.58  thf(d5_xboole_0, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.58       ( ![D:$i]:
% 0.36/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.58          | (r2_hidden @ X0 @ X2)
% 0.36/0.58          | (r2_hidden @ X0 @ X3)
% 0.36/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.36/0.58          | (r2_hidden @ X0 @ X2)
% 0.36/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.36/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ sk_A @ X0)
% 0.36/0.58          | (r2_hidden @ sk_A @ 
% 0.36/0.58             (k4_xboole_0 @ 
% 0.36/0.58              (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['13', '15'])).
% 0.36/0.58  thf('17', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.36/0.58          | (r2_hidden @ X0 @ X2)
% 0.36/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.36/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ sk_A @ X0)
% 0.36/0.58          | (r2_hidden @ sk_A @ X1)
% 0.36/0.58          | (r2_hidden @ sk_A @ 
% 0.36/0.58             (k4_xboole_0 @ 
% 0.36/0.58              (k4_xboole_0 @ 
% 0.36/0.58               (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ X0) @ 
% 0.36/0.58              X1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.58  thf(t41_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.58       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.58  thf('19', plain,
% 0.36/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.36/0.58           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ sk_A @ X0)
% 0.36/0.58          | (r2_hidden @ sk_A @ X1)
% 0.36/0.58          | (r2_hidden @ sk_A @ 
% 0.36/0.58             (k4_xboole_0 @ 
% 0.36/0.58              (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.36/0.58              (k2_xboole_0 @ X0 @ X1))))),
% 0.36/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.36/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 0.36/0.58          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0)
% 0.36/0.58            = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C)
% 0.36/0.58         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.58      inference('sup-', [status(thm)], ['21', '24'])).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ sk_A @ X0)
% 0.36/0.58          | (r2_hidden @ sk_A @ X1)
% 0.36/0.58          | (r2_hidden @ sk_A @ 
% 0.36/0.58             (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.36/0.58              (k2_xboole_0 @ X0 @ X1))))),
% 0.36/0.58      inference('demod', [status(thm)], ['20', '25'])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.36/0.58         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.36/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.36/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.36/0.58         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.36/0.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.36/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.36/0.58          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.36/0.58          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.36/0.58          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.36/0.58          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.36/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.36/0.58          | (r2_hidden @ X4 @ X1)
% 0.36/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.36/0.58          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['30', '32'])).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.36/0.58          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.36/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.36/0.58          | ~ (r2_hidden @ X4 @ X2)
% 0.36/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X4 @ X2)
% 0.36/0.58          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['35'])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.36/0.58          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['34', '36'])).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.36/0.58          | ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['33', '37'])).
% 0.36/0.58  thf('39', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 0.36/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.58  thf('40', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X4 @ X2)
% 0.36/0.58          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['35'])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 0.36/0.58          | ~ (r2_hidden @ X2 @ X1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.58      inference('condensation', [status(thm)], ['41'])).
% 0.36/0.58  thf('43', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_A @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['26', '42'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      (![X19 : $i, X20 : $i]:
% 0.36/0.58         (~ (v3_setfam_1 @ X20 @ X19)
% 0.36/0.58          | ~ (r2_hidden @ X19 @ X20)
% 0.36/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.36/0.58      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.36/0.58  thf('46', plain,
% 0.36/0.58      ((~ (r2_hidden @ sk_A @ sk_C) | ~ (v3_setfam_1 @ sk_C @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.58  thf('47', plain, ((v3_setfam_1 @ sk_C @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('48', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.36/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.58  thf('49', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.36/0.58      inference('clc', [status(thm)], ['43', '48'])).
% 0.36/0.58  thf('50', plain, ($false), inference('demod', [status(thm)], ['4', '49'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
