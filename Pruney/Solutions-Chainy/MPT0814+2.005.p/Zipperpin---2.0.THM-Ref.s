%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dicIjDAsHo

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:38 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 125 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  556 (1179 expanded)
%              Number of equality atoms :   15 (  40 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_F_2_type,type,(
    sk_F_2: $i > $i > $i > $i )).

thf(t6_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
       => ~ ( ( r2_hidden @ A @ D )
            & ! [E: $i,F: $i] :
                ~ ( ( A
                    = ( k4_tarski @ E @ F ) )
                  & ( r2_hidden @ E @ B )
                  & ( r2_hidden @ F @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_relset_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ D @ C )
        & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ A )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ B )
               => ( D
                 != ( k4_tarski @ E @ F ) ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) )
      | ( X22
        = ( k4_tarski @ ( sk_E_2 @ X22 @ X21 @ X20 ) @ ( sk_F_2 @ X22 @ X21 @ X20 ) ) )
      | ~ ( r2_hidden @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( X0
        = ( k4_tarski @ ( sk_E_2 @ X0 @ sk_C @ sk_B_1 ) @ ( sk_F_2 @ X0 @ sk_C @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_2 @ sk_A @ sk_C @ sk_B_1 ) @ ( sk_F_2 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) )
      | ( m1_subset_1 @ ( sk_E_2 @ X22 @ X21 @ X20 ) @ X20 )
      | ~ ( r2_hidden @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_E_2 @ X0 @ sk_C @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( sk_E_2 @ sk_A @ sk_C @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_E_2 @ sk_A @ sk_C @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X15 @ X12 @ X13 ) @ ( sk_E_1 @ X15 @ X12 @ X13 ) @ X15 @ X12 @ X13 )
      | ( X14
       != ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X15 @ X12 @ X13 ) @ ( sk_E_1 @ X15 @ X12 @ X13 ) @ X15 @ X12 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X3 @ X7 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_E_2 @ sk_A @ sk_C @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B_1 )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ( sk_A
       != ( k4_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E_2 @ sk_A @ sk_C @ sk_B_1 ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F_2 @ sk_A @ sk_C @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) )
      | ( m1_subset_1 @ ( sk_F_2 @ X22 @ X21 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_F_2 @ X0 @ sk_C @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( sk_F_2 @ sk_A @ sk_C @ sk_B_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F_2 @ sk_A @ sk_C @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X6 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( sk_F_2 @ sk_A @ sk_C @ sk_B_1 ) @ sk_C ),
    inference(clc,[status(thm)],['40','47'])).

thf('49',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['33','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dicIjDAsHo
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.68  % Solved by: fo/fo7.sh
% 0.50/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.68  % done 179 iterations in 0.229s
% 0.50/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.68  % SZS output start Refutation
% 0.50/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.68  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.50/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.68  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.50/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.68  thf(sk_E_2_type, type, sk_E_2: $i > $i > $i > $i).
% 0.50/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.50/0.68  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.50/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.50/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.50/0.68  thf(sk_F_2_type, type, sk_F_2: $i > $i > $i > $i).
% 0.50/0.68  thf(t6_relset_1, conjecture,
% 0.50/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.50/0.68       ( ~( ( r2_hidden @ A @ D ) & 
% 0.50/0.68            ( ![E:$i,F:$i]:
% 0.50/0.68              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.50/0.68                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.68        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.50/0.68          ( ~( ( r2_hidden @ A @ D ) & 
% 0.50/0.68               ( ![E:$i,F:$i]:
% 0.50/0.68                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.50/0.68                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.50/0.68    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.50/0.68  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('1', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(t3_subset, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.68  thf('2', plain,
% 0.50/0.68      (![X27 : $i, X28 : $i]:
% 0.50/0.68         ((r1_tarski @ X27 @ X28) | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.68  thf('3', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.50/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.68  thf(t65_subset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.68     ( ~( ( r2_hidden @ D @ C ) & 
% 0.50/0.68          ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.50/0.68          ( ![E:$i]:
% 0.50/0.68            ( ( m1_subset_1 @ E @ A ) =>
% 0.50/0.68              ( ![F:$i]:
% 0.50/0.68                ( ( m1_subset_1 @ F @ B ) => ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ))).
% 0.50/0.68  thf('4', plain,
% 0.50/0.68      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.50/0.68         (~ (r1_tarski @ X19 @ (k2_zfmisc_1 @ X20 @ X21))
% 0.50/0.68          | ((X22)
% 0.50/0.68              = (k4_tarski @ (sk_E_2 @ X22 @ X21 @ X20) @ 
% 0.50/0.68                 (sk_F_2 @ X22 @ X21 @ X20)))
% 0.50/0.68          | ~ (r2_hidden @ X22 @ X19))),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_subset_1])).
% 0.50/0.68  thf('5', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X0 @ sk_D_1)
% 0.50/0.68          | ((X0)
% 0.50/0.68              = (k4_tarski @ (sk_E_2 @ X0 @ sk_C @ sk_B_1) @ 
% 0.50/0.68                 (sk_F_2 @ X0 @ sk_C @ sk_B_1))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.50/0.68  thf('6', plain,
% 0.50/0.68      (((sk_A)
% 0.50/0.68         = (k4_tarski @ (sk_E_2 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.50/0.68            (sk_F_2 @ sk_A @ sk_C @ sk_B_1)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['0', '5'])).
% 0.50/0.68  thf('7', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('8', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.50/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.68  thf('9', plain,
% 0.50/0.68      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.50/0.68         (~ (r1_tarski @ X19 @ (k2_zfmisc_1 @ X20 @ X21))
% 0.50/0.68          | (m1_subset_1 @ (sk_E_2 @ X22 @ X21 @ X20) @ X20)
% 0.50/0.68          | ~ (r2_hidden @ X22 @ X19))),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_subset_1])).
% 0.50/0.68  thf('10', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X0 @ sk_D_1)
% 0.50/0.68          | (m1_subset_1 @ (sk_E_2 @ X0 @ sk_C @ sk_B_1) @ sk_B_1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.68  thf('11', plain, ((m1_subset_1 @ (sk_E_2 @ sk_A @ sk_C @ sk_B_1) @ sk_B_1)),
% 0.50/0.68      inference('sup-', [status(thm)], ['7', '10'])).
% 0.50/0.68  thf(t2_subset, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ A @ B ) =>
% 0.50/0.68       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.50/0.68  thf('12', plain,
% 0.50/0.68      (![X25 : $i, X26 : $i]:
% 0.50/0.68         ((r2_hidden @ X25 @ X26)
% 0.50/0.68          | (v1_xboole_0 @ X26)
% 0.50/0.68          | ~ (m1_subset_1 @ X25 @ X26))),
% 0.50/0.68      inference('cnf', [status(esa)], [t2_subset])).
% 0.50/0.68  thf('13', plain,
% 0.50/0.68      (((v1_xboole_0 @ sk_B_1)
% 0.50/0.68        | (r2_hidden @ (sk_E_2 @ sk_A @ sk_C @ sk_B_1) @ sk_B_1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.68  thf(d1_xboole_0, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.68  thf('14', plain,
% 0.50/0.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.50/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.68  thf(d2_zfmisc_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.50/0.68       ( ![D:$i]:
% 0.50/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.68           ( ?[E:$i,F:$i]:
% 0.50/0.68             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.50/0.68               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.50/0.68  thf(zf_stmt_2, axiom,
% 0.50/0.68    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.50/0.68     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.50/0.68       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.50/0.68         ( r2_hidden @ E @ A ) ) ))).
% 0.50/0.68  thf(zf_stmt_3, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.50/0.68       ( ![D:$i]:
% 0.50/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.68           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.50/0.68  thf('15', plain,
% 0.50/0.68      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X15 @ X14)
% 0.50/0.68          | (zip_tseitin_0 @ (sk_F_1 @ X15 @ X12 @ X13) @ 
% 0.50/0.68             (sk_E_1 @ X15 @ X12 @ X13) @ X15 @ X12 @ X13)
% 0.50/0.68          | ((X14) != (k2_zfmisc_1 @ X13 @ X12)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.68  thf('16', plain,
% 0.50/0.68      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.50/0.68         ((zip_tseitin_0 @ (sk_F_1 @ X15 @ X12 @ X13) @ 
% 0.50/0.68           (sk_E_1 @ X15 @ X12 @ X13) @ X15 @ X12 @ X13)
% 0.50/0.68          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X13 @ X12)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['15'])).
% 0.50/0.68  thf('17', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.50/0.68          | (zip_tseitin_0 @ 
% 0.50/0.68             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.50/0.68             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.50/0.68             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['14', '16'])).
% 0.50/0.68  thf('18', plain,
% 0.50/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.68         ((r2_hidden @ X3 @ X7) | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.68  thf('19', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1))
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.68  thf('20', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.68  thf('21', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.50/0.68  thf('22', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(cc1_subset_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( v1_xboole_0 @ A ) =>
% 0.50/0.68       ( ![B:$i]:
% 0.50/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.50/0.68  thf('23', plain,
% 0.50/0.68      (![X23 : $i, X24 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.50/0.68          | (v1_xboole_0 @ X23)
% 0.50/0.68          | ~ (v1_xboole_0 @ X24))),
% 0.50/0.68      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.50/0.68  thf('24', plain,
% 0.50/0.68      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))
% 0.50/0.68        | (v1_xboole_0 @ sk_D_1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.50/0.68  thf('25', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('26', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.68  thf('27', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.50/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.68  thf('28', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.50/0.68      inference('clc', [status(thm)], ['24', '27'])).
% 0.50/0.68  thf('29', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.50/0.68      inference('sup-', [status(thm)], ['21', '28'])).
% 0.50/0.68  thf('30', plain, ((r2_hidden @ (sk_E_2 @ sk_A @ sk_C @ sk_B_1) @ sk_B_1)),
% 0.50/0.68      inference('clc', [status(thm)], ['13', '29'])).
% 0.50/0.68  thf('31', plain,
% 0.50/0.68      (![X30 : $i, X31 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X30 @ sk_B_1)
% 0.50/0.68          | ~ (r2_hidden @ X31 @ sk_C)
% 0.50/0.68          | ((sk_A) != (k4_tarski @ X30 @ X31)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('32', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((sk_A) != (k4_tarski @ (sk_E_2 @ sk_A @ sk_C @ sk_B_1) @ X0))
% 0.50/0.68          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.50/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.68  thf('33', plain,
% 0.50/0.68      ((((sk_A) != (sk_A))
% 0.50/0.68        | ~ (r2_hidden @ (sk_F_2 @ sk_A @ sk_C @ sk_B_1) @ sk_C))),
% 0.50/0.68      inference('sup-', [status(thm)], ['6', '32'])).
% 0.50/0.68  thf('34', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('35', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.50/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.68  thf('36', plain,
% 0.50/0.68      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.50/0.68         (~ (r1_tarski @ X19 @ (k2_zfmisc_1 @ X20 @ X21))
% 0.50/0.68          | (m1_subset_1 @ (sk_F_2 @ X22 @ X21 @ X20) @ X21)
% 0.50/0.68          | ~ (r2_hidden @ X22 @ X19))),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_subset_1])).
% 0.50/0.68  thf('37', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X0 @ sk_D_1)
% 0.50/0.68          | (m1_subset_1 @ (sk_F_2 @ X0 @ sk_C @ sk_B_1) @ sk_C))),
% 0.50/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.50/0.68  thf('38', plain, ((m1_subset_1 @ (sk_F_2 @ sk_A @ sk_C @ sk_B_1) @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['34', '37'])).
% 0.50/0.68  thf('39', plain,
% 0.50/0.68      (![X25 : $i, X26 : $i]:
% 0.50/0.68         ((r2_hidden @ X25 @ X26)
% 0.50/0.68          | (v1_xboole_0 @ X26)
% 0.50/0.68          | ~ (m1_subset_1 @ X25 @ X26))),
% 0.50/0.68      inference('cnf', [status(esa)], [t2_subset])).
% 0.50/0.68  thf('40', plain,
% 0.50/0.68      (((v1_xboole_0 @ sk_C)
% 0.50/0.68        | (r2_hidden @ (sk_F_2 @ sk_A @ sk_C @ sk_B_1) @ sk_C))),
% 0.50/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.50/0.68  thf('41', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.50/0.68          | (zip_tseitin_0 @ 
% 0.50/0.68             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.50/0.68             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.50/0.68             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['14', '16'])).
% 0.50/0.68  thf('42', plain,
% 0.50/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.68         ((r2_hidden @ X4 @ X6) | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.68  thf('43', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1))
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['41', '42'])).
% 0.50/0.68  thf('44', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.68  thf('45', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.50/0.68  thf('46', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.50/0.68      inference('clc', [status(thm)], ['24', '27'])).
% 0.50/0.68  thf('47', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.68  thf('48', plain, ((r2_hidden @ (sk_F_2 @ sk_A @ sk_C @ sk_B_1) @ sk_C)),
% 0.50/0.68      inference('clc', [status(thm)], ['40', '47'])).
% 0.50/0.68  thf('49', plain, (((sk_A) != (sk_A))),
% 0.50/0.68      inference('demod', [status(thm)], ['33', '48'])).
% 0.50/0.68  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 0.50/0.68  
% 0.50/0.68  % SZS output end Refutation
% 0.50/0.68  
% 0.50/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
