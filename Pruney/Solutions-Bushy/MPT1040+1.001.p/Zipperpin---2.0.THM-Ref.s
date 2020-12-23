%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1040+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3ZpaL8QvDz

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 605 expanded)
%              Number of leaves         :   24 ( 169 expanded)
%              Depth                    :   19
%              Number of atoms          :  745 (11340 expanded)
%              Number of equality atoms :   45 ( 582 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t155_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t155_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( v1_partfun1 @ X3 @ X4 )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X6 @ X9 @ X11 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ( X7 != X8 )
      | ~ ( v1_partfun1 @ X7 @ X11 )
      | ~ ( r1_partfun1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X6: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( r1_partfun1 @ X6 @ X8 )
      | ~ ( v1_partfun1 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( zip_tseitin_0 @ X8 @ X8 @ X6 @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X17
       != ( k5_partfun1 @ X15 @ X14 @ X13 ) )
      | ( r2_hidden @ X19 @ X17 )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X19 @ ( k5_partfun1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['22','23'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('26',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','26'])).

thf('28',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('31',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('38',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','35'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X6: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( r1_partfun1 @ X6 @ X8 )
      | ~ ( v1_partfun1 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( zip_tseitin_0 @ X8 @ X8 @ X6 @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( v1_partfun1 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('51',plain,
    ( ( ( v1_partfun1 @ sk_D @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['22','23'])).

thf('53',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_partfun1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('57',plain,(
    v1_partfun1 @ sk_D @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','46','57'])).

thf('59',plain,(
    zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X13: $i,X14: $i,X15: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X19 @ ( k5_partfun1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ k1_xboole_0 )
        | ~ ( v1_funct_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('68',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('69',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['37','72'])).


%------------------------------------------------------------------------------
