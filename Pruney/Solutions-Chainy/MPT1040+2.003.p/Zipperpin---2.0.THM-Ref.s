%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hc68tLF0Ru

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 657 expanded)
%              Number of leaves         :   26 ( 187 expanded)
%              Depth                    :   20
%              Number of atoms          :  798 (11541 expanded)
%              Number of equality atoms :   58 ( 639 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( v1_partfun1 @ X4 @ X5 )
      | ~ ( v1_funct_2 @ X4 @ X5 @ X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ( v1_xboole_0 @ X6 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X12 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( X8 != X9 )
      | ~ ( v1_partfun1 @ X8 @ X12 )
      | ~ ( r1_partfun1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X7: $i,X9: $i,X10: $i,X12: $i] :
      ( ~ ( r1_partfun1 @ X7 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X12 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ( zip_tseitin_0 @ X9 @ X9 @ X7 @ X10 @ X12 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k5_partfun1 @ X16 @ X15 @ X14 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X20 @ ( k5_partfun1 @ X16 @ X15 @ X14 ) ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ o_0_0_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('35',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('36',plain,
    ( ( o_0_0_xboole_0 != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('38',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','41'])).

thf('43',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','42'])).

thf('44',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','41'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X7: $i,X9: $i,X10: $i,X12: $i] :
      ( ~ ( r1_partfun1 @ X7 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X12 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ( zip_tseitin_0 @ X9 @ X9 @ X7 @ X10 @ X12 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ o_0_0_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('58',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X3 ) ) )
      | ( v1_partfun1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('59',plain,
    ( ( ( v1_partfun1 @ sk_D @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['22','23'])).

thf('61',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('62',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_partfun1 @ sk_D @ o_0_0_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('65',plain,(
    v1_partfun1 @ sk_D @ o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['51','52','65'])).

thf('67',plain,(
    zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['44','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X14: $i,X15: $i,X16: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X20 @ ( k5_partfun1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('74',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ ( k5_partfun1 @ o_0_0_xboole_0 @ sk_B @ sk_C ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ o_0_0_xboole_0 )
        | ~ ( v1_funct_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ ( k5_partfun1 @ o_0_0_xboole_0 @ sk_B @ sk_C ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('78',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('79',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ ( k5_partfun1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['43','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hc68tLF0Ru
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 85 iterations in 0.028s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.19/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(t155_funct_2, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ![D:$i]:
% 0.19/0.48         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48           ( ( r1_partfun1 @ C @ D ) =>
% 0.19/0.48             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.19/0.48               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48          ( ![D:$i]:
% 0.19/0.48            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.48                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48              ( ( r1_partfun1 @ C @ D ) =>
% 0.19/0.48                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.19/0.48                  ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t155_funct_2])).
% 0.19/0.48  thf('0', plain, (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc5_funct_2, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.48       ( ![C:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.19/0.48             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.19/0.48          | (v1_partfun1 @ X4 @ X5)
% 0.19/0.48          | ~ (v1_funct_2 @ X4 @ X5 @ X6)
% 0.19/0.48          | ~ (v1_funct_1 @ X4)
% 0.19/0.48          | (v1_xboole_0 @ X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B)
% 0.19/0.48        | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.19/0.48        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d7_partfun1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.48         ( v1_funct_1 @ C ) ) =>
% 0.19/0.48       ( ![D:$i]:
% 0.19/0.48         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.19/0.48           ( ![E:$i]:
% 0.19/0.48             ( ( r2_hidden @ E @ D ) <=>
% 0.19/0.48               ( ?[F:$i]:
% 0.19/0.48                 ( ( v1_funct_1 @ F ) & 
% 0.19/0.48                   ( m1_subset_1 @
% 0.19/0.48                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.48                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.19/0.48                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_1, axiom,
% 0.19/0.48    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.19/0.48     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.19/0.48       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.19/0.48         ( ( F ) = ( E ) ) & 
% 0.19/0.48         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.48         ( v1_funct_1 @ F ) ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.19/0.48         ((zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X12)
% 0.19/0.48          | ~ (v1_funct_1 @ X8)
% 0.19/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.19/0.48          | ((X8) != (X9))
% 0.19/0.48          | ~ (v1_partfun1 @ X8 @ X12)
% 0.19/0.48          | ~ (r1_partfun1 @ X7 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X7 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.19/0.48         (~ (r1_partfun1 @ X7 @ X9)
% 0.19/0.48          | ~ (v1_partfun1 @ X9 @ X12)
% 0.19/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.19/0.48          | ~ (v1_funct_1 @ X9)
% 0.19/0.48          | (zip_tseitin_0 @ X9 @ X9 @ X7 @ X10 @ X12))),
% 0.19/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '10'])).
% 0.19/0.48  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A)
% 0.19/0.48          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.19/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ sk_B)
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.19/0.48          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.19/0.48  thf(zf_stmt_3, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ![D:$i]:
% 0.19/0.48         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.19/0.48           ( ![E:$i]:
% 0.19/0.48             ( ( r2_hidden @ E @ D ) <=>
% 0.19/0.48               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.19/0.48         (((X18) != (k5_partfun1 @ X16 @ X15 @ X14))
% 0.19/0.48          | (r2_hidden @ X20 @ X18)
% 0.19/0.48          | ~ (zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16)
% 0.19/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.19/0.48          | ~ (v1_funct_1 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i, X16 : $i, X20 : $i, X21 : $i]:
% 0.19/0.48         (~ (v1_funct_1 @ X14)
% 0.19/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16)
% 0.19/0.48          | (r2_hidden @ X20 @ (k5_partfun1 @ X16 @ X15 @ X14)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '18'])).
% 0.19/0.48  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B)
% 0.19/0.48        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '21'])).
% 0.19/0.48  thf('23', plain, (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('24', plain, ((v1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf(t6_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t6_boole])).
% 0.19/0.48  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.19/0.48  thf('26', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ o_0_0_xboole_0 @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '28'])).
% 0.19/0.48  thf('30', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['30'])).
% 0.19/0.48  thf('32', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((((sk_A) = (o_0_0_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('34', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['30'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      ((((o_0_0_xboole_0) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.48  thf('37', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.19/0.48         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.48  thf('39', plain, ((((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.48  thf('40', plain, ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['30'])).
% 0.19/0.48  thf('41', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain, (((sk_A) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['33', '41'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      (~ (r2_hidden @ sk_D @ 
% 0.19/0.48          (k5_partfun1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['29', '42'])).
% 0.19/0.48  thf('44', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('46', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ o_0_0_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.48  thf('48', plain, (((sk_A) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['33', '41'])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      (![X7 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.19/0.48         (~ (r1_partfun1 @ X7 @ X9)
% 0.19/0.48          | ~ (v1_partfun1 @ X9 @ X12)
% 0.19/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.19/0.48          | ~ (v1_funct_1 @ X9)
% 0.19/0.48          | (zip_tseitin_0 @ X9 @ X9 @ X7 @ X10 @ X12))),
% 0.19/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ o_0_0_xboole_0 @ o_0_0_xboole_0)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48          | ~ (v1_partfun1 @ sk_D @ o_0_0_xboole_0)
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.48  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['30'])).
% 0.19/0.48  thf('54', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('55', plain,
% 0.19/0.48      (((m1_subset_1 @ sk_D @ 
% 0.19/0.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['53', '54'])).
% 0.19/0.48  thf('56', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.48  thf('57', plain,
% 0.19/0.48      (((m1_subset_1 @ sk_D @ 
% 0.19/0.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B))))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['55', '56'])).
% 0.19/0.48  thf(cc1_partfun1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.48       ( ![C:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.19/0.48  thf('58', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X3)))
% 0.19/0.48          | (v1_partfun1 @ X2 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.19/0.48  thf('59', plain,
% 0.19/0.48      ((((v1_partfun1 @ sk_D @ o_0_0_xboole_0)
% 0.19/0.48         | ~ (v1_xboole_0 @ o_0_0_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.48  thf('60', plain, ((v1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('61', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.48  thf('62', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.19/0.48      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.48  thf('63', plain,
% 0.19/0.48      (((v1_partfun1 @ sk_D @ o_0_0_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['59', '62'])).
% 0.19/0.48  thf('64', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('65', plain, ((v1_partfun1 @ sk_D @ o_0_0_xboole_0)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['63', '64'])).
% 0.19/0.48  thf('66', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ o_0_0_xboole_0 @ o_0_0_xboole_0)
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.19/0.48      inference('demod', [status(thm)], ['51', '52', '65'])).
% 0.19/0.48  thf('67', plain,
% 0.19/0.48      ((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0)),
% 0.19/0.48      inference('sup-', [status(thm)], ['44', '66'])).
% 0.19/0.48  thf('68', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['30'])).
% 0.19/0.48  thf('69', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('70', plain,
% 0.19/0.48      (((m1_subset_1 @ sk_C @ 
% 0.19/0.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['68', '69'])).
% 0.19/0.48  thf('71', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.48  thf('72', plain,
% 0.19/0.48      (((m1_subset_1 @ sk_C @ 
% 0.19/0.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B))))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['70', '71'])).
% 0.19/0.48  thf('73', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i, X16 : $i, X20 : $i, X21 : $i]:
% 0.19/0.48         (~ (v1_funct_1 @ X14)
% 0.19/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16)
% 0.19/0.48          | (r2_hidden @ X20 @ (k5_partfun1 @ X16 @ X15 @ X14)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.48  thf('74', plain,
% 0.19/0.48      ((![X0 : $i, X1 : $i]:
% 0.19/0.48          ((r2_hidden @ X0 @ (k5_partfun1 @ o_0_0_xboole_0 @ sk_B @ sk_C))
% 0.19/0.48           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ o_0_0_xboole_0)
% 0.19/0.48           | ~ (v1_funct_1 @ sk_C)))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['72', '73'])).
% 0.19/0.48  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('76', plain,
% 0.19/0.48      ((![X0 : $i, X1 : $i]:
% 0.19/0.48          ((r2_hidden @ X0 @ (k5_partfun1 @ o_0_0_xboole_0 @ sk_B @ sk_C))
% 0.19/0.48           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ o_0_0_xboole_0)))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['74', '75'])).
% 0.19/0.48  thf('77', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.48  thf('78', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.48  thf('79', plain,
% 0.19/0.48      ((![X0 : $i, X1 : $i]:
% 0.19/0.48          ((r2_hidden @ X0 @ 
% 0.19/0.48            (k5_partfun1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C))
% 0.19/0.48           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ o_0_0_xboole_0 @ 
% 0.19/0.48                o_0_0_xboole_0)))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.19/0.48  thf('80', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('81', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ X0 @ 
% 0.19/0.48           (k5_partfun1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 0.19/0.48  thf('82', plain,
% 0.19/0.48      ((r2_hidden @ sk_D @ 
% 0.19/0.48        (k5_partfun1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['67', '81'])).
% 0.19/0.48  thf('83', plain, ($false), inference('demod', [status(thm)], ['43', '82'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
