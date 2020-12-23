%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hwrj60yBaI

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 391 expanded)
%              Number of leaves         :   16 ( 113 expanded)
%              Depth                    :   21
%              Number of atoms          :  785 (7832 expanded)
%              Number of equality atoms :   59 ( 180 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t143_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
             => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ( v1_partfun1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_2 @ X5 @ X6 @ X4 )
      | ( v1_partfun1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( X10 = X7 )
      | ~ ( r1_partfun1 @ X10 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ~ ( v1_partfun1 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( X0 = sk_C ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( X0 = sk_C )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( r1_partfun1 @ sk_B @ sk_C )
    | ( sk_B = sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_partfun1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( sk_B = sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_2 @ X5 @ X6 @ X4 )
      | ( v1_partfun1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['18','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['18','24'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
    | ( sk_B = sk_C ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X6 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ( v1_partfun1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_2 @ X5 @ k1_xboole_0 @ X4 )
      | ( v1_partfun1 @ X5 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_B = sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B = sk_C )
    | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['18','24'])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_A )
    | ( sk_B = sk_C ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['18','24'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( X0 = sk_C ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( sk_B = sk_C )
      | ( X0 = sk_C )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( X0 = sk_C )
      | ( sk_B = sk_C ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B = sk_C ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_B = sk_C )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( r1_partfun1 @ sk_B @ sk_C )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['26','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_partfun1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_B = sk_C )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( v1_partfun1 @ sk_B @ k1_xboole_0 )
    | ( sk_B = sk_C )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['25','48'])).

thf('50',plain,
    ( ( sk_B = sk_C )
    | ~ ( v1_partfun1 @ sk_B @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['18','24'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
    | ( sk_B = sk_C ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_2 @ X5 @ k1_xboole_0 @ X4 )
      | ( v1_partfun1 @ X5 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('55',plain,
    ( ( sk_B = sk_C )
    | ~ ( v1_funct_1 @ sk_B )
    | ( v1_partfun1 @ sk_B @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_B @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( sk_B = sk_C )
    | ( v1_partfun1 @ sk_B @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_B @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['18','24'])).

thf('59',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_funct_2 @ sk_B @ k1_xboole_0 @ sk_A )
    | ( sk_B = sk_C ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_partfun1 @ sk_B @ k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['57','60'])).

thf('62',plain,(
    sk_B = sk_C ),
    inference(clc,[status(thm)],['50','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X0 @ X1 @ X2 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['64'])).

thf('66',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hwrj60yBaI
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 82 iterations in 0.041s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(t143_funct_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.50             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.50           ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.50          ( ![C:$i]:
% 0.20/0.50            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.50                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.50              ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t143_funct_2])).
% 0.20/0.50  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t132_funct_2, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.50           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.50           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (((X4) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_funct_1 @ X5)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.20/0.50          | (v1_partfun1 @ X5 @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.20/0.50          | ~ (v1_funct_2 @ X5 @ X6 @ X4)
% 0.20/0.50          | ~ (v1_funct_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (v1_funct_2 @ X5 @ X6 @ X4)
% 0.20/0.50          | (v1_partfun1 @ X5 @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.20/0.50          | ~ (v1_funct_1 @ X5)
% 0.20/0.50          | ((X4) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.50        | (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.50        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.50  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain, ((((sk_A) = (k1_xboole_0)) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t148_partfun1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.50             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.20/0.50               ( r1_partfun1 @ C @ D ) ) =>
% 0.20/0.50             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (v1_funct_1 @ X7)
% 0.20/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.20/0.50          | ((X10) = (X7))
% 0.20/0.50          | ~ (r1_partfun1 @ X10 @ X7)
% 0.20/0.50          | ~ (v1_partfun1 @ X7 @ X8)
% 0.20/0.50          | ~ (v1_partfun1 @ X10 @ X8)
% 0.20/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.20/0.50          | ~ (v1_funct_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.50          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.50          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.50          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.50          | ((X0) = (sk_C))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.50          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.50          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.50          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.50          | ((X0) = (sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_A) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (sk_C))
% 0.20/0.50          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.50          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.50          | ~ (v1_funct_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((~ (v1_funct_1 @ sk_B)
% 0.20/0.50        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.50        | ~ (r1_partfun1 @ sk_B @ sk_C)
% 0.20/0.50        | ((sk_B) = (sk_C))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '14'])).
% 0.20/0.50  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain, ((r1_partfun1 @ sk_B @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.50        | ((sk_B) = (sk_C))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (v1_funct_2 @ X5 @ X6 @ X4)
% 0.20/0.50          | (v1_partfun1 @ X5 @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.20/0.50          | ~ (v1_funct_1 @ X5)
% 0.20/0.50          | ((X4) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.50        | (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.50        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain, ((((sk_A) = (k1_xboole_0)) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.50  thf('25', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['18', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['18', '24'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ 
% 0.20/0.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))
% 0.20/0.50        | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (((X6) != (k1_xboole_0))
% 0.20/0.50          | ~ (v1_funct_1 @ X5)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.20/0.50          | (v1_partfun1 @ X5 @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.20/0.50          | ~ (v1_funct_2 @ X5 @ X6 @ X4)
% 0.20/0.50          | ~ (v1_funct_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (v1_funct_2 @ X5 @ k1_xboole_0 @ X4)
% 0.20/0.50          | (v1_partfun1 @ X5 @ k1_xboole_0)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X4)))
% 0.20/0.50          | ~ (v1_funct_1 @ X5))),
% 0.20/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((((sk_B) = (sk_C))
% 0.20/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.50        | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.20/0.50        | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '31'])).
% 0.20/0.50  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((((sk_B) = (sk_C))
% 0.20/0.50        | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.20/0.50        | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['18', '24'])).
% 0.20/0.50  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_A) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (((v1_partfun1 @ sk_C @ k1_xboole_0) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['34', '37'])).
% 0.20/0.50  thf('39', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['18', '24'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.50          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.50          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.50          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.50          | ((X0) = (sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.20/0.50          | ((sk_B) = (sk_C))
% 0.20/0.50          | ((X0) = (sk_C))
% 0.20/0.50          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.50          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.50          | ~ (v1_funct_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_B) = (sk_C))
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.50          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.50          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.50          | ((X0) = (sk_C))
% 0.20/0.50          | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['38', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((X0) = (sk_C))
% 0.20/0.50          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.50          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((((sk_B) = (sk_C))
% 0.20/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.50        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.50        | ~ (r1_partfun1 @ sk_B @ sk_C)
% 0.20/0.50        | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '43'])).
% 0.20/0.50  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain, ((r1_partfun1 @ sk_B @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((((sk_B) = (sk_C)) | ~ (v1_partfun1 @ sk_B @ sk_A) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.50  thf('48', plain, ((~ (v1_partfun1 @ sk_B @ sk_A) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      ((~ (v1_partfun1 @ sk_B @ k1_xboole_0)
% 0.20/0.50        | ((sk_B) = (sk_C))
% 0.20/0.50        | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((((sk_B) = (sk_C)) | ~ (v1_partfun1 @ sk_B @ k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.50  thf('51', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['18', '24'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_B @ 
% 0.20/0.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))
% 0.20/0.50        | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (v1_funct_2 @ X5 @ k1_xboole_0 @ X4)
% 0.20/0.50          | (v1_partfun1 @ X5 @ k1_xboole_0)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X4)))
% 0.20/0.50          | ~ (v1_funct_1 @ X5))),
% 0.20/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((((sk_B) = (sk_C))
% 0.20/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.50        | (v1_partfun1 @ sk_B @ k1_xboole_0)
% 0.20/0.50        | ~ (v1_funct_2 @ sk_B @ k1_xboole_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((((sk_B) = (sk_C))
% 0.20/0.50        | (v1_partfun1 @ sk_B @ k1_xboole_0)
% 0.20/0.50        | ~ (v1_funct_2 @ sk_B @ k1_xboole_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['18', '24'])).
% 0.20/0.50  thf('59', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (((v1_funct_2 @ sk_B @ k1_xboole_0 @ sk_A) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain, (((v1_partfun1 @ sk_B @ k1_xboole_0) | ((sk_B) = (sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['57', '60'])).
% 0.20/0.50  thf('62', plain, (((sk_B) = (sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['50', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(reflexivity_r2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r2_relset_1 @ X0 @ X1 @ X2 @ X2)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.20/0.50      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.50      inference('condensation', [status(thm)], ['64'])).
% 0.20/0.50  thf('66', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '65'])).
% 0.20/0.50  thf('67', plain, ($false),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '62', '66'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
