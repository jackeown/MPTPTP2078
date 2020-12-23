%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WoKCq5EzXA

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 (1534 expanded)
%              Number of leaves         :   30 ( 450 expanded)
%              Depth                    :   16
%              Number of atoms          :  630 (28077 expanded)
%              Number of equality atoms :   65 (2231 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X22 ) @ ( k1_funct_1 @ X22 @ X19 ) )
        = X19 )
      | ~ ( v2_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_funct_1 @ sk_B @ sk_C )
    = ( k1_funct_1 @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_D ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_C != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','18'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','34'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ( X15
        = ( k1_funct_1 @ ( k2_funct_1 @ X14 ) @ ( k1_funct_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('48',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('49',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('52',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('53',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['45','46','47','48','49','50','51','52'])).

thf('54',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','53'])).

thf('55',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['45','46','47','48','49','50','51','52'])).

thf('57',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','54','57'])).

thf('59',plain,
    ( sk_C
    = ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','58'])).

thf('60',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('62',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','54','57'])).

thf('64',plain,
    ( sk_D
    = ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_funct_1 @ sk_B @ sk_C )
    = ( k1_funct_1 @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['45','46','47','48','49','50','51','52'])).

thf('67',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['45','46','47','48','49','50','51','52'])).

thf('68',plain,
    ( ( k1_funct_1 @ k1_xboole_0 @ sk_C )
    = ( k1_funct_1 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( sk_D
    = ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','68'])).

thf('70',plain,(
    sk_D = sk_C ),
    inference('sup+',[status(thm)],['59','69'])).

thf('71',plain,(
    sk_C != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WoKCq5EzXA
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:07:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 96 iterations in 0.037s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(t85_funct_2, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.50       ( ( v2_funct_1 @ B ) =>
% 0.22/0.50         ( ![C:$i,D:$i]:
% 0.22/0.50           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.50               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.50             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.50          ( ( v2_funct_1 @ B ) =>
% 0.22/0.50            ( ![C:$i,D:$i]:
% 0.22/0.50              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.50                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.50                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.22/0.50  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t32_funct_2, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.50       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.22/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.50           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.22/0.50             ( C ) ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X19 @ X20)
% 0.22/0.50          | ((X21) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_funct_1 @ X22)
% 0.22/0.50          | ~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.22/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.22/0.50          | ((k1_funct_1 @ (k2_funct_1 @ X22) @ (k1_funct_1 @ X22 @ X19))
% 0.22/0.50              = (X19))
% 0.22/0.50          | ~ (v2_funct_1 @ X22))),
% 0.22/0.50      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_funct_1 @ sk_B)
% 0.22/0.50          | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0))
% 0.22/0.50              = (X0))
% 0.22/0.50          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.50          | ((sk_A) = (k1_xboole_0))
% 0.22/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain, ((v2_funct_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0)) = (X0))
% 0.22/0.50          | ((sk_A) = (k1_xboole_0))
% 0.22/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((((sk_A) = (k1_xboole_0))
% 0.22/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C))
% 0.22/0.50            = (sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '8'])).
% 0.22/0.50  thf('10', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0)) = (X0))
% 0.22/0.50          | ((sk_A) = (k1_xboole_0))
% 0.22/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((((sk_A) = (k1_xboole_0))
% 0.22/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_D))
% 0.22/0.50            = (sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('13', plain, (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((((sk_A) = (k1_xboole_0))
% 0.22/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C))
% 0.22/0.50            = (sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((((sk_C) = (sk_D)) | ((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['9', '14'])).
% 0.22/0.50  thf('16', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_D)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.50  thf('17', plain, (((sk_C) != (sk_D))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('18', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain, ((r2_hidden @ sk_C @ k1_xboole_0)),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '18'])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('20', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X7 : $i, X9 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf(cc2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.50         ((v4_relat_1 @ X16 @ X17)
% 0.22/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('24', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf(d18_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (v4_relat_1 @ X10 @ X11)
% 0.22/0.50          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.22/0.50          | ~ (v1_relat_1 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf(t113_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.50  thf(fc6_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.50  thf('30', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.22/0.50      inference('demod', [status(thm)], ['26', '30'])).
% 0.22/0.50  thf('32', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i]:
% 0.22/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['31', '34'])).
% 0.22/0.50  thf(t56_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.22/0.50         ( ( ( A ) =
% 0.22/0.50             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.22/0.50           ( ( A ) =
% 0.22/0.50             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (v2_funct_1 @ X14)
% 0.22/0.50          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 0.22/0.50          | ((X15)
% 0.22/0.50              = (k1_funct_1 @ (k2_funct_1 @ X14) @ (k1_funct_1 @ X14 @ X15)))
% 0.22/0.50          | ~ (v1_funct_1 @ X14)
% 0.22/0.50          | ~ (v1_relat_1 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.50          | ((X0)
% 0.22/0.50              = (k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 0.22/0.50                 (k1_funct_1 @ k1_xboole_0 @ X0)))
% 0.22/0.50          | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.50          | ((X0)
% 0.22/0.50              = (k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 0.22/0.50                 (k1_funct_1 @ k1_xboole_0 @ X0)))
% 0.22/0.50          | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i]:
% 0.22/0.50         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('43', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i]:
% 0.22/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_B)
% 0.22/0.50        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.50  thf('49', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.50  thf('53', plain, (((k1_xboole_0) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['45', '46', '47', '48', '49', '50', '51', '52'])).
% 0.22/0.50  thf('54', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.22/0.50      inference('demod', [status(thm)], ['40', '53'])).
% 0.22/0.50  thf('55', plain, ((v2_funct_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('56', plain, (((k1_xboole_0) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['45', '46', '47', '48', '49', '50', '51', '52'])).
% 0.22/0.50  thf('57', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.22/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.50          | ((X0)
% 0.22/0.50              = (k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 0.22/0.50                 (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['39', '54', '57'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      (((sk_C)
% 0.22/0.50         = (k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 0.22/0.50            (k1_funct_1 @ k1_xboole_0 @ sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '58'])).
% 0.22/0.50  thf('60', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('62', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.22/0.50      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.50          | ((X0)
% 0.22/0.50              = (k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 0.22/0.50                 (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['39', '54', '57'])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      (((sk_D)
% 0.22/0.50         = (k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 0.22/0.50            (k1_funct_1 @ k1_xboole_0 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.50  thf('65', plain, (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('66', plain, (((k1_xboole_0) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['45', '46', '47', '48', '49', '50', '51', '52'])).
% 0.22/0.50  thf('67', plain, (((k1_xboole_0) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['45', '46', '47', '48', '49', '50', '51', '52'])).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      (((k1_funct_1 @ k1_xboole_0 @ sk_C) = (k1_funct_1 @ k1_xboole_0 @ sk_D))),
% 0.22/0.50      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      (((sk_D)
% 0.22/0.50         = (k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 0.22/0.50            (k1_funct_1 @ k1_xboole_0 @ sk_C)))),
% 0.22/0.50      inference('demod', [status(thm)], ['64', '68'])).
% 0.22/0.50  thf('70', plain, (((sk_D) = (sk_C))),
% 0.22/0.50      inference('sup+', [status(thm)], ['59', '69'])).
% 0.22/0.50  thf('71', plain, (((sk_C) != (sk_D))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('72', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
