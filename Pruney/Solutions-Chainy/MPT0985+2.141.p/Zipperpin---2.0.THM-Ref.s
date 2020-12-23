%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pW76codPO1

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:46 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  200 (3482 expanded)
%              Number of leaves         :   47 (1071 expanded)
%              Depth                    :   24
%              Number of atoms          : 1484 (50364 expanded)
%              Number of equality atoms :   88 (1804 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('3',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('26',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X50: $i] :
      ( ( v1_funct_2 @ X50 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('36',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X18: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_relat_1 @ X18 ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('40',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k10_relat_1 @ X22 @ X23 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X22 ) @ X23 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C_1 @ X0 )
        = ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('44',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['39','46'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('49',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('50',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['47','53'])).

thf('55',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['38','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('57',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['37','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('62',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('63',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('64',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('67',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','60','61','67'])).

thf('69',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','68'])).

thf('70',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('72',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('76',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('77',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('81',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('84',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['83'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('85',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X39 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k4_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('90',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('91',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('92',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('94',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('96',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_A @ ( k4_relat_1 @ sk_C_1 ) )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['74','96'])).

thf('98',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('99',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_A @ ( k4_relat_1 @ sk_C_1 ) )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42
       != ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ k1_xboole_0 )
      | ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A )
      | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('104',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['71'])).

thf('106',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['71'])).

thf('111',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('112',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('113',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('114',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['113','116'])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('119',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('120',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','120'])).

thf('122',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['71'])).

thf('124',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['110','111','125'])).

thf('127',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('128',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('129',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('131',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['71'])).

thf('132',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['109','130','131'])).

thf('133',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['102','132'])).

thf('134',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['71'])).

thf('135',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('136',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('137',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['109','130','131'])).

thf('139',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['133','139'])).

thf('141',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('142',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('143',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('145',plain,
    ( ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_A @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X41 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X40: $i] :
      ( zip_tseitin_0 @ X40 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['145','147'])).

thf('149',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['109','130','131'])).

thf('150',plain,(
    zip_tseitin_1 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference(demod,[status(thm)],['140','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pW76codPO1
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.82/3.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.82/3.08  % Solved by: fo/fo7.sh
% 2.82/3.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.82/3.08  % done 3592 iterations in 2.628s
% 2.82/3.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.82/3.08  % SZS output start Refutation
% 2.82/3.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.82/3.08  thf(sk_B_type, type, sk_B: $i).
% 2.82/3.08  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.82/3.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.82/3.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.82/3.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.82/3.08  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.82/3.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.82/3.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.82/3.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.82/3.08  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.82/3.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.82/3.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.82/3.08  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.82/3.08  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.82/3.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.82/3.08  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.82/3.08  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.82/3.08  thf(sk_A_type, type, sk_A: $i).
% 2.82/3.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.82/3.08  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.82/3.08  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.82/3.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.82/3.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.82/3.08  thf(d1_funct_2, axiom,
% 2.82/3.08    (![A:$i,B:$i,C:$i]:
% 2.82/3.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.08       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.82/3.08           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.82/3.08             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.82/3.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.82/3.08           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.82/3.08             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.82/3.08  thf(zf_stmt_0, axiom,
% 2.82/3.08    (![B:$i,A:$i]:
% 2.82/3.08     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.82/3.08       ( zip_tseitin_0 @ B @ A ) ))).
% 2.82/3.08  thf('0', plain,
% 2.82/3.08      (![X40 : $i, X41 : $i]:
% 2.82/3.08         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.08  thf(t31_funct_2, conjecture,
% 2.82/3.08    (![A:$i,B:$i,C:$i]:
% 2.82/3.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.82/3.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.08       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.82/3.08         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.82/3.08           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.82/3.08           ( m1_subset_1 @
% 2.82/3.08             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.82/3.08  thf(zf_stmt_1, negated_conjecture,
% 2.82/3.08    (~( ![A:$i,B:$i,C:$i]:
% 2.82/3.08        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.82/3.08            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.08          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.82/3.08            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.82/3.08              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.82/3.08              ( m1_subset_1 @
% 2.82/3.08                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 2.82/3.08    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 2.82/3.08  thf('1', plain,
% 2.82/3.08      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.82/3.08  thf(zf_stmt_3, axiom,
% 2.82/3.08    (![C:$i,B:$i,A:$i]:
% 2.82/3.08     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.82/3.08       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.82/3.08  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.82/3.08  thf(zf_stmt_5, axiom,
% 2.82/3.08    (![A:$i,B:$i,C:$i]:
% 2.82/3.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.08       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.82/3.08         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.82/3.08           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.82/3.08             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.82/3.08  thf('2', plain,
% 2.82/3.08      (![X45 : $i, X46 : $i, X47 : $i]:
% 2.82/3.08         (~ (zip_tseitin_0 @ X45 @ X46)
% 2.82/3.08          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 2.82/3.08          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.82/3.08  thf('3', plain,
% 2.82/3.08      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.82/3.08        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.82/3.08      inference('sup-', [status(thm)], ['1', '2'])).
% 2.82/3.08  thf('4', plain,
% 2.82/3.08      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 2.82/3.08      inference('sup-', [status(thm)], ['0', '3'])).
% 2.82/3.08  thf('5', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('6', plain,
% 2.82/3.08      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.82/3.08         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 2.82/3.08          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 2.82/3.08          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.82/3.08  thf('7', plain,
% 2.82/3.08      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.82/3.08        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['5', '6'])).
% 2.82/3.08  thf('8', plain,
% 2.82/3.08      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf(redefinition_k1_relset_1, axiom,
% 2.82/3.08    (![A:$i,B:$i,C:$i]:
% 2.82/3.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.08       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.82/3.08  thf('9', plain,
% 2.82/3.08      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.82/3.08         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 2.82/3.08          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.82/3.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.82/3.08  thf('10', plain,
% 2.82/3.08      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('sup-', [status(thm)], ['8', '9'])).
% 2.82/3.08  thf('11', plain,
% 2.82/3.08      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.82/3.08        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['7', '10'])).
% 2.82/3.08  thf('12', plain,
% 2.82/3.08      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['4', '11'])).
% 2.82/3.08  thf('13', plain,
% 2.82/3.08      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf(cc2_relat_1, axiom,
% 2.82/3.08    (![A:$i]:
% 2.82/3.08     ( ( v1_relat_1 @ A ) =>
% 2.82/3.08       ( ![B:$i]:
% 2.82/3.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.82/3.08  thf('14', plain,
% 2.82/3.08      (![X10 : $i, X11 : $i]:
% 2.82/3.08         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 2.82/3.08          | (v1_relat_1 @ X10)
% 2.82/3.08          | ~ (v1_relat_1 @ X11))),
% 2.82/3.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.82/3.08  thf('15', plain,
% 2.82/3.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('sup-', [status(thm)], ['13', '14'])).
% 2.82/3.08  thf(fc6_relat_1, axiom,
% 2.82/3.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.82/3.08  thf('16', plain,
% 2.82/3.08      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 2.82/3.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.82/3.08  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf(d9_funct_1, axiom,
% 2.82/3.08    (![A:$i]:
% 2.82/3.08     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.82/3.08       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.82/3.08  thf('18', plain,
% 2.82/3.08      (![X20 : $i]:
% 2.82/3.08         (~ (v2_funct_1 @ X20)
% 2.82/3.08          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 2.82/3.08          | ~ (v1_funct_1 @ X20)
% 2.82/3.08          | ~ (v1_relat_1 @ X20))),
% 2.82/3.08      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.82/3.08  thf('19', plain,
% 2.82/3.08      ((~ (v1_funct_1 @ sk_C_1)
% 2.82/3.08        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 2.82/3.08        | ~ (v2_funct_1 @ sk_C_1))),
% 2.82/3.08      inference('sup-', [status(thm)], ['17', '18'])).
% 2.82/3.08  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('21', plain, ((v2_funct_1 @ sk_C_1)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('22', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.82/3.08  thf(t55_funct_1, axiom,
% 2.82/3.08    (![A:$i]:
% 2.82/3.08     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.82/3.08       ( ( v2_funct_1 @ A ) =>
% 2.82/3.08         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.82/3.08           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.82/3.08  thf('23', plain,
% 2.82/3.08      (![X24 : $i]:
% 2.82/3.08         (~ (v2_funct_1 @ X24)
% 2.82/3.08          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 2.82/3.08          | ~ (v1_funct_1 @ X24)
% 2.82/3.08          | ~ (v1_relat_1 @ X24))),
% 2.82/3.08      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.82/3.08  thf('24', plain,
% 2.82/3.08      ((((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 2.82/3.08        | ~ (v1_relat_1 @ sk_C_1)
% 2.82/3.08        | ~ (v1_funct_1 @ sk_C_1)
% 2.82/3.08        | ~ (v2_funct_1 @ sk_C_1))),
% 2.82/3.08      inference('sup+', [status(thm)], ['22', '23'])).
% 2.82/3.08  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf('26', plain, ((v1_funct_1 @ sk_C_1)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('27', plain, ((v2_funct_1 @ sk_C_1)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('28', plain,
% 2.82/3.08      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 2.82/3.08  thf('29', plain,
% 2.82/3.08      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf(redefinition_k2_relset_1, axiom,
% 2.82/3.08    (![A:$i,B:$i,C:$i]:
% 2.82/3.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.08       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.82/3.08  thf('30', plain,
% 2.82/3.08      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.82/3.08         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 2.82/3.08          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.82/3.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.82/3.08  thf('31', plain,
% 2.82/3.08      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('sup-', [status(thm)], ['29', '30'])).
% 2.82/3.08  thf('32', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('33', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 2.82/3.08      inference('sup+', [status(thm)], ['31', '32'])).
% 2.82/3.08  thf('34', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['28', '33'])).
% 2.82/3.08  thf(t3_funct_2, axiom,
% 2.82/3.08    (![A:$i]:
% 2.82/3.08     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.82/3.08       ( ( v1_funct_1 @ A ) & 
% 2.82/3.08         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.82/3.08         ( m1_subset_1 @
% 2.82/3.08           A @ 
% 2.82/3.08           ( k1_zfmisc_1 @
% 2.82/3.08             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.82/3.08  thf('35', plain,
% 2.82/3.08      (![X50 : $i]:
% 2.82/3.08         ((v1_funct_2 @ X50 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))
% 2.82/3.08          | ~ (v1_funct_1 @ X50)
% 2.82/3.08          | ~ (v1_relat_1 @ X50))),
% 2.82/3.08      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.82/3.08  thf('36', plain,
% 2.82/3.08      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ 
% 2.82/3.08         (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 2.82/3.08        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 2.82/3.08        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('sup+', [status(thm)], ['34', '35'])).
% 2.82/3.08  thf(t169_relat_1, axiom,
% 2.82/3.08    (![A:$i]:
% 2.82/3.08     ( ( v1_relat_1 @ A ) =>
% 2.82/3.08       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.82/3.08  thf('37', plain,
% 2.82/3.08      (![X18 : $i]:
% 2.82/3.08         (((k10_relat_1 @ X18 @ (k2_relat_1 @ X18)) = (k1_relat_1 @ X18))
% 2.82/3.08          | ~ (v1_relat_1 @ X18))),
% 2.82/3.08      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.82/3.08  thf(t37_relat_1, axiom,
% 2.82/3.08    (![A:$i]:
% 2.82/3.08     ( ( v1_relat_1 @ A ) =>
% 2.82/3.08       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 2.82/3.08         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 2.82/3.08  thf('38', plain,
% 2.82/3.08      (![X19 : $i]:
% 2.82/3.08         (((k2_relat_1 @ X19) = (k1_relat_1 @ (k4_relat_1 @ X19)))
% 2.82/3.08          | ~ (v1_relat_1 @ X19))),
% 2.82/3.08      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.82/3.08  thf(t146_relat_1, axiom,
% 2.82/3.08    (![A:$i]:
% 2.82/3.08     ( ( v1_relat_1 @ A ) =>
% 2.82/3.08       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.82/3.08  thf('39', plain,
% 2.82/3.08      (![X17 : $i]:
% 2.82/3.08         (((k9_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (k2_relat_1 @ X17))
% 2.82/3.08          | ~ (v1_relat_1 @ X17))),
% 2.82/3.08      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.82/3.08  thf('40', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.82/3.08  thf(t155_funct_1, axiom,
% 2.82/3.08    (![A:$i,B:$i]:
% 2.82/3.08     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.82/3.08       ( ( v2_funct_1 @ B ) =>
% 2.82/3.08         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 2.82/3.08  thf('41', plain,
% 2.82/3.08      (![X22 : $i, X23 : $i]:
% 2.82/3.08         (~ (v2_funct_1 @ X22)
% 2.82/3.08          | ((k10_relat_1 @ X22 @ X23)
% 2.82/3.08              = (k9_relat_1 @ (k2_funct_1 @ X22) @ X23))
% 2.82/3.08          | ~ (v1_funct_1 @ X22)
% 2.82/3.08          | ~ (v1_relat_1 @ X22))),
% 2.82/3.08      inference('cnf', [status(esa)], [t155_funct_1])).
% 2.82/3.08  thf('42', plain,
% 2.82/3.08      (![X0 : $i]:
% 2.82/3.08         (((k10_relat_1 @ sk_C_1 @ X0)
% 2.82/3.08            = (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))
% 2.82/3.08          | ~ (v1_relat_1 @ sk_C_1)
% 2.82/3.08          | ~ (v1_funct_1 @ sk_C_1)
% 2.82/3.08          | ~ (v2_funct_1 @ sk_C_1))),
% 2.82/3.08      inference('sup+', [status(thm)], ['40', '41'])).
% 2.82/3.08  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf('44', plain, ((v1_funct_1 @ sk_C_1)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('45', plain, ((v2_funct_1 @ sk_C_1)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('46', plain,
% 2.82/3.08      (![X0 : $i]:
% 2.82/3.08         ((k10_relat_1 @ sk_C_1 @ X0)
% 2.82/3.08           = (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))),
% 2.82/3.08      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 2.82/3.08  thf('47', plain,
% 2.82/3.08      ((((k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 2.82/3.08          = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 2.82/3.08        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('sup+', [status(thm)], ['39', '46'])).
% 2.82/3.08  thf('48', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.82/3.08  thf(dt_k2_funct_1, axiom,
% 2.82/3.08    (![A:$i]:
% 2.82/3.08     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.82/3.08       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.82/3.08         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.82/3.08  thf('49', plain,
% 2.82/3.08      (![X21 : $i]:
% 2.82/3.08         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 2.82/3.08          | ~ (v1_funct_1 @ X21)
% 2.82/3.08          | ~ (v1_relat_1 @ X21))),
% 2.82/3.08      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.82/3.08  thf('50', plain,
% 2.82/3.08      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 2.82/3.08        | ~ (v1_relat_1 @ sk_C_1)
% 2.82/3.08        | ~ (v1_funct_1 @ sk_C_1))),
% 2.82/3.08      inference('sup+', [status(thm)], ['48', '49'])).
% 2.82/3.08  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('53', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.82/3.08  thf('54', plain,
% 2.82/3.08      (((k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 2.82/3.08         = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['47', '53'])).
% 2.82/3.08  thf('55', plain,
% 2.82/3.08      ((((k10_relat_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1))
% 2.82/3.08          = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 2.82/3.08        | ~ (v1_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('sup+', [status(thm)], ['38', '54'])).
% 2.82/3.08  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf('57', plain,
% 2.82/3.08      (((k10_relat_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1))
% 2.82/3.08         = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['55', '56'])).
% 2.82/3.08  thf('58', plain,
% 2.82/3.08      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 2.82/3.08        | ~ (v1_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('sup+', [status(thm)], ['37', '57'])).
% 2.82/3.08  thf('59', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf('60', plain,
% 2.82/3.08      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['58', '59'])).
% 2.82/3.08  thf('61', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.82/3.08  thf('62', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.82/3.08  thf('63', plain,
% 2.82/3.08      (![X21 : $i]:
% 2.82/3.08         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 2.82/3.08          | ~ (v1_funct_1 @ X21)
% 2.82/3.08          | ~ (v1_relat_1 @ X21))),
% 2.82/3.08      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.82/3.08  thf('64', plain,
% 2.82/3.08      (((v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 2.82/3.08        | ~ (v1_relat_1 @ sk_C_1)
% 2.82/3.08        | ~ (v1_funct_1 @ sk_C_1))),
% 2.82/3.08      inference('sup+', [status(thm)], ['62', '63'])).
% 2.82/3.08  thf('65', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf('66', plain, ((v1_funct_1 @ sk_C_1)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('67', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['64', '65', '66'])).
% 2.82/3.08  thf('68', plain,
% 2.82/3.08      ((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['36', '60', '61', '67'])).
% 2.82/3.08  thf('69', plain,
% 2.82/3.08      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A)
% 2.82/3.08        | ((sk_B) = (k1_xboole_0)))),
% 2.82/3.08      inference('sup+', [status(thm)], ['12', '68'])).
% 2.82/3.08  thf('70', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.82/3.08  thf('71', plain,
% 2.82/3.08      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 2.82/3.08        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 2.82/3.08        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('72', plain,
% 2.82/3.08      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('split', [status(esa)], ['71'])).
% 2.82/3.08  thf('73', plain,
% 2.82/3.08      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['70', '72'])).
% 2.82/3.08  thf('74', plain,
% 2.82/3.08      ((((sk_B) = (k1_xboole_0)))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['69', '73'])).
% 2.82/3.08  thf('75', plain,
% 2.82/3.08      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf(cc2_relset_1, axiom,
% 2.82/3.08    (![A:$i,B:$i,C:$i]:
% 2.82/3.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.82/3.08  thf('76', plain,
% 2.82/3.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.82/3.08         ((v4_relat_1 @ X25 @ X26)
% 2.82/3.08          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 2.82/3.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.82/3.08  thf('77', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 2.82/3.08      inference('sup-', [status(thm)], ['75', '76'])).
% 2.82/3.08  thf(d18_relat_1, axiom,
% 2.82/3.08    (![A:$i,B:$i]:
% 2.82/3.08     ( ( v1_relat_1 @ B ) =>
% 2.82/3.08       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.82/3.08  thf('78', plain,
% 2.82/3.08      (![X12 : $i, X13 : $i]:
% 2.82/3.08         (~ (v4_relat_1 @ X12 @ X13)
% 2.82/3.08          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 2.82/3.08          | ~ (v1_relat_1 @ X12))),
% 2.82/3.08      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.82/3.08  thf('79', plain,
% 2.82/3.08      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 2.82/3.08      inference('sup-', [status(thm)], ['77', '78'])).
% 2.82/3.08  thf('80', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf('81', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 2.82/3.08      inference('demod', [status(thm)], ['79', '80'])).
% 2.82/3.08  thf('82', plain,
% 2.82/3.08      (![X19 : $i]:
% 2.82/3.08         (((k1_relat_1 @ X19) = (k2_relat_1 @ (k4_relat_1 @ X19)))
% 2.82/3.08          | ~ (v1_relat_1 @ X19))),
% 2.82/3.08      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.82/3.08  thf(d10_xboole_0, axiom,
% 2.82/3.08    (![A:$i,B:$i]:
% 2.82/3.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.82/3.08  thf('83', plain,
% 2.82/3.08      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.82/3.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.82/3.08  thf('84', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.82/3.08      inference('simplify', [status(thm)], ['83'])).
% 2.82/3.08  thf(t11_relset_1, axiom,
% 2.82/3.08    (![A:$i,B:$i,C:$i]:
% 2.82/3.08     ( ( v1_relat_1 @ C ) =>
% 2.82/3.08       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 2.82/3.08           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 2.82/3.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.82/3.08  thf('85', plain,
% 2.82/3.08      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.82/3.08         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 2.82/3.08          | ~ (r1_tarski @ (k2_relat_1 @ X37) @ X39)
% 2.82/3.08          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.82/3.08          | ~ (v1_relat_1 @ X37))),
% 2.82/3.08      inference('cnf', [status(esa)], [t11_relset_1])).
% 2.82/3.08  thf('86', plain,
% 2.82/3.08      (![X0 : $i, X1 : $i]:
% 2.82/3.08         (~ (v1_relat_1 @ X0)
% 2.82/3.08          | (m1_subset_1 @ X0 @ 
% 2.82/3.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 2.82/3.08          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 2.82/3.08      inference('sup-', [status(thm)], ['84', '85'])).
% 2.82/3.08  thf('87', plain,
% 2.82/3.08      (![X0 : $i, X1 : $i]:
% 2.82/3.08         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 2.82/3.08          | ~ (v1_relat_1 @ X0)
% 2.82/3.08          | (m1_subset_1 @ (k4_relat_1 @ X0) @ 
% 2.82/3.08             (k1_zfmisc_1 @ 
% 2.82/3.08              (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ X1)))
% 2.82/3.08          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['82', '86'])).
% 2.82/3.08  thf('88', plain,
% 2.82/3.08      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 2.82/3.08        | (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08           (k1_zfmisc_1 @ 
% 2.82/3.08            (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_1)) @ sk_A)))
% 2.82/3.08        | ~ (v1_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('sup-', [status(thm)], ['81', '87'])).
% 2.82/3.08  thf('89', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.82/3.08  thf('90', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['28', '33'])).
% 2.82/3.08  thf('91', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf('92', plain,
% 2.82/3.08      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.08      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 2.82/3.08  thf('93', plain,
% 2.82/3.08      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.82/3.08         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 2.82/3.08          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.82/3.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.82/3.08  thf('94', plain,
% 2.82/3.08      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C_1))
% 2.82/3.08         = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['92', '93'])).
% 2.82/3.08  thf('95', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['28', '33'])).
% 2.82/3.08  thf('96', plain,
% 2.82/3.08      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C_1)) = (sk_B))),
% 2.82/3.08      inference('demod', [status(thm)], ['94', '95'])).
% 2.82/3.08  thf('97', plain,
% 2.82/3.08      ((((k1_relset_1 @ k1_xboole_0 @ sk_A @ (k4_relat_1 @ sk_C_1)) = (sk_B)))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('sup+', [status(thm)], ['74', '96'])).
% 2.82/3.08  thf('98', plain,
% 2.82/3.08      ((((sk_B) = (k1_xboole_0)))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['69', '73'])).
% 2.82/3.08  thf('99', plain,
% 2.82/3.08      ((((k1_relset_1 @ k1_xboole_0 @ sk_A @ (k4_relat_1 @ sk_C_1))
% 2.82/3.08          = (k1_xboole_0)))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('demod', [status(thm)], ['97', '98'])).
% 2.82/3.08  thf('100', plain,
% 2.82/3.08      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.82/3.08         (((X42) != (k1_relset_1 @ X42 @ X43 @ X44))
% 2.82/3.08          | (v1_funct_2 @ X44 @ X42 @ X43)
% 2.82/3.08          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.82/3.08  thf('101', plain,
% 2.82/3.08      (((((k1_xboole_0) != (k1_xboole_0))
% 2.82/3.08         | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C_1) @ sk_A @ k1_xboole_0)
% 2.82/3.08         | (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ k1_xboole_0 @ sk_A)))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['99', '100'])).
% 2.82/3.08  thf('102', plain,
% 2.82/3.08      ((((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ k1_xboole_0 @ sk_A)
% 2.82/3.08         | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C_1) @ sk_A @ k1_xboole_0)))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('simplify', [status(thm)], ['101'])).
% 2.82/3.08  thf('103', plain, ((v1_relat_1 @ sk_C_1)),
% 2.82/3.08      inference('demod', [status(thm)], ['15', '16'])).
% 2.82/3.08  thf('104', plain,
% 2.82/3.08      (![X21 : $i]:
% 2.82/3.08         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 2.82/3.08          | ~ (v1_funct_1 @ X21)
% 2.82/3.08          | ~ (v1_relat_1 @ X21))),
% 2.82/3.08      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.82/3.08  thf('105', plain,
% 2.82/3.08      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 2.82/3.08         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 2.82/3.08      inference('split', [status(esa)], ['71'])).
% 2.82/3.08  thf('106', plain,
% 2.82/3.08      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 2.82/3.08         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 2.82/3.08      inference('sup-', [status(thm)], ['104', '105'])).
% 2.82/3.08  thf('107', plain, ((v1_funct_1 @ sk_C_1)),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.82/3.08  thf('108', plain,
% 2.82/3.08      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 2.82/3.08      inference('demod', [status(thm)], ['106', '107'])).
% 2.82/3.08  thf('109', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['103', '108'])).
% 2.82/3.08  thf('110', plain,
% 2.82/3.08      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.82/3.08         <= (~
% 2.82/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.82/3.08      inference('split', [status(esa)], ['71'])).
% 2.82/3.08  thf('111', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.82/3.08  thf('112', plain,
% 2.82/3.08      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['4', '11'])).
% 2.82/3.08  thf('113', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['28', '33'])).
% 2.82/3.08  thf('114', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.82/3.08      inference('simplify', [status(thm)], ['83'])).
% 2.82/3.08  thf('115', plain,
% 2.82/3.08      (![X0 : $i, X1 : $i]:
% 2.82/3.08         (~ (v1_relat_1 @ X0)
% 2.82/3.08          | (m1_subset_1 @ X0 @ 
% 2.82/3.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 2.82/3.08          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 2.82/3.08      inference('sup-', [status(thm)], ['84', '85'])).
% 2.82/3.08  thf('116', plain,
% 2.82/3.08      (![X0 : $i]:
% 2.82/3.08         ((m1_subset_1 @ X0 @ 
% 2.82/3.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 2.82/3.08          | ~ (v1_relat_1 @ X0))),
% 2.82/3.08      inference('sup-', [status(thm)], ['114', '115'])).
% 2.82/3.08  thf('117', plain,
% 2.82/3.08      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08         (k1_zfmisc_1 @ 
% 2.82/3.08          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))))
% 2.82/3.08        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('sup+', [status(thm)], ['113', '116'])).
% 2.82/3.08  thf('118', plain,
% 2.82/3.08      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.82/3.08      inference('demod', [status(thm)], ['58', '59'])).
% 2.82/3.08  thf('119', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.82/3.08  thf('120', plain,
% 2.82/3.08      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 2.82/3.08      inference('demod', [status(thm)], ['117', '118', '119'])).
% 2.82/3.08  thf('121', plain,
% 2.82/3.08      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.82/3.08        | ((sk_B) = (k1_xboole_0)))),
% 2.82/3.08      inference('sup+', [status(thm)], ['112', '120'])).
% 2.82/3.08  thf('122', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.82/3.08  thf('123', plain,
% 2.82/3.08      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.82/3.08         <= (~
% 2.82/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.82/3.08      inference('split', [status(esa)], ['71'])).
% 2.82/3.08  thf('124', plain,
% 2.82/3.08      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.82/3.08         <= (~
% 2.82/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.82/3.08      inference('sup-', [status(thm)], ['122', '123'])).
% 2.82/3.08  thf('125', plain,
% 2.82/3.08      ((((sk_B) = (k1_xboole_0)))
% 2.82/3.08         <= (~
% 2.82/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.82/3.08      inference('sup-', [status(thm)], ['121', '124'])).
% 2.82/3.08  thf('126', plain,
% 2.82/3.08      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A))))
% 2.82/3.08         <= (~
% 2.82/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.82/3.08      inference('demod', [status(thm)], ['110', '111', '125'])).
% 2.82/3.08  thf('127', plain,
% 2.82/3.08      ((((sk_B) = (k1_xboole_0)))
% 2.82/3.08         <= (~
% 2.82/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.82/3.08      inference('sup-', [status(thm)], ['121', '124'])).
% 2.82/3.08  thf('128', plain,
% 2.82/3.08      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.08      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 2.82/3.08  thf('129', plain,
% 2.82/3.08      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A))))
% 2.82/3.08         <= (~
% 2.82/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.82/3.08      inference('sup+', [status(thm)], ['127', '128'])).
% 2.82/3.08  thf('130', plain,
% 2.82/3.08      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.82/3.08      inference('demod', [status(thm)], ['126', '129'])).
% 2.82/3.08  thf('131', plain,
% 2.82/3.08      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 2.82/3.08       ~
% 2.82/3.08       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.82/3.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 2.82/3.08       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 2.82/3.08      inference('split', [status(esa)], ['71'])).
% 2.82/3.08  thf('132', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 2.82/3.08      inference('sat_resolution*', [status(thm)], ['109', '130', '131'])).
% 2.82/3.08  thf('133', plain,
% 2.82/3.08      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ k1_xboole_0 @ sk_A)
% 2.82/3.08        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C_1) @ sk_A @ k1_xboole_0))),
% 2.82/3.08      inference('simpl_trail', [status(thm)], ['102', '132'])).
% 2.82/3.08  thf('134', plain,
% 2.82/3.08      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('split', [status(esa)], ['71'])).
% 2.82/3.08  thf('135', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.82/3.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.82/3.08  thf('136', plain,
% 2.82/3.08      ((((sk_B) = (k1_xboole_0)))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['69', '73'])).
% 2.82/3.08  thf('137', plain,
% 2.82/3.08      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ k1_xboole_0 @ sk_A))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('demod', [status(thm)], ['134', '135', '136'])).
% 2.82/3.08  thf('138', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 2.82/3.08      inference('sat_resolution*', [status(thm)], ['109', '130', '131'])).
% 2.82/3.08  thf('139', plain,
% 2.82/3.08      (~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ k1_xboole_0 @ sk_A)),
% 2.82/3.08      inference('simpl_trail', [status(thm)], ['137', '138'])).
% 2.82/3.08  thf('140', plain,
% 2.82/3.08      (~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C_1) @ sk_A @ k1_xboole_0)),
% 2.82/3.08      inference('clc', [status(thm)], ['133', '139'])).
% 2.82/3.08  thf('141', plain,
% 2.82/3.08      ((((sk_B) = (k1_xboole_0)))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['69', '73'])).
% 2.82/3.08  thf('142', plain,
% 2.82/3.08      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.08      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 2.82/3.08  thf('143', plain,
% 2.82/3.08      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.82/3.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A))))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('sup+', [status(thm)], ['141', '142'])).
% 2.82/3.08  thf('144', plain,
% 2.82/3.08      (![X45 : $i, X46 : $i, X47 : $i]:
% 2.82/3.08         (~ (zip_tseitin_0 @ X45 @ X46)
% 2.82/3.08          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 2.82/3.08          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.82/3.08  thf('145', plain,
% 2.82/3.08      ((((zip_tseitin_1 @ (k4_relat_1 @ sk_C_1) @ sk_A @ k1_xboole_0)
% 2.82/3.08         | ~ (zip_tseitin_0 @ sk_A @ k1_xboole_0)))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('sup-', [status(thm)], ['143', '144'])).
% 2.82/3.08  thf('146', plain,
% 2.82/3.08      (![X40 : $i, X41 : $i]:
% 2.82/3.08         ((zip_tseitin_0 @ X40 @ X41) | ((X41) != (k1_xboole_0)))),
% 2.82/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.08  thf('147', plain, (![X40 : $i]: (zip_tseitin_0 @ X40 @ k1_xboole_0)),
% 2.82/3.08      inference('simplify', [status(thm)], ['146'])).
% 2.82/3.08  thf('148', plain,
% 2.82/3.08      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C_1) @ sk_A @ k1_xboole_0))
% 2.82/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 2.82/3.08      inference('demod', [status(thm)], ['145', '147'])).
% 2.82/3.08  thf('149', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 2.82/3.08      inference('sat_resolution*', [status(thm)], ['109', '130', '131'])).
% 2.82/3.08  thf('150', plain,
% 2.82/3.08      ((zip_tseitin_1 @ (k4_relat_1 @ sk_C_1) @ sk_A @ k1_xboole_0)),
% 2.82/3.08      inference('simpl_trail', [status(thm)], ['148', '149'])).
% 2.82/3.08  thf('151', plain, ($false), inference('demod', [status(thm)], ['140', '150'])).
% 2.82/3.08  
% 2.82/3.08  % SZS output end Refutation
% 2.82/3.08  
% 2.82/3.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
