%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0lkUmXsejC

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 499 expanded)
%              Number of leaves         :   46 ( 171 expanded)
%              Depth                    :   22
%              Number of atoms          :  828 (5822 expanded)
%              Number of equality atoms :   48 ( 273 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k7_relset_1 @ X43 @ X44 @ X42 @ X45 )
        = ( k9_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 )
      | ( r2_hidden @ X46 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v4_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_0 @ D @ C @ B @ A ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ X54 )
       != X53 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X54 @ X55 @ X53 ) @ X54 @ X55 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X55 @ X53 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ~ ( v1_funct_1 @ X54 )
      | ( zip_tseitin_1 @ X54 @ X55 @ ( k1_relat_1 @ X54 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X54 @ X55 @ ( k1_relat_1 @ X54 ) ) @ X54 @ X55 @ ( k1_relat_1 @ X54 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_D_1 @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('34',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ k1_xboole_0 ) @ sk_D_1 @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','36'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ sk_D_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( zip_tseitin_1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ sk_D_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('59',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X36 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('65',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('69',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('70',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','53'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['4','54','73','74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0lkUmXsejC
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 228 iterations in 0.063s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.19/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.19/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(t64_funct_2, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.51         ( m1_subset_1 @
% 0.19/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.51       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.51         ( r1_tarski @
% 0.19/0.51           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.19/0.51           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.51            ( m1_subset_1 @
% 0.19/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.51          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.51            ( r1_tarski @
% 0.19/0.51              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.19/0.51              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (~ (r1_tarski @ 
% 0.19/0.51          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.19/0.51          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.19/0.51          | ((k7_relset_1 @ X43 @ X44 @ X42 @ X45) = (k9_relat_1 @ X42 @ X45)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.19/0.51           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.19/0.51          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.51  thf(t5_funct_2, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.19/0.51       ( ( ( ![D:$i]:
% 0.19/0.51             ( ( r2_hidden @ D @ A ) =>
% 0.19/0.51               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.19/0.51           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.51           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_1, axiom,
% 0.19/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.51     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.19/0.51       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.19/0.51         ((zip_tseitin_0 @ X46 @ X47 @ X48 @ X49) | (r2_hidden @ X46 @ X49))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.51  thf(t144_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X24 : $i, X25 : $i]:
% 0.19/0.51         ((r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k2_relat_1 @ X24))
% 0.19/0.51          | ~ (v1_relat_1 @ X24))),
% 0.19/0.51      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc2_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.51         ((v4_relat_1 @ X33 @ X34)
% 0.19/0.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.51  thf('9', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.51  thf(d18_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (![X22 : $i, X23 : $i]:
% 0.19/0.51         (~ (v4_relat_1 @ X22 @ X23)
% 0.19/0.51          | (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.19/0.51          | ~ (v1_relat_1 @ X22))),
% 0.19/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_D_1)
% 0.19/0.51        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc1_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( v1_relat_1 @ C ) ))).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.51         ((v1_relat_1 @ X30)
% 0.19/0.51          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.51  thf('14', plain, ((v1_relat_1 @ sk_D_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['11', '14'])).
% 0.19/0.51  thf(l3_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X9 : $i, X10 : $i]:
% 0.19/0.51         (((X10) = (k1_tarski @ X9))
% 0.19/0.51          | ((X10) = (k1_xboole_0))
% 0.19/0.51          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 0.19/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.51        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.51  thf(t14_funct_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.51       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.19/0.51         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X26 : $i, X27 : $i]:
% 0.19/0.51         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 0.19/0.51          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 0.19/0.51          | ~ (v1_funct_1 @ X27)
% 0.19/0.51          | ~ (v1_relat_1 @ X27))),
% 0.19/0.51      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_1))
% 0.19/0.51          | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.19/0.51        | ~ (v1_funct_1 @ sk_D_1)
% 0.19/0.51        | ~ (v1_relat_1 @ sk_D_1)
% 0.19/0.51        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.51      inference('eq_res', [status(thm)], ['19'])).
% 0.19/0.51  thf('21', plain, ((v1_funct_1 @ sk_D_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.19/0.51        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.19/0.51          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 0.19/0.51        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '25'])).
% 0.19/0.51  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('28', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.19/0.51  thf(zf_stmt_3, axiom,
% 0.19/0.51    (![C:$i,B:$i,A:$i]:
% 0.19/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.19/0.51       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.19/0.51  thf(zf_stmt_5, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.51       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.19/0.51           ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) =>
% 0.19/0.51         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.19/0.51         (((k1_relat_1 @ X54) != (X53))
% 0.19/0.51          | ~ (zip_tseitin_0 @ (sk_D @ X54 @ X55 @ X53) @ X54 @ X55 @ X53)
% 0.19/0.51          | (zip_tseitin_1 @ X54 @ X55 @ X53)
% 0.19/0.51          | ~ (v1_funct_1 @ X54)
% 0.19/0.51          | ~ (v1_relat_1 @ X54))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (![X54 : $i, X55 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X54)
% 0.19/0.51          | ~ (v1_funct_1 @ X54)
% 0.19/0.51          | (zip_tseitin_1 @ X54 @ X55 @ (k1_relat_1 @ X54))
% 0.19/0.51          | ~ (zip_tseitin_0 @ (sk_D @ X54 @ X55 @ (k1_relat_1 @ X54)) @ X54 @ 
% 0.19/0.51               X55 @ (k1_relat_1 @ X54)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ 
% 0.19/0.51             sk_D_1 @ X0 @ k1_xboole_0)
% 0.19/0.51          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.19/0.51          | ~ (v1_funct_1 @ sk_D_1)
% 0.19/0.51          | ~ (v1_relat_1 @ sk_D_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['28', '30'])).
% 0.19/0.51  thf('32', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.51  thf('33', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.51  thf('34', plain, ((v1_funct_1 @ sk_D_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('35', plain, ((v1_relat_1 @ sk_D_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ k1_xboole_0) @ sk_D_1 @ 
% 0.19/0.51             X0 @ k1_xboole_0)
% 0.19/0.51          | (zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.51          | (zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '36'])).
% 0.19/0.51  thf(t7_ordinal1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (![X28 : $i, X29 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0)
% 0.19/0.51          | ~ (r1_tarski @ k1_xboole_0 @ (sk_D @ sk_D_1 @ X0 @ k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.51  thf(t4_subset_1, axiom,
% 0.19/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.51  thf(t3_subset, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i]:
% 0.19/0.51         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.51  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.51  thf('43', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0)),
% 0.19/0.51      inference('demod', [status(thm)], ['39', '42'])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.19/0.51         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.19/0.51          | ~ (zip_tseitin_1 @ X50 @ X51 @ X52))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (m1_subset_1 @ sk_D_1 @ 
% 0.19/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.51  thf(t113_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (![X13 : $i, X14 : $i]:
% 0.19/0.51         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.19/0.51          | ((X13) != (k1_xboole_0)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.19/0.51  thf('48', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['45', '47'])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i]:
% 0.19/0.51         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.51  thf('50', plain, ((r1_tarski @ sk_D_1 @ k1_xboole_0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.51  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.51  thf(d10_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      (![X0 : $i, X2 : $i]:
% 0.19/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.51  thf('53', plain,
% 0.19/0.51      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.51  thf('54', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['50', '53'])).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.51  thf('56', plain,
% 0.19/0.51      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.19/0.51         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 0.19/0.51          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.51  thf('58', plain,
% 0.19/0.51      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.51  thf(dt_k2_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.51  thf('59', plain,
% 0.19/0.51      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.19/0.51         ((m1_subset_1 @ (k2_relset_1 @ X36 @ X37 @ X38) @ (k1_zfmisc_1 @ X37))
% 0.19/0.51          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.19/0.51  thf('60', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (m1_subset_1 @ (k2_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 0.19/0.51          (k1_zfmisc_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.51  thf('61', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (m1_subset_1 @ (k2_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['57', '60'])).
% 0.19/0.51  thf('62', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i]:
% 0.19/0.51         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.51  thf('63', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['61', '62'])).
% 0.19/0.51  thf('64', plain,
% 0.19/0.51      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.51  thf('65', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.19/0.51  thf('66', plain,
% 0.19/0.51      (![X24 : $i, X25 : $i]:
% 0.19/0.51         ((r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k2_relat_1 @ X24))
% 0.19/0.51          | ~ (v1_relat_1 @ X24))),
% 0.19/0.51      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.19/0.51  thf('67', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.51          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['65', '66'])).
% 0.19/0.51  thf('68', plain,
% 0.19/0.51      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.51  thf('69', plain,
% 0.19/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.51         ((v1_relat_1 @ X30)
% 0.19/0.51          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.51  thf('70', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.19/0.51  thf('71', plain,
% 0.19/0.51      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.19/0.51      inference('demod', [status(thm)], ['67', '70'])).
% 0.19/0.51  thf('72', plain,
% 0.19/0.51      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.51  thf('73', plain,
% 0.19/0.51      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['71', '72'])).
% 0.19/0.51  thf('74', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['50', '53'])).
% 0.19/0.51  thf('75', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.51  thf('76', plain, ($false),
% 0.19/0.51      inference('demod', [status(thm)], ['4', '54', '73', '74', '75'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
