%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESDLcFfDkF

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 540 expanded)
%              Number of leaves         :   45 ( 184 expanded)
%              Depth                    :   23
%              Number of atoms          :  824 (6059 expanded)
%              Number of equality atoms :   48 ( 276 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k7_relset_1 @ X42 @ X43 @ X41 @ X44 )
        = ( k9_relat_1 @ X41 @ X44 ) ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 )
      | ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X28 @ X29 ) @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v4_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('19',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ X31 )
       != ( k1_tarski @ X30 ) )
      | ( ( k2_relat_1 @ X31 )
        = ( k1_tarski @ ( k1_funct_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ X53 )
       != X52 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X53 @ X54 @ X52 ) @ X53 @ X54 @ X52 )
      | ( zip_tseitin_1 @ X53 @ X54 @ X52 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ~ ( v1_funct_1 @ X53 )
      | ( zip_tseitin_1 @ X53 @ X54 @ ( k1_relat_1 @ X53 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X53 @ X54 @ ( k1_relat_1 @ X53 ) ) @ X53 @ X54 @ ( k1_relat_1 @ X53 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ k1_xboole_0 ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ k1_xboole_0 ) @ sk_D_1 @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','40'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ sk_D_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( zip_tseitin_1 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ sk_D_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('60',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relset_1 @ X2 @ X0 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('67',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k7_relset_1 @ X42 @ X43 @ X41 @ X44 )
        = ( k9_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['4','58','69','70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESDLcFfDkF
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 212 iterations in 0.070s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(t64_funct_2, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.52         ( m1_subset_1 @
% 0.20/0.52           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.52       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.52         ( r1_tarski @
% 0.20/0.52           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.20/0.52           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.52            ( m1_subset_1 @
% 0.20/0.52              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.52          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.52            ( r1_tarski @
% 0.20/0.52              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.20/0.52              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (~ (r1_tarski @ 
% 0.20/0.52          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.20/0.52          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.20/0.52          | ((k7_relset_1 @ X42 @ X43 @ X41 @ X44) = (k9_relat_1 @ X41 @ X44)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.20/0.52           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.52          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.52  thf(t5_funct_2, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.20/0.52       ( ( ( ![D:$i]:
% 0.20/0.52             ( ( r2_hidden @ D @ A ) =>
% 0.20/0.52               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.20/0.52           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.52           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_1, axiom,
% 0.20/0.52    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.52     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.20/0.52       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.20/0.52         ((zip_tseitin_0 @ X45 @ X46 @ X47 @ X48) | (r2_hidden @ X45 @ X48))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.52  thf(t144_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]:
% 0.20/0.52         ((r1_tarski @ (k9_relat_1 @ X28 @ X29) @ (k2_relat_1 @ X28))
% 0.20/0.52          | ~ (v1_relat_1 @ X28))),
% 0.20/0.52      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.52         ((v4_relat_1 @ X34 @ X35)
% 0.20/0.52          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.52  thf('9', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf(d18_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X24 : $i, X25 : $i]:
% 0.20/0.52         (~ (v4_relat_1 @ X24 @ X25)
% 0.20/0.52          | (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.20/0.52          | ~ (v1_relat_1 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.52        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.20/0.52          | (v1_relat_1 @ X22)
% 0.20/0.52          | ~ (v1_relat_1 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.20/0.52        | (v1_relat_1 @ sk_D_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf(fc6_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.52  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.52  thf(l3_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i]:
% 0.20/0.52         (((X10) = (k1_tarski @ X9))
% 0.20/0.52          | ((X10) = (k1_xboole_0))
% 0.20/0.52          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.20/0.52        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf(t14_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.52         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X30 : $i, X31 : $i]:
% 0.20/0.52         (((k1_relat_1 @ X31) != (k1_tarski @ X30))
% 0.20/0.52          | ((k2_relat_1 @ X31) = (k1_tarski @ (k1_funct_1 @ X31 @ X30)))
% 0.20/0.52          | ~ (v1_funct_1 @ X31)
% 0.20/0.52          | ~ (v1_relat_1 @ X31))),
% 0.20/0.52      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_1))
% 0.20/0.52          | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.20/0.52        | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_D_1)
% 0.20/0.52        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('eq_res', [status(thm)], ['21'])).
% 0.20/0.52  thf('23', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.20/0.52        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (~ (r1_tarski @ 
% 0.20/0.52          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.20/0.52          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((~ (r1_tarski @ 
% 0.20/0.52           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.20/0.52           (k2_relat_1 @ sk_D_1))
% 0.20/0.52        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.20/0.52           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 0.20/0.52        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '29'])).
% 0.20/0.52  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('32', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_3, axiom,
% 0.20/0.52    (![C:$i,B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.52       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_5, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.52           ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) =>
% 0.20/0.52         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.20/0.52         (((k1_relat_1 @ X53) != (X52))
% 0.20/0.52          | ~ (zip_tseitin_0 @ (sk_D @ X53 @ X54 @ X52) @ X53 @ X54 @ X52)
% 0.20/0.52          | (zip_tseitin_1 @ X53 @ X54 @ X52)
% 0.20/0.52          | ~ (v1_funct_1 @ X53)
% 0.20/0.52          | ~ (v1_relat_1 @ X53))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X53 : $i, X54 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X53)
% 0.20/0.52          | ~ (v1_funct_1 @ X53)
% 0.20/0.52          | (zip_tseitin_1 @ X53 @ X54 @ (k1_relat_1 @ X53))
% 0.20/0.52          | ~ (zip_tseitin_0 @ (sk_D @ X53 @ X54 @ (k1_relat_1 @ X53)) @ X53 @ 
% 0.20/0.52               X54 @ (k1_relat_1 @ X53)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ k1_xboole_0) @ sk_D_1 @ 
% 0.20/0.52             X0 @ (k1_relat_1 @ sk_D_1))
% 0.20/0.52          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.20/0.52          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.52          | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '34'])).
% 0.20/0.52  thf('36', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('37', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ k1_xboole_0) @ sk_D_1 @ 
% 0.20/0.52             X0 @ k1_xboole_0)
% 0.20/0.52          | (zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.20/0.52          | (zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '40'])).
% 0.20/0.52  thf(t7_ordinal1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X32 : $i, X33 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0)
% 0.20/0.52          | ~ (r1_tarski @ k1_xboole_0 @ (sk_D @ sk_D_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf(t4_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 0.20/0.52          | ~ (zip_tseitin_1 @ X49 @ X50 @ X51))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (m1_subset_1 @ sk_D_1 @ 
% 0.20/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf(t113_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.20/0.52          | ((X13) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.52  thf('52', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '51'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('54', plain, ((r1_tarski @ sk_D_1 @ k1_xboole_0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.52  thf(dt_k7_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.20/0.52          | (m1_subset_1 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X40) @ 
% 0.20/0.52             (k1_zfmisc_1 @ X39)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (m1_subset_1 @ (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 0.20/0.52          (k1_zfmisc_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (r1_tarski @ (k7_relset_1 @ X2 @ X0 @ k1_xboole_0 @ X1) @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k7_relset_1 @ X1 @ k1_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.20/0.52          | ((k7_relset_1 @ X42 @ X43 @ X41 @ X44) = (k9_relat_1 @ X41 @ X44)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.20/0.52           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['65', '68'])).
% 0.20/0.52  thf('70', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '57'])).
% 0.20/0.52  thf('71', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('72', plain, ($false),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '58', '69', '70', '71'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
