%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7OElumECtY

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:40 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 205 expanded)
%              Number of leaves         :   63 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  982 (1895 expanded)
%              Number of equality atoms :  102 ( 170 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k8_relset_1 @ X46 @ X47 @ X48 @ X47 )
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('2',plain,
    ( ( k8_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ sk_B )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k8_relset_1 @ X43 @ X44 @ X42 @ X45 )
        = ( k10_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ( X51
        = ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ~ ( zip_tseitin_1 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('11',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_0 @ X54 @ X55 )
      | ( zip_tseitin_1 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','5','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29
        = ( k7_relat_1 @ X29 @ X30 ) )
      | ~ ( v4_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
      | ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( ( k7_relat_1 @ X28 @ X27 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('32',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t168_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X32 @ ( k1_tarski @ X31 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t168_funct_1])).

thf('34',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['38','43'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('45',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ X24 @ X25 )
        = ( k10_relat_1 @ X24 @ ( k3_xboole_0 @ ( k2_relat_1 @ X24 ) @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ X24 @ X25 )
        = ( k10_relat_1 @ X24 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X24 ) @ X25 ) ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = ( k10_relat_1 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('51',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('56',plain,(
    ! [X26: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k2_relat_1 @ X26 ) )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('57',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('59',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('60',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','54','62','63'])).

thf('65',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['17','44','64'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 != X18 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X18 ) )
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('67',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X18 ) )
     != ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X18 ) )
     != ( k1_tarski @ X18 ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('72',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('73',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('75',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('80',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X18: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X18 ) ) ),
    inference(demod,[status(thm)],['71','81'])).

thf('83',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','82'])).

thf('84',plain,(
    $false ),
    inference(simplify,[status(thm)],['83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7OElumECtY
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:42:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.72  % Solved by: fo/fo7.sh
% 0.46/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.72  % done 364 iterations in 0.265s
% 0.46/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.72  % SZS output start Refutation
% 0.46/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.72  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.72  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.72  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.72  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.72  thf(t62_funct_2, conjecture,
% 0.46/0.72    (![A:$i,B:$i,C:$i]:
% 0.46/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.72         ( m1_subset_1 @
% 0.46/0.72           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.72       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.72         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.46/0.72           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.72            ( m1_subset_1 @
% 0.46/0.72              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.72          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.72            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.46/0.72              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.46/0.72    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.46/0.72  thf('0', plain,
% 0.46/0.72      ((m1_subset_1 @ sk_C @ 
% 0.46/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf(t38_relset_1, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i]:
% 0.46/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.72       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.46/0.72         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.72  thf('1', plain,
% 0.46/0.72      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.46/0.72         (((k8_relset_1 @ X46 @ X47 @ X48 @ X47)
% 0.46/0.72            = (k1_relset_1 @ X46 @ X47 @ X48))
% 0.46/0.72          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.46/0.72      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.46/0.72  thf('2', plain,
% 0.46/0.72      (((k8_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ sk_B)
% 0.46/0.72         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.72  thf('3', plain,
% 0.46/0.72      ((m1_subset_1 @ sk_C @ 
% 0.46/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf(redefinition_k8_relset_1, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.72       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.46/0.72  thf('4', plain,
% 0.46/0.72      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.46/0.72         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.46/0.72          | ((k8_relset_1 @ X43 @ X44 @ X42 @ X45) = (k10_relat_1 @ X42 @ X45)))),
% 0.46/0.72      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.72  thf('5', plain,
% 0.46/0.72      (![X0 : $i]:
% 0.46/0.72         ((k8_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ X0)
% 0.46/0.72           = (k10_relat_1 @ sk_C @ X0))),
% 0.46/0.72      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.72  thf('6', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf(d1_funct_2, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i]:
% 0.46/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.72  thf(zf_stmt_1, axiom,
% 0.46/0.72    (![C:$i,B:$i,A:$i]:
% 0.46/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.72  thf('7', plain,
% 0.46/0.72      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.46/0.72         (~ (v1_funct_2 @ X53 @ X51 @ X52)
% 0.46/0.72          | ((X51) = (k1_relset_1 @ X51 @ X52 @ X53))
% 0.46/0.72          | ~ (zip_tseitin_1 @ X53 @ X52 @ X51))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.72  thf('8', plain,
% 0.46/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.72        | ((k1_tarski @ sk_A)
% 0.46/0.72            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.46/0.72      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.72  thf(zf_stmt_2, axiom,
% 0.46/0.72    (![B:$i,A:$i]:
% 0.46/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.72  thf('9', plain,
% 0.46/0.72      (![X49 : $i, X50 : $i]:
% 0.46/0.72         ((zip_tseitin_0 @ X49 @ X50) | ((X49) = (k1_xboole_0)))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.72  thf('10', plain,
% 0.46/0.72      ((m1_subset_1 @ sk_C @ 
% 0.46/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.72  thf(zf_stmt_5, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i]:
% 0.46/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.72  thf('11', plain,
% 0.46/0.72      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.46/0.72         (~ (zip_tseitin_0 @ X54 @ X55)
% 0.46/0.72          | (zip_tseitin_1 @ X56 @ X54 @ X55)
% 0.46/0.72          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.72  thf('12', plain,
% 0.46/0.72      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.72        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.72  thf('13', plain,
% 0.46/0.72      ((((sk_B) = (k1_xboole_0))
% 0.46/0.72        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.72      inference('sup-', [status(thm)], ['9', '12'])).
% 0.46/0.72  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf('15', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.46/0.72      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.46/0.72  thf('16', plain,
% 0.46/0.72      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.72      inference('demod', [status(thm)], ['8', '15'])).
% 0.46/0.72  thf('17', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.72      inference('demod', [status(thm)], ['2', '5', '16'])).
% 0.46/0.72  thf('18', plain,
% 0.46/0.72      ((m1_subset_1 @ sk_C @ 
% 0.46/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf(cc2_relset_1, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i]:
% 0.46/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.72  thf('19', plain,
% 0.46/0.72      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.72         ((v4_relat_1 @ X36 @ X37)
% 0.46/0.72          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.46/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.72  thf('20', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.46/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.72  thf(t209_relat_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.72       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.46/0.72  thf('21', plain,
% 0.46/0.72      (![X29 : $i, X30 : $i]:
% 0.46/0.72         (((X29) = (k7_relat_1 @ X29 @ X30))
% 0.46/0.72          | ~ (v4_relat_1 @ X29 @ X30)
% 0.46/0.72          | ~ (v1_relat_1 @ X29))),
% 0.46/0.72      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.72  thf('22', plain,
% 0.46/0.72      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.72        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.46/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.72  thf('23', plain,
% 0.46/0.72      ((m1_subset_1 @ sk_C @ 
% 0.46/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf(cc1_relset_1, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i]:
% 0.46/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.72       ( v1_relat_1 @ C ) ))).
% 0.46/0.72  thf('24', plain,
% 0.46/0.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.46/0.72         ((v1_relat_1 @ X33)
% 0.46/0.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.46/0.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.72  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.72  thf('26', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.46/0.72      inference('demod', [status(thm)], ['22', '25'])).
% 0.46/0.72  thf(l27_zfmisc_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.46/0.72  thf('27', plain,
% 0.46/0.72      (![X16 : $i, X17 : $i]:
% 0.46/0.72         ((r1_xboole_0 @ (k1_tarski @ X16) @ X17) | (r2_hidden @ X16 @ X17))),
% 0.46/0.72      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.46/0.72  thf(t187_relat_1, axiom,
% 0.46/0.72    (![A:$i]:
% 0.46/0.72     ( ( v1_relat_1 @ A ) =>
% 0.46/0.72       ( ![B:$i]:
% 0.46/0.72         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.46/0.72           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.46/0.72  thf('28', plain,
% 0.46/0.72      (![X27 : $i, X28 : $i]:
% 0.46/0.72         (~ (r1_xboole_0 @ X27 @ (k1_relat_1 @ X28))
% 0.46/0.72          | ((k7_relat_1 @ X28 @ X27) = (k1_xboole_0))
% 0.46/0.72          | ~ (v1_relat_1 @ X28))),
% 0.46/0.72      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.46/0.72  thf('29', plain,
% 0.46/0.72      (![X0 : $i, X1 : $i]:
% 0.46/0.72         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.46/0.72          | ~ (v1_relat_1 @ X0)
% 0.46/0.72          | ((k7_relat_1 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.46/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.72  thf('30', plain,
% 0.46/0.72      ((((sk_C) = (k1_xboole_0))
% 0.46/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.72        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.46/0.72      inference('sup+', [status(thm)], ['26', '29'])).
% 0.46/0.72  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.72  thf('32', plain,
% 0.46/0.72      ((((sk_C) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.46/0.72      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.72  thf(t168_funct_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.72       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.46/0.72         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.46/0.72           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.46/0.72  thf('33', plain,
% 0.46/0.72      (![X31 : $i, X32 : $i]:
% 0.46/0.72         (~ (r2_hidden @ X31 @ (k1_relat_1 @ X32))
% 0.46/0.72          | ((k2_relat_1 @ (k7_relat_1 @ X32 @ (k1_tarski @ X31)))
% 0.46/0.72              = (k1_tarski @ (k1_funct_1 @ X32 @ X31)))
% 0.46/0.72          | ~ (v1_funct_1 @ X32)
% 0.46/0.72          | ~ (v1_relat_1 @ X32))),
% 0.46/0.72      inference('cnf', [status(esa)], [t168_funct_1])).
% 0.46/0.72  thf('34', plain,
% 0.46/0.72      ((((sk_C) = (k1_xboole_0))
% 0.46/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.72        | ((k2_relat_1 @ (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.46/0.72            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.46/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.72  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.72  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf('37', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.46/0.72      inference('demod', [status(thm)], ['22', '25'])).
% 0.46/0.72  thf('38', plain,
% 0.46/0.72      ((((sk_C) = (k1_xboole_0))
% 0.46/0.72        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.46/0.72      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.46/0.72  thf('39', plain,
% 0.46/0.72      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.46/0.72         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf('40', plain,
% 0.46/0.72      ((m1_subset_1 @ sk_C @ 
% 0.46/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i]:
% 0.46/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.72  thf('41', plain,
% 0.46/0.72      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.46/0.72         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 0.46/0.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.46/0.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.72  thf('42', plain,
% 0.46/0.72      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.46/0.72      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.72  thf('43', plain,
% 0.46/0.72      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.46/0.72      inference('demod', [status(thm)], ['39', '42'])).
% 0.46/0.72  thf('44', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.72      inference('simplify_reflect-', [status(thm)], ['38', '43'])).
% 0.46/0.72  thf(t60_relat_1, axiom,
% 0.46/0.72    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.46/0.72     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.72  thf('45', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.72  thf(t168_relat_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( v1_relat_1 @ B ) =>
% 0.46/0.72       ( ( k10_relat_1 @ B @ A ) =
% 0.46/0.72         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.46/0.72  thf('46', plain,
% 0.46/0.72      (![X24 : $i, X25 : $i]:
% 0.46/0.72         (((k10_relat_1 @ X24 @ X25)
% 0.46/0.72            = (k10_relat_1 @ X24 @ (k3_xboole_0 @ (k2_relat_1 @ X24) @ X25)))
% 0.46/0.72          | ~ (v1_relat_1 @ X24))),
% 0.46/0.72      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.46/0.72  thf(t12_setfam_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.72  thf('47', plain,
% 0.46/0.72      (![X21 : $i, X22 : $i]:
% 0.46/0.72         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 0.46/0.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.72  thf('48', plain,
% 0.46/0.72      (![X24 : $i, X25 : $i]:
% 0.46/0.72         (((k10_relat_1 @ X24 @ X25)
% 0.46/0.72            = (k10_relat_1 @ X24 @ 
% 0.46/0.72               (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X24) @ X25))))
% 0.46/0.72          | ~ (v1_relat_1 @ X24))),
% 0.46/0.72      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.72  thf('49', plain,
% 0.46/0.72      (![X0 : $i]:
% 0.46/0.72         (((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.46/0.72            = (k10_relat_1 @ k1_xboole_0 @ 
% 0.46/0.72               (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))))
% 0.46/0.72          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.46/0.72      inference('sup+', [status(thm)], ['45', '48'])).
% 0.46/0.72  thf(t17_xboole_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.72  thf('50', plain,
% 0.46/0.72      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.46/0.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.72  thf(t3_xboole_1, axiom,
% 0.46/0.72    (![A:$i]:
% 0.46/0.72     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.72  thf('51', plain,
% 0.46/0.72      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 0.46/0.72      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.72  thf('52', plain,
% 0.46/0.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.72      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.72  thf('53', plain,
% 0.46/0.72      (![X21 : $i, X22 : $i]:
% 0.46/0.72         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 0.46/0.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.72  thf('54', plain,
% 0.46/0.72      (![X0 : $i]:
% 0.46/0.72         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.46/0.72      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.72  thf('55', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.72  thf(t169_relat_1, axiom,
% 0.46/0.72    (![A:$i]:
% 0.46/0.72     ( ( v1_relat_1 @ A ) =>
% 0.46/0.72       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.46/0.72  thf('56', plain,
% 0.46/0.72      (![X26 : $i]:
% 0.46/0.72         (((k10_relat_1 @ X26 @ (k2_relat_1 @ X26)) = (k1_relat_1 @ X26))
% 0.46/0.72          | ~ (v1_relat_1 @ X26))),
% 0.46/0.72      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.46/0.72  thf('57', plain,
% 0.46/0.72      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.72        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.46/0.72      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.72  thf('58', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.72  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.46/0.72  thf('59', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.72      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.46/0.72  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.46/0.72  thf('60', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.46/0.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.72  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.72      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.72  thf('62', plain,
% 0.46/0.72      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.72      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.46/0.72  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.72      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.72  thf('64', plain,
% 0.46/0.72      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.72      inference('demod', [status(thm)], ['49', '54', '62', '63'])).
% 0.46/0.72  thf('65', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.46/0.72      inference('demod', [status(thm)], ['17', '44', '64'])).
% 0.46/0.72  thf(t20_zfmisc_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.72         ( k1_tarski @ A ) ) <=>
% 0.46/0.72       ( ( A ) != ( B ) ) ))).
% 0.46/0.72  thf('66', plain,
% 0.46/0.72      (![X18 : $i, X19 : $i]:
% 0.46/0.72         (((X19) != (X18))
% 0.46/0.72          | ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X18))
% 0.46/0.72              != (k1_tarski @ X19)))),
% 0.46/0.72      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.46/0.72  thf('67', plain,
% 0.46/0.72      (![X18 : $i]:
% 0.46/0.72         ((k4_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X18))
% 0.46/0.72           != (k1_tarski @ X18))),
% 0.46/0.72      inference('simplify', [status(thm)], ['66'])).
% 0.46/0.72  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.72  thf('68', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.72      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.72  thf(t100_xboole_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.72  thf('69', plain,
% 0.46/0.72      (![X1 : $i, X2 : $i]:
% 0.46/0.72         ((k4_xboole_0 @ X1 @ X2)
% 0.46/0.72           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.72  thf('70', plain,
% 0.46/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.72      inference('sup+', [status(thm)], ['68', '69'])).
% 0.46/0.72  thf('71', plain,
% 0.46/0.72      (![X18 : $i]:
% 0.46/0.72         ((k5_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X18))
% 0.46/0.72           != (k1_tarski @ X18))),
% 0.46/0.72      inference('demod', [status(thm)], ['67', '70'])).
% 0.46/0.72  thf(t2_boole, axiom,
% 0.46/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.72  thf('72', plain,
% 0.46/0.72      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.72  thf('73', plain,
% 0.46/0.72      (![X1 : $i, X2 : $i]:
% 0.46/0.72         ((k4_xboole_0 @ X1 @ X2)
% 0.46/0.72           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.72  thf('74', plain,
% 0.46/0.72      (![X0 : $i]:
% 0.46/0.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.72      inference('sup+', [status(thm)], ['72', '73'])).
% 0.46/0.72  thf(t5_boole, axiom,
% 0.46/0.72    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.72  thf('75', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.72      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.72  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.72      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.72  thf(t48_xboole_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.72  thf('77', plain,
% 0.46/0.72      (![X7 : $i, X8 : $i]:
% 0.46/0.72         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.46/0.72           = (k3_xboole_0 @ X7 @ X8))),
% 0.46/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.72  thf('78', plain,
% 0.46/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.72      inference('sup+', [status(thm)], ['76', '77'])).
% 0.46/0.72  thf('79', plain,
% 0.46/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.72      inference('sup+', [status(thm)], ['68', '69'])).
% 0.46/0.72  thf('80', plain,
% 0.46/0.72      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.72  thf('81', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.72      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.46/0.72  thf('82', plain, (![X18 : $i]: ((k1_xboole_0) != (k1_tarski @ X18))),
% 0.46/0.72      inference('demod', [status(thm)], ['71', '81'])).
% 0.46/0.72  thf('83', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.72      inference('sup-', [status(thm)], ['65', '82'])).
% 0.46/0.72  thf('84', plain, ($false), inference('simplify', [status(thm)], ['83'])).
% 0.46/0.72  
% 0.46/0.72  % SZS output end Refutation
% 0.46/0.72  
% 0.56/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
