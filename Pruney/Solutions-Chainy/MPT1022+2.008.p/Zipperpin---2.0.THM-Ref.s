%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uZlaXCD3s2

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:25 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 184 expanded)
%              Number of leaves         :   42 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  930 (3032 expanded)
%              Number of equality atoms :   65 ( 167 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t92_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ A )
        & ( v3_funct_2 @ C @ A @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r1_tarski @ B @ A )
       => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
            = B )
          & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
            = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ A )
          & ( v3_funct_2 @ C @ A @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r1_tarski @ B @ A )
         => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
              = B )
            & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
              = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t92_funct_2])).

thf('0',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
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

thf('2',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ( X48
        = ( k1_relset_1 @ X48 @ X49 @ X50 ) )
      | ~ ( zip_tseitin_1 @ X50 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X51 @ X52 )
      | ( zip_tseitin_1 @ X53 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('8',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( X47 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('9',plain,(
    ! [X46: $i] :
      ( zip_tseitin_0 @ X46 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k1_relat_1 @ X26 ) )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k10_relat_1 @ X26 @ ( k9_relat_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('26',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v3_funct_2 @ X43 @ X44 @ X45 )
      | ( v2_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('27',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ~ ( v3_funct_2 @ sk_C_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['18','23','24','30'])).

thf('32',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('34',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k8_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k10_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('40',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('45',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('47',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v3_funct_2 @ X43 @ X44 @ X45 )
      | ( v2_funct_2 @ X43 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('50',plain,
    ( ( v2_funct_2 @ sk_C_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_C_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_2 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('54',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v2_funct_2 @ X55 @ X54 )
      | ( ( k2_relat_1 @ X55 )
        = X54 )
      | ~ ( v5_relat_1 @ X55 @ X54 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v5_relat_1 @ sk_C_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v5_relat_1 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['55','56','59'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('61',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( k2_relat_1 @ X24 ) )
      | ( ( k9_relat_1 @ X24 @ ( k10_relat_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['47','65'])).

thf('67',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['45','46','66'])).

thf('68',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('70',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['42','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uZlaXCD3s2
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 288 iterations in 0.283s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.55/0.74  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.55/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.74  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.55/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.74  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.55/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.55/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.55/0.74  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.55/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.55/0.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(t92_funct_2, conjecture,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.55/0.74         ( v3_funct_2 @ C @ A @ A ) & 
% 0.55/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.74       ( ( r1_tarski @ B @ A ) =>
% 0.55/0.74         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.55/0.74             ( B ) ) & 
% 0.55/0.74           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.55/0.74             ( B ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.74        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.55/0.74            ( v3_funct_2 @ C @ A @ A ) & 
% 0.55/0.74            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.74          ( ( r1_tarski @ B @ A ) =>
% 0.55/0.74            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.55/0.74                ( B ) ) & 
% 0.55/0.74              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.55/0.74                ( B ) ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.55/0.74  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('1', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(d1_funct_2, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.55/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.55/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.55/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_1, axiom,
% 0.55/0.74    (![C:$i,B:$i,A:$i]:
% 0.55/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.55/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.55/0.74         (~ (v1_funct_2 @ X50 @ X48 @ X49)
% 0.55/0.74          | ((X48) = (k1_relset_1 @ X48 @ X49 @ X50))
% 0.55/0.74          | ~ (zip_tseitin_1 @ X50 @ X49 @ X48))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.55/0.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_C_1)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.55/0.74  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.55/0.74  thf(zf_stmt_4, axiom,
% 0.55/0.74    (![B:$i,A:$i]:
% 0.55/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.55/0.74  thf(zf_stmt_5, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.55/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.55/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.55/0.74         (~ (zip_tseitin_0 @ X51 @ X52)
% 0.55/0.74          | (zip_tseitin_1 @ X53 @ X51 @ X52)
% 0.55/0.74          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.55/0.74        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X46 : $i, X47 : $i]:
% 0.55/0.74         ((zip_tseitin_0 @ X46 @ X47) | ((X46) = (k1_xboole_0)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (![X46 : $i, X47 : $i]:
% 0.55/0.74         ((zip_tseitin_0 @ X46 @ X47) | ((X47) != (k1_xboole_0)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.55/0.74  thf('9', plain, (![X46 : $i]: (zip_tseitin_0 @ X46 @ k1_xboole_0)),
% 0.55/0.74      inference('simplify', [status(thm)], ['8'])).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.55/0.74      inference('sup+', [status(thm)], ['7', '9'])).
% 0.55/0.74  thf('11', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.55/0.74      inference('eq_fact', [status(thm)], ['10'])).
% 0.55/0.74  thf('12', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['6', '11'])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.55/0.74         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.55/0.74          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.74  thf('16', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.55/0.74      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.55/0.74  thf(t164_funct_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.74       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.55/0.74         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      (![X25 : $i, X26 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X25 @ (k1_relat_1 @ X26))
% 0.55/0.74          | ~ (v2_funct_1 @ X26)
% 0.55/0.74          | ((k10_relat_1 @ X26 @ (k9_relat_1 @ X26 @ X25)) = (X25))
% 0.55/0.74          | ~ (v1_funct_1 @ X26)
% 0.55/0.74          | ~ (v1_relat_1 @ X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.55/0.74          | ~ (v1_relat_1 @ sk_C_1)
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C_1)
% 0.55/0.74          | ((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ X0)) = (X0))
% 0.55/0.74          | ~ (v2_funct_1 @ sk_C_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(cc2_relat_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (![X10 : $i, X11 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.55/0.74          | (v1_relat_1 @ X10)
% 0.55/0.74          | ~ (v1_relat_1 @ X11))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.55/0.74  thf(fc6_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.74  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.55/0.74      inference('demod', [status(thm)], ['21', '22'])).
% 0.55/0.74  thf('24', plain, ((v1_funct_1 @ sk_C_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(cc2_funct_2, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.55/0.74         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.55/0.74  thf('26', plain,
% 0.55/0.74      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.55/0.74         (~ (v1_funct_1 @ X43)
% 0.55/0.74          | ~ (v3_funct_2 @ X43 @ X44 @ X45)
% 0.55/0.74          | (v2_funct_1 @ X43)
% 0.55/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      (((v2_funct_1 @ sk_C_1)
% 0.55/0.74        | ~ (v3_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 0.55/0.74        | ~ (v1_funct_1 @ sk_C_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['25', '26'])).
% 0.55/0.74  thf('28', plain, ((v3_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('29', plain, ((v1_funct_1 @ sk_C_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('30', plain, ((v2_funct_1 @ sk_C_1)),
% 0.55/0.74      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.55/0.74  thf('31', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.55/0.74          | ((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['18', '23', '24', '30'])).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      (((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_B)) = (sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['0', '31'])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(redefinition_k8_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.55/0.74          | ((k8_relset_1 @ X40 @ X41 @ X39 @ X42) = (k10_relat_1 @ X39 @ X42)))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ X0)
% 0.55/0.74           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) != (sk_B))
% 0.55/0.74        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74            (k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) != (sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74          (k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) != (sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74                (k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B))))),
% 0.55/0.74      inference('split', [status(esa)], ['36'])).
% 0.55/0.74  thf('38', plain,
% 0.55/0.74      ((((k10_relat_1 @ sk_C_1 @ (k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B))
% 0.55/0.74          != (sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74                (k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['35', '37'])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(redefinition_k7_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.55/0.74          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ X0)
% 0.55/0.74           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      ((((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_B)) != (sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74                (k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B))))),
% 0.55/0.74      inference('demod', [status(thm)], ['38', '41'])).
% 0.55/0.74  thf('43', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ X0)
% 0.55/0.74           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) != (sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B))))),
% 0.55/0.74      inference('split', [status(esa)], ['36'])).
% 0.55/0.74  thf('45', plain,
% 0.55/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_B))
% 0.55/0.74          != (sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['43', '44'])).
% 0.55/0.74  thf('46', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ X0)
% 0.55/0.74           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.74  thf('47', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('48', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('49', plain,
% 0.55/0.74      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.55/0.74         (~ (v1_funct_1 @ X43)
% 0.55/0.74          | ~ (v3_funct_2 @ X43 @ X44 @ X45)
% 0.55/0.74          | (v2_funct_2 @ X43 @ X45)
% 0.55/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.55/0.74  thf('50', plain,
% 0.55/0.74      (((v2_funct_2 @ sk_C_1 @ sk_A)
% 0.55/0.74        | ~ (v3_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 0.55/0.74        | ~ (v1_funct_1 @ sk_C_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['48', '49'])).
% 0.55/0.74  thf('51', plain, ((v3_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('53', plain, ((v2_funct_2 @ sk_C_1 @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.55/0.74  thf(d3_funct_2, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.55/0.74       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.55/0.74  thf('54', plain,
% 0.55/0.74      (![X54 : $i, X55 : $i]:
% 0.55/0.74         (~ (v2_funct_2 @ X55 @ X54)
% 0.55/0.74          | ((k2_relat_1 @ X55) = (X54))
% 0.55/0.74          | ~ (v5_relat_1 @ X55 @ X54)
% 0.55/0.74          | ~ (v1_relat_1 @ X55))),
% 0.55/0.74      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.55/0.74  thf('55', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ sk_C_1)
% 0.55/0.74        | ~ (v5_relat_1 @ sk_C_1 @ sk_A)
% 0.55/0.74        | ((k2_relat_1 @ sk_C_1) = (sk_A)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.55/0.74  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 0.55/0.74      inference('demod', [status(thm)], ['21', '22'])).
% 0.55/0.74  thf('57', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(cc2_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.74  thf('58', plain,
% 0.55/0.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.55/0.74         ((v5_relat_1 @ X29 @ X31)
% 0.55/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.74  thf('59', plain, ((v5_relat_1 @ sk_C_1 @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['57', '58'])).
% 0.55/0.74  thf('60', plain, (((k2_relat_1 @ sk_C_1) = (sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['55', '56', '59'])).
% 0.55/0.74  thf(t147_funct_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.74       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.55/0.74         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.55/0.74  thf('61', plain,
% 0.55/0.74      (![X23 : $i, X24 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X23 @ (k2_relat_1 @ X24))
% 0.55/0.74          | ((k9_relat_1 @ X24 @ (k10_relat_1 @ X24 @ X23)) = (X23))
% 0.55/0.74          | ~ (v1_funct_1 @ X24)
% 0.55/0.74          | ~ (v1_relat_1 @ X24))),
% 0.55/0.74      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.55/0.74  thf('62', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.55/0.74          | ~ (v1_relat_1 @ sk_C_1)
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C_1)
% 0.55/0.74          | ((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['60', '61'])).
% 0.55/0.74  thf('63', plain, ((v1_relat_1 @ sk_C_1)),
% 0.55/0.74      inference('demod', [status(thm)], ['21', '22'])).
% 0.55/0.74  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('65', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.55/0.74          | ((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.55/0.74  thf('66', plain,
% 0.55/0.74      (((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_B)) = (sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['47', '65'])).
% 0.55/0.74  thf('67', plain,
% 0.55/0.74      ((((sk_B) != (sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B))))),
% 0.55/0.74      inference('demod', [status(thm)], ['45', '46', '66'])).
% 0.55/0.74  thf('68', plain,
% 0.55/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['67'])).
% 0.55/0.74  thf('69', plain,
% 0.55/0.74      (~
% 0.55/0.74       (((k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74          (k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B))) | 
% 0.55/0.74       ~
% 0.55/0.74       (((k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B)))),
% 0.55/0.74      inference('split', [status(esa)], ['36'])).
% 0.55/0.74  thf('70', plain,
% 0.55/0.74      (~
% 0.55/0.74       (((k8_relset_1 @ sk_A @ sk_A @ sk_C_1 @ 
% 0.55/0.74          (k7_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_B)) = (sk_B)))),
% 0.55/0.74      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.55/0.74  thf('71', plain,
% 0.55/0.74      (((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_B)) != (sk_B))),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['42', '70'])).
% 0.55/0.74  thf('72', plain, ($false),
% 0.55/0.74      inference('simplify_reflect-', [status(thm)], ['32', '71'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
