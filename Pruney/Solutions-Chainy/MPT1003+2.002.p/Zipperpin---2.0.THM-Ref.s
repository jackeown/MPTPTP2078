%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QcAWtFQm85

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:02 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  191 (9384 expanded)
%              Number of leaves         :   42 (2750 expanded)
%              Depth                    :   30
%              Number of atoms          : 1442 (114163 expanded)
%              Number of equality atoms :  155 (12115 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t51_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('10',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('18',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X37: $i] :
      ( zip_tseitin_0 @ X37 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','36'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','41'])).

thf('43',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('46',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k8_relset_1 @ X34 @ X35 @ X36 @ X35 )
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('49',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('60',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relset_1 @ X2 @ X0 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('68',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('72',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['0','3'])).

thf('73',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('78',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','79'])).

thf('81',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','80'])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['57','81'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','82'])).

thf('84',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('85',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','85'])).

thf('87',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['20','86'])).

thf('88',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['15','87'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['89'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X48 ) @ X49 )
      | ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ X49 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['88','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('96',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['93','94','97'])).

thf('99',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['93','94','97'])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('104',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X47 ) ) )
      | ( ( k8_relset_1 @ X45 @ X47 @ X46 @ X47 )
        = X45 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('105',plain,
    ( ( ( k8_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['15','87'])).

thf('107',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('108',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X48 ) @ X49 )
      | ( v1_funct_2 @ X48 @ ( k1_relat_1 @ X48 ) @ X49 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( k8_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['93','94','97'])).

thf('117',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['89'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('121',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k2_relat_1 @ X15 ) )
      | ( ( k9_relat_1 @ X15 @ ( k10_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['119','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('126',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('128',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('132',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('134',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['128','129'])).

thf('137',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['131'])).

thf('138',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['102','130','132','135','136','137'])).

thf('139',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['102','130','132','135','136','137'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('142',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != sk_A ),
    inference(demod,[status(thm)],['8','138','139','140','141'])).

thf('143',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['15','87'])).

thf('144',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['102','130','132','135','136','137'])).

thf('145',plain,
    ( sk_A
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['142','145'])).

thf('147',plain,(
    $false ),
    inference(simplify,[status(thm)],['146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QcAWtFQm85
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:50:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.05/1.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.29  % Solved by: fo/fo7.sh
% 1.05/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.29  % done 1276 iterations in 0.846s
% 1.05/1.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.29  % SZS output start Refutation
% 1.05/1.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.05/1.29  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.05/1.29  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.05/1.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.29  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.05/1.29  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.29  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.05/1.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.05/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.29  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.05/1.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.29  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.05/1.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.29  thf(t51_funct_2, conjecture,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.29         ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 1.05/1.29           ( A ) ) ) ))).
% 1.05/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.29    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.29        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.29            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.29            ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 1.05/1.29              ( A ) ) ) ) )),
% 1.05/1.29    inference('cnf.neg', [status(esa)], [t51_funct_2])).
% 1.05/1.29  thf('0', plain,
% 1.05/1.29      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 1.05/1.29         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('1', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(redefinition_k7_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.05/1.29  thf('2', plain,
% 1.05/1.29      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.05/1.29          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.05/1.29  thf('3', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.05/1.29      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.29  thf('4', plain,
% 1.05/1.29      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))
% 1.05/1.29         != (sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['0', '3'])).
% 1.05/1.29  thf('5', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(redefinition_k8_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.05/1.29  thf('6', plain,
% 1.05/1.29      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.05/1.29          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.05/1.29  thf('7', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.05/1.29      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.29  thf('8', plain,
% 1.05/1.29      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) != (sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['4', '7'])).
% 1.05/1.29  thf('9', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(d1_funct_2, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.29           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.05/1.29             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.05/1.29         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.29           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.05/1.29             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.05/1.29  thf(zf_stmt_1, axiom,
% 1.05/1.29    (![C:$i,B:$i,A:$i]:
% 1.05/1.29     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.05/1.29       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.05/1.29  thf('10', plain,
% 1.05/1.29      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.05/1.29         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 1.05/1.29          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 1.05/1.29          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.29  thf('11', plain,
% 1.05/1.29      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.05/1.29        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['9', '10'])).
% 1.05/1.29  thf('12', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(redefinition_k1_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.05/1.29  thf('13', plain,
% 1.05/1.29      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.05/1.29         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.05/1.29          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.05/1.29  thf('14', plain,
% 1.05/1.29      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.05/1.29      inference('sup-', [status(thm)], ['12', '13'])).
% 1.05/1.29  thf('15', plain,
% 1.05/1.29      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.05/1.29      inference('demod', [status(thm)], ['11', '14'])).
% 1.05/1.29  thf(zf_stmt_2, axiom,
% 1.05/1.29    (![B:$i,A:$i]:
% 1.05/1.29     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.29       ( zip_tseitin_0 @ B @ A ) ))).
% 1.05/1.29  thf('16', plain,
% 1.05/1.29      (![X37 : $i, X38 : $i]:
% 1.05/1.29         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.05/1.29  thf('17', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.05/1.29  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.05/1.29  thf(zf_stmt_5, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.05/1.29         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.29           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.05/1.29             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.05/1.29  thf('18', plain,
% 1.05/1.29      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.05/1.29         (~ (zip_tseitin_0 @ X42 @ X43)
% 1.05/1.29          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 1.05/1.29          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.29  thf('19', plain,
% 1.05/1.29      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.05/1.29      inference('sup-', [status(thm)], ['17', '18'])).
% 1.05/1.29  thf('20', plain,
% 1.05/1.29      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.05/1.29      inference('sup-', [status(thm)], ['16', '19'])).
% 1.05/1.29  thf('21', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('22', plain,
% 1.05/1.29      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.05/1.29      inference('split', [status(esa)], ['21'])).
% 1.05/1.29  thf('23', plain,
% 1.05/1.29      (![X37 : $i, X38 : $i]:
% 1.05/1.29         ((zip_tseitin_0 @ X37 @ X38) | ((X38) != (k1_xboole_0)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.05/1.29  thf('24', plain, (![X37 : $i]: (zip_tseitin_0 @ X37 @ k1_xboole_0)),
% 1.05/1.29      inference('simplify', [status(thm)], ['23'])).
% 1.05/1.29  thf(t4_subset_1, axiom,
% 1.05/1.29    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.05/1.29  thf('25', plain,
% 1.05/1.29      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.05/1.29      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.29  thf('26', plain,
% 1.05/1.29      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.05/1.29         (~ (zip_tseitin_0 @ X42 @ X43)
% 1.05/1.29          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 1.05/1.29          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.29  thf('27', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.05/1.29      inference('sup-', [status(thm)], ['25', '26'])).
% 1.05/1.29  thf('28', plain,
% 1.05/1.29      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.05/1.29      inference('sup-', [status(thm)], ['24', '27'])).
% 1.05/1.29  thf('29', plain,
% 1.05/1.29      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('split', [status(esa)], ['21'])).
% 1.05/1.29  thf('30', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('31', plain,
% 1.05/1.29      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup+', [status(thm)], ['29', '30'])).
% 1.05/1.29  thf('32', plain,
% 1.05/1.29      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('split', [status(esa)], ['21'])).
% 1.05/1.29  thf('33', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('34', plain,
% 1.05/1.29      (((m1_subset_1 @ sk_C @ 
% 1.05/1.29         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup+', [status(thm)], ['32', '33'])).
% 1.05/1.29  thf(t113_zfmisc_1, axiom,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.05/1.29       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.05/1.29  thf('35', plain,
% 1.05/1.29      (![X5 : $i, X6 : $i]:
% 1.05/1.29         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.05/1.29      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.05/1.29  thf('36', plain,
% 1.05/1.29      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.05/1.29      inference('simplify', [status(thm)], ['35'])).
% 1.05/1.29  thf('37', plain,
% 1.05/1.29      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('demod', [status(thm)], ['34', '36'])).
% 1.05/1.29  thf(t3_subset, axiom,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.05/1.29  thf('38', plain,
% 1.05/1.29      (![X8 : $i, X9 : $i]:
% 1.05/1.29         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.05/1.29      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.29  thf('39', plain,
% 1.05/1.29      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['37', '38'])).
% 1.05/1.29  thf(t3_xboole_1, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.29  thf('40', plain,
% 1.05/1.29      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 1.05/1.29      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.05/1.29  thf('41', plain,
% 1.05/1.29      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.29  thf('42', plain,
% 1.05/1.29      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('demod', [status(thm)], ['31', '41'])).
% 1.05/1.29  thf('43', plain,
% 1.05/1.29      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.05/1.29         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 1.05/1.29          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 1.05/1.29          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.29  thf('44', plain,
% 1.05/1.29      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 1.05/1.29         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0))))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['42', '43'])).
% 1.05/1.29  thf('45', plain,
% 1.05/1.29      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.05/1.29      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.29  thf(t38_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.05/1.29         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.05/1.29  thf('46', plain,
% 1.05/1.29      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.05/1.29         (((k8_relset_1 @ X34 @ X35 @ X36 @ X35)
% 1.05/1.29            = (k1_relset_1 @ X34 @ X35 @ X36))
% 1.05/1.29          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.05/1.29      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.05/1.29  thf('47', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 1.05/1.29           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.05/1.29      inference('sup-', [status(thm)], ['45', '46'])).
% 1.05/1.29  thf('48', plain,
% 1.05/1.29      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.05/1.29      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.29  thf('49', plain,
% 1.05/1.29      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.05/1.29          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.05/1.29  thf('50', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 1.05/1.29           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 1.05/1.29      inference('sup-', [status(thm)], ['48', '49'])).
% 1.05/1.29  thf('51', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k10_relat_1 @ k1_xboole_0 @ X0)
% 1.05/1.29           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.05/1.29      inference('demod', [status(thm)], ['47', '50'])).
% 1.05/1.29  thf('52', plain,
% 1.05/1.29      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.05/1.29      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.29  thf('53', plain,
% 1.05/1.29      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.05/1.29         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.05/1.29          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.05/1.29  thf('54', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.05/1.29      inference('sup-', [status(thm)], ['52', '53'])).
% 1.05/1.29  thf('55', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k10_relat_1 @ k1_xboole_0 @ X0)
% 1.05/1.29           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.05/1.29      inference('demod', [status(thm)], ['47', '50'])).
% 1.05/1.29  thf('56', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_relat_1 @ k1_xboole_0))),
% 1.05/1.29      inference('demod', [status(thm)], ['54', '55'])).
% 1.05/1.29  thf('57', plain,
% 1.05/1.29      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 1.05/1.29         | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('demod', [status(thm)], ['44', '51', '56'])).
% 1.05/1.29  thf('58', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_relat_1 @ k1_xboole_0))),
% 1.05/1.29      inference('demod', [status(thm)], ['54', '55'])).
% 1.05/1.29  thf('59', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 1.05/1.29           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 1.05/1.29      inference('sup-', [status(thm)], ['48', '49'])).
% 1.05/1.29  thf('60', plain,
% 1.05/1.29      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.05/1.29      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.29  thf(dt_k7_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.05/1.29  thf('61', plain,
% 1.05/1.29      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.05/1.29          | (m1_subset_1 @ (k7_relset_1 @ X20 @ X21 @ X19 @ X22) @ 
% 1.05/1.29             (k1_zfmisc_1 @ X21)))),
% 1.05/1.29      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.05/1.29  thf('62', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         (m1_subset_1 @ (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 1.05/1.29          (k1_zfmisc_1 @ X0))),
% 1.05/1.29      inference('sup-', [status(thm)], ['60', '61'])).
% 1.05/1.29  thf('63', plain,
% 1.05/1.29      (![X8 : $i, X9 : $i]:
% 1.05/1.29         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.05/1.29      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.29  thf('64', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         (r1_tarski @ (k7_relset_1 @ X2 @ X0 @ k1_xboole_0 @ X1) @ X0)),
% 1.05/1.29      inference('sup-', [status(thm)], ['62', '63'])).
% 1.05/1.29  thf('65', plain,
% 1.05/1.29      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 1.05/1.29      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.05/1.29  thf('66', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k7_relset_1 @ X1 @ k1_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.05/1.29      inference('sup-', [status(thm)], ['64', '65'])).
% 1.05/1.29  thf('67', plain,
% 1.05/1.29      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.05/1.29      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.29  thf('68', plain,
% 1.05/1.29      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.05/1.29          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.05/1.29  thf('69', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 1.05/1.29           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 1.05/1.29      inference('sup-', [status(thm)], ['67', '68'])).
% 1.05/1.29  thf('70', plain,
% 1.05/1.29      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.05/1.29      inference('demod', [status(thm)], ['66', '69'])).
% 1.05/1.29  thf('71', plain,
% 1.05/1.29      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('split', [status(esa)], ['21'])).
% 1.05/1.29  thf('72', plain,
% 1.05/1.29      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))
% 1.05/1.29         != (sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['0', '3'])).
% 1.05/1.29  thf('73', plain,
% 1.05/1.29      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))
% 1.05/1.29          != (sk_A)))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['71', '72'])).
% 1.05/1.29  thf('74', plain,
% 1.05/1.29      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.29  thf('75', plain,
% 1.05/1.29      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.29  thf('76', plain,
% 1.05/1.29      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('split', [status(esa)], ['21'])).
% 1.05/1.29  thf('77', plain,
% 1.05/1.29      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('split', [status(esa)], ['21'])).
% 1.05/1.29  thf('78', plain,
% 1.05/1.29      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ 
% 1.05/1.29          (k9_relat_1 @ k1_xboole_0 @ k1_xboole_0)) != (k1_xboole_0)))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 1.05/1.29  thf('79', plain,
% 1.05/1.29      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0)
% 1.05/1.29          != (k1_xboole_0)))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['70', '78'])).
% 1.05/1.29  thf('80', plain,
% 1.05/1.29      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['59', '79'])).
% 1.05/1.29  thf('81', plain,
% 1.05/1.29      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 1.05/1.29         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['58', '80'])).
% 1.05/1.30  thf('82', plain,
% 1.05/1.30      ((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0))
% 1.05/1.30         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.30      inference('simplify_reflect-', [status(thm)], ['57', '81'])).
% 1.05/1.30  thf('83', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 1.05/1.30      inference('sup-', [status(thm)], ['28', '82'])).
% 1.05/1.30  thf('84', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.05/1.30      inference('split', [status(esa)], ['21'])).
% 1.05/1.30  thf('85', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.05/1.30      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 1.05/1.30  thf('86', plain, (((sk_B) != (k1_xboole_0))),
% 1.05/1.30      inference('simpl_trail', [status(thm)], ['22', '85'])).
% 1.05/1.30  thf('87', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 1.05/1.30      inference('simplify_reflect-', [status(thm)], ['20', '86'])).
% 1.05/1.30  thf('88', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.05/1.30      inference('demod', [status(thm)], ['15', '87'])).
% 1.05/1.30  thf(d10_xboole_0, axiom,
% 1.05/1.30    (![A:$i,B:$i]:
% 1.05/1.30     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.05/1.30  thf('89', plain,
% 1.05/1.30      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.05/1.30      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.30  thf('90', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.05/1.30      inference('simplify', [status(thm)], ['89'])).
% 1.05/1.30  thf(t4_funct_2, axiom,
% 1.05/1.30    (![A:$i,B:$i]:
% 1.05/1.30     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.30       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.05/1.30         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.05/1.30           ( m1_subset_1 @
% 1.05/1.30             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.05/1.30  thf('91', plain,
% 1.05/1.30      (![X48 : $i, X49 : $i]:
% 1.05/1.30         (~ (r1_tarski @ (k2_relat_1 @ X48) @ X49)
% 1.05/1.30          | (m1_subset_1 @ X48 @ 
% 1.05/1.30             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ X49)))
% 1.05/1.30          | ~ (v1_funct_1 @ X48)
% 1.05/1.30          | ~ (v1_relat_1 @ X48))),
% 1.05/1.30      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.05/1.30  thf('92', plain,
% 1.05/1.30      (![X0 : $i]:
% 1.05/1.30         (~ (v1_relat_1 @ X0)
% 1.05/1.30          | ~ (v1_funct_1 @ X0)
% 1.05/1.30          | (m1_subset_1 @ X0 @ 
% 1.05/1.30             (k1_zfmisc_1 @ 
% 1.05/1.30              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.05/1.30      inference('sup-', [status(thm)], ['90', '91'])).
% 1.05/1.30  thf('93', plain,
% 1.05/1.30      (((m1_subset_1 @ sk_C @ 
% 1.05/1.30         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))
% 1.05/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.30        | ~ (v1_relat_1 @ sk_C))),
% 1.05/1.30      inference('sup+', [status(thm)], ['88', '92'])).
% 1.05/1.30  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.30  thf('95', plain,
% 1.05/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.30  thf(cc1_relset_1, axiom,
% 1.05/1.30    (![A:$i,B:$i,C:$i]:
% 1.05/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.30       ( v1_relat_1 @ C ) ))).
% 1.05/1.30  thf('96', plain,
% 1.05/1.30      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.05/1.30         ((v1_relat_1 @ X16)
% 1.05/1.30          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.05/1.30      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.30  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.30      inference('sup-', [status(thm)], ['95', '96'])).
% 1.05/1.30  thf('98', plain,
% 1.05/1.30      ((m1_subset_1 @ sk_C @ 
% 1.05/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 1.05/1.30      inference('demod', [status(thm)], ['93', '94', '97'])).
% 1.05/1.30  thf('99', plain,
% 1.05/1.30      (![X8 : $i, X9 : $i]:
% 1.05/1.30         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.05/1.30      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.30  thf('100', plain,
% 1.05/1.30      ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C)))),
% 1.05/1.30      inference('sup-', [status(thm)], ['98', '99'])).
% 1.05/1.30  thf('101', plain,
% 1.05/1.30      (![X0 : $i, X2 : $i]:
% 1.05/1.30         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.05/1.30      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.30  thf('102', plain,
% 1.05/1.30      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C)) @ sk_C)
% 1.05/1.30        | ((k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_C)))),
% 1.05/1.30      inference('sup-', [status(thm)], ['100', '101'])).
% 1.05/1.30  thf('103', plain,
% 1.05/1.30      ((m1_subset_1 @ sk_C @ 
% 1.05/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 1.05/1.30      inference('demod', [status(thm)], ['93', '94', '97'])).
% 1.05/1.30  thf(t48_funct_2, axiom,
% 1.05/1.30    (![A:$i,B:$i,C:$i]:
% 1.05/1.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.30       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.30         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 1.05/1.30  thf('104', plain,
% 1.05/1.30      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.05/1.30         (((X47) = (k1_xboole_0))
% 1.05/1.30          | ~ (v1_funct_1 @ X46)
% 1.05/1.30          | ~ (v1_funct_2 @ X46 @ X45 @ X47)
% 1.05/1.30          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X47)))
% 1.05/1.30          | ((k8_relset_1 @ X45 @ X47 @ X46 @ X47) = (X45)))),
% 1.05/1.30      inference('cnf', [status(esa)], [t48_funct_2])).
% 1.05/1.30  thf('105', plain,
% 1.05/1.30      ((((k8_relset_1 @ sk_A @ (k2_relat_1 @ sk_C) @ sk_C @ (k2_relat_1 @ sk_C))
% 1.05/1.30          = (sk_A))
% 1.05/1.30        | ~ (v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))
% 1.05/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.30        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.05/1.30      inference('sup-', [status(thm)], ['103', '104'])).
% 1.05/1.30  thf('106', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.05/1.30      inference('demod', [status(thm)], ['15', '87'])).
% 1.05/1.30  thf('107', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.05/1.30      inference('simplify', [status(thm)], ['89'])).
% 1.05/1.30  thf('108', plain,
% 1.05/1.30      (![X48 : $i, X49 : $i]:
% 1.05/1.30         (~ (r1_tarski @ (k2_relat_1 @ X48) @ X49)
% 1.05/1.30          | (v1_funct_2 @ X48 @ (k1_relat_1 @ X48) @ X49)
% 1.05/1.30          | ~ (v1_funct_1 @ X48)
% 1.05/1.30          | ~ (v1_relat_1 @ X48))),
% 1.05/1.30      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.05/1.30  thf('109', plain,
% 1.05/1.30      (![X0 : $i]:
% 1.05/1.30         (~ (v1_relat_1 @ X0)
% 1.05/1.30          | ~ (v1_funct_1 @ X0)
% 1.05/1.30          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.05/1.30      inference('sup-', [status(thm)], ['107', '108'])).
% 1.05/1.30  thf('110', plain,
% 1.05/1.30      (((v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))
% 1.05/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.30        | ~ (v1_relat_1 @ sk_C))),
% 1.05/1.30      inference('sup+', [status(thm)], ['106', '109'])).
% 1.05/1.30  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.30  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.30      inference('sup-', [status(thm)], ['95', '96'])).
% 1.05/1.30  thf('113', plain, ((v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))),
% 1.05/1.30      inference('demod', [status(thm)], ['110', '111', '112'])).
% 1.05/1.30  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.30  thf('115', plain,
% 1.05/1.30      ((((k8_relset_1 @ sk_A @ (k2_relat_1 @ sk_C) @ sk_C @ (k2_relat_1 @ sk_C))
% 1.05/1.30          = (sk_A))
% 1.05/1.30        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.05/1.30      inference('demod', [status(thm)], ['105', '113', '114'])).
% 1.05/1.30  thf('116', plain,
% 1.05/1.30      ((m1_subset_1 @ sk_C @ 
% 1.05/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 1.05/1.30      inference('demod', [status(thm)], ['93', '94', '97'])).
% 1.05/1.30  thf('117', plain,
% 1.05/1.30      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.05/1.30         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.05/1.30          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 1.05/1.30      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.05/1.30  thf('118', plain,
% 1.05/1.30      (![X0 : $i]:
% 1.05/1.30         ((k8_relset_1 @ sk_A @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 1.05/1.30           = (k10_relat_1 @ sk_C @ X0))),
% 1.05/1.30      inference('sup-', [status(thm)], ['116', '117'])).
% 1.05/1.30  thf('119', plain,
% 1.05/1.30      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (sk_A))
% 1.05/1.30        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.05/1.30      inference('demod', [status(thm)], ['115', '118'])).
% 1.05/1.30  thf('120', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.05/1.30      inference('simplify', [status(thm)], ['89'])).
% 1.05/1.30  thf(t147_funct_1, axiom,
% 1.05/1.30    (![A:$i,B:$i]:
% 1.05/1.30     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.30       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.05/1.30         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.05/1.30  thf('121', plain,
% 1.05/1.30      (![X14 : $i, X15 : $i]:
% 1.05/1.30         (~ (r1_tarski @ X14 @ (k2_relat_1 @ X15))
% 1.05/1.30          | ((k9_relat_1 @ X15 @ (k10_relat_1 @ X15 @ X14)) = (X14))
% 1.05/1.30          | ~ (v1_funct_1 @ X15)
% 1.05/1.30          | ~ (v1_relat_1 @ X15))),
% 1.05/1.30      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.05/1.30  thf('122', plain,
% 1.05/1.30      (![X0 : $i]:
% 1.05/1.30         (~ (v1_relat_1 @ X0)
% 1.05/1.30          | ~ (v1_funct_1 @ X0)
% 1.05/1.30          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.05/1.30              = (k2_relat_1 @ X0)))),
% 1.05/1.30      inference('sup-', [status(thm)], ['120', '121'])).
% 1.05/1.30  thf('123', plain,
% 1.05/1.30      ((((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 1.05/1.30        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.05/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.30        | ~ (v1_relat_1 @ sk_C))),
% 1.05/1.30      inference('sup+', [status(thm)], ['119', '122'])).
% 1.05/1.30  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.30  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.30      inference('sup-', [status(thm)], ['95', '96'])).
% 1.05/1.30  thf('126', plain,
% 1.05/1.30      ((((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 1.05/1.30        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.05/1.30      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.05/1.30  thf('127', plain,
% 1.05/1.30      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) != (sk_A))),
% 1.05/1.30      inference('demod', [status(thm)], ['4', '7'])).
% 1.05/1.30  thf('128', plain,
% 1.05/1.30      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (sk_A))
% 1.05/1.30        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.05/1.30      inference('sup-', [status(thm)], ['126', '127'])).
% 1.05/1.30  thf('129', plain,
% 1.05/1.30      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (sk_A))
% 1.05/1.30        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.05/1.30      inference('demod', [status(thm)], ['115', '118'])).
% 1.05/1.30  thf('130', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.05/1.30      inference('clc', [status(thm)], ['128', '129'])).
% 1.05/1.30  thf('131', plain,
% 1.05/1.30      (![X5 : $i, X6 : $i]:
% 1.05/1.30         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.05/1.30      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.05/1.30  thf('132', plain,
% 1.05/1.30      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.30      inference('simplify', [status(thm)], ['131'])).
% 1.05/1.30  thf('133', plain,
% 1.05/1.30      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.05/1.30      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.30  thf('134', plain,
% 1.05/1.30      (![X8 : $i, X9 : $i]:
% 1.05/1.30         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.05/1.30      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.30  thf('135', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.05/1.30      inference('sup-', [status(thm)], ['133', '134'])).
% 1.05/1.30  thf('136', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.05/1.30      inference('clc', [status(thm)], ['128', '129'])).
% 1.05/1.30  thf('137', plain,
% 1.05/1.30      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.30      inference('simplify', [status(thm)], ['131'])).
% 1.05/1.30  thf('138', plain, (((k1_xboole_0) = (sk_C))),
% 1.05/1.30      inference('demod', [status(thm)],
% 1.05/1.30                ['102', '130', '132', '135', '136', '137'])).
% 1.05/1.30  thf('139', plain, (((k1_xboole_0) = (sk_C))),
% 1.05/1.30      inference('demod', [status(thm)],
% 1.05/1.30                ['102', '130', '132', '135', '136', '137'])).
% 1.05/1.30  thf('140', plain,
% 1.05/1.30      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.05/1.30      inference('demod', [status(thm)], ['66', '69'])).
% 1.05/1.30  thf('141', plain,
% 1.05/1.30      (![X0 : $i]:
% 1.05/1.30         ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_relat_1 @ k1_xboole_0))),
% 1.05/1.30      inference('demod', [status(thm)], ['54', '55'])).
% 1.05/1.30  thf('142', plain, (((k1_relat_1 @ k1_xboole_0) != (sk_A))),
% 1.05/1.30      inference('demod', [status(thm)], ['8', '138', '139', '140', '141'])).
% 1.05/1.30  thf('143', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.05/1.30      inference('demod', [status(thm)], ['15', '87'])).
% 1.05/1.30  thf('144', plain, (((k1_xboole_0) = (sk_C))),
% 1.05/1.30      inference('demod', [status(thm)],
% 1.05/1.30                ['102', '130', '132', '135', '136', '137'])).
% 1.05/1.30  thf('145', plain, (((sk_A) = (k1_relat_1 @ k1_xboole_0))),
% 1.05/1.30      inference('demod', [status(thm)], ['143', '144'])).
% 1.05/1.30  thf('146', plain, (((sk_A) != (sk_A))),
% 1.05/1.30      inference('demod', [status(thm)], ['142', '145'])).
% 1.05/1.30  thf('147', plain, ($false), inference('simplify', [status(thm)], ['146'])).
% 1.05/1.30  
% 1.05/1.30  % SZS output end Refutation
% 1.05/1.30  
% 1.05/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
