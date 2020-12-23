%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xSCJOPJasI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:09 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  171 (2206 expanded)
%              Number of leaves         :   38 ( 646 expanded)
%              Depth                    :   24
%              Number of atoms          : 1123 (29432 expanded)
%              Number of equality atoms :   90 (1587 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('12',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['14','19'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X28 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','27','28'])).

thf('30',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

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

thf('33',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','71'])).

thf('73',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31
       != ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('79',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['75','81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('84',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('94',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','94'])).

thf('96',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','27','28'])).

thf('97',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','97'])).

thf('99',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('100',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','100'])).

thf('102',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['50','101'])).

thf('103',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','102'])).

thf('104',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','103'])).

thf('105',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31
       != ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('106',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('109',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','109'])).

thf('111',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('113',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('114',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','109'])).

thf('118',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('119',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('121',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','109'])).

thf('122',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('123',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['116','117','119','120','121','122'])).

thf('124',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('125',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','102'])).

thf('126',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['116','117','119','120','121','122'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','71'])).

thf('129',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['75','81'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['111','123','129','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xSCJOPJasI
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:51:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.54/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.71  % Solved by: fo/fo7.sh
% 0.54/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.71  % done 383 iterations in 0.241s
% 0.54/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.71  % SZS output start Refutation
% 0.54/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.54/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.71  thf(t8_funct_2, conjecture,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.71       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.54/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.54/0.71           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.54/0.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.71            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.71          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.54/0.71            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.54/0.71              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.54/0.71                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.54/0.71  thf('0', plain,
% 0.54/0.71      ((~ (v1_funct_1 @ sk_D)
% 0.54/0.71        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.54/0.71        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('1', plain,
% 0.54/0.71      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.54/0.71         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.54/0.71      inference('split', [status(esa)], ['0'])).
% 0.54/0.71  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.54/0.71      inference('split', [status(esa)], ['0'])).
% 0.54/0.71  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.54/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.71  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('6', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.71  thf('7', plain,
% 0.54/0.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.54/0.71         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.54/0.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.54/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.71  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.54/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.54/0.71  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.54/0.71      inference('demod', [status(thm)], ['5', '8'])).
% 0.54/0.71  thf('10', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(cc2_relset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.71  thf('11', plain,
% 0.54/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.71         ((v4_relat_1 @ X17 @ X18)
% 0.54/0.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.54/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.71  thf('12', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.54/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.71  thf(d18_relat_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( v1_relat_1 @ B ) =>
% 0.54/0.71       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.71  thf('13', plain,
% 0.54/0.71      (![X12 : $i, X13 : $i]:
% 0.54/0.71         (~ (v4_relat_1 @ X12 @ X13)
% 0.54/0.71          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.54/0.71          | ~ (v1_relat_1 @ X12))),
% 0.54/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(cc2_relat_1, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( v1_relat_1 @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (![X10 : $i, X11 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.54/0.71          | (v1_relat_1 @ X10)
% 0.54/0.71          | ~ (v1_relat_1 @ X11))),
% 0.54/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.71  thf('17', plain,
% 0.54/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.54/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.71  thf(fc6_relat_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.71  thf('18', plain,
% 0.54/0.71      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.54/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.71  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.54/0.71  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.54/0.71      inference('demod', [status(thm)], ['14', '19'])).
% 0.54/0.71  thf(t11_relset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( v1_relat_1 @ C ) =>
% 0.54/0.71       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.54/0.71           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.54/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.54/0.71  thf('21', plain,
% 0.54/0.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.71         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.54/0.71          | ~ (r1_tarski @ (k2_relat_1 @ X26) @ X28)
% 0.54/0.71          | (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.54/0.71          | ~ (v1_relat_1 @ X26))),
% 0.54/0.71      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.54/0.71  thf('22', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ sk_D)
% 0.54/0.71          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.54/0.71          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.71  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.54/0.71  thf('24', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.54/0.71          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.54/0.71      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.71  thf('25', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['9', '24'])).
% 0.54/0.71  thf('26', plain,
% 0.54/0.71      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.54/0.71         <= (~
% 0.54/0.71             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.54/0.71      inference('split', [status(esa)], ['0'])).
% 0.54/0.71  thf('27', plain,
% 0.54/0.71      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.54/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.54/0.71       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.54/0.71       ~ ((v1_funct_1 @ sk_D))),
% 0.54/0.71      inference('split', [status(esa)], ['0'])).
% 0.54/0.71  thf('29', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.54/0.71      inference('sat_resolution*', [status(thm)], ['4', '27', '28'])).
% 0.54/0.71  thf('30', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.54/0.71      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.54/0.71  thf(d1_funct_2, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.54/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.54/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.54/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.54/0.71  thf(zf_stmt_1, axiom,
% 0.54/0.71    (![B:$i,A:$i]:
% 0.54/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.71       ( zip_tseitin_0 @ B @ A ) ))).
% 0.54/0.71  thf('31', plain,
% 0.54/0.71      (![X29 : $i, X30 : $i]:
% 0.54/0.71         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.71  thf('32', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['9', '24'])).
% 0.54/0.71  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.54/0.71  thf(zf_stmt_3, axiom,
% 0.54/0.71    (![C:$i,B:$i,A:$i]:
% 0.54/0.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.54/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.54/0.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.54/0.71  thf(zf_stmt_5, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.54/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.54/0.71  thf('33', plain,
% 0.54/0.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.71         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.54/0.71          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.54/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.71  thf('34', plain,
% 0.54/0.71      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['32', '33'])).
% 0.54/0.71  thf('35', plain,
% 0.54/0.71      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['31', '34'])).
% 0.54/0.71  thf('36', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['9', '24'])).
% 0.54/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.71  thf('37', plain,
% 0.54/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.71         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.54/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.71  thf('38', plain,
% 0.54/0.71      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.54/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.54/0.71  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('40', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.54/0.71         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.54/0.71          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.54/0.71          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.71  thf('41', plain,
% 0.54/0.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.54/0.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.54/0.71  thf('42', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('43', plain,
% 0.54/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.71         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.54/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.71  thf('44', plain,
% 0.54/0.71      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.54/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.71  thf('45', plain,
% 0.54/0.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.54/0.71      inference('demod', [status(thm)], ['41', '44'])).
% 0.54/0.71  thf('46', plain,
% 0.54/0.71      (![X29 : $i, X30 : $i]:
% 0.54/0.71         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.71  thf('47', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('48', plain,
% 0.54/0.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.71         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.54/0.71          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.54/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.71  thf('49', plain,
% 0.54/0.71      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.71  thf('50', plain,
% 0.54/0.71      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['46', '49'])).
% 0.54/0.71  thf('51', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('52', plain,
% 0.54/0.71      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.54/0.71      inference('split', [status(esa)], ['51'])).
% 0.54/0.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.71  thf('53', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.71  thf(t3_subset, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.71  thf('54', plain,
% 0.54/0.71      (![X7 : $i, X9 : $i]:
% 0.54/0.71         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.54/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.71  thf('55', plain,
% 0.54/0.71      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.71  thf('56', plain,
% 0.54/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.71         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.54/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.71  thf('57', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['55', '56'])).
% 0.54/0.71  thf('58', plain,
% 0.54/0.71      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.71  thf('59', plain,
% 0.54/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.71         ((v4_relat_1 @ X17 @ X18)
% 0.54/0.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.54/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.71  thf('60', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.54/0.71      inference('sup-', [status(thm)], ['58', '59'])).
% 0.54/0.71  thf('61', plain,
% 0.54/0.71      (![X12 : $i, X13 : $i]:
% 0.54/0.71         (~ (v4_relat_1 @ X12 @ X13)
% 0.54/0.71          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.54/0.71          | ~ (v1_relat_1 @ X12))),
% 0.54/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.71  thf('62', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.71          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.71  thf(t113_zfmisc_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.71  thf('63', plain,
% 0.54/0.71      (![X5 : $i, X6 : $i]:
% 0.54/0.71         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.71  thf('64', plain,
% 0.54/0.71      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.54/0.71      inference('simplify', [status(thm)], ['63'])).
% 0.54/0.71  thf('65', plain,
% 0.54/0.71      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.54/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.71  thf('66', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.71      inference('sup+', [status(thm)], ['64', '65'])).
% 0.54/0.71  thf('67', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.54/0.71      inference('demod', [status(thm)], ['62', '66'])).
% 0.54/0.71  thf('68', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.71  thf(d10_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.71  thf('69', plain,
% 0.54/0.71      (![X0 : $i, X2 : $i]:
% 0.54/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.71  thf('70', plain,
% 0.54/0.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['68', '69'])).
% 0.54/0.71  thf('71', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['67', '70'])).
% 0.54/0.71  thf('72', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.71      inference('demod', [status(thm)], ['57', '71'])).
% 0.54/0.71  thf('73', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.54/0.71         (((X31) != (k1_relset_1 @ X31 @ X32 @ X33))
% 0.54/0.71          | (v1_funct_2 @ X33 @ X31 @ X32)
% 0.54/0.71          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.71  thf('74', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (((X1) != (k1_xboole_0))
% 0.54/0.71          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.54/0.71          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['72', '73'])).
% 0.54/0.71  thf('75', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.71          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.71      inference('simplify', [status(thm)], ['74'])).
% 0.54/0.71  thf('76', plain,
% 0.54/0.71      (![X29 : $i, X30 : $i]:
% 0.54/0.71         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.71  thf('77', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 0.54/0.71      inference('simplify', [status(thm)], ['76'])).
% 0.54/0.71  thf('78', plain,
% 0.54/0.71      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.71  thf('79', plain,
% 0.54/0.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.71         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.54/0.71          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.54/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.71  thf('80', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['78', '79'])).
% 0.54/0.71  thf('81', plain,
% 0.54/0.71      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.54/0.71      inference('sup-', [status(thm)], ['77', '80'])).
% 0.54/0.71  thf('82', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.54/0.71      inference('demod', [status(thm)], ['75', '81'])).
% 0.54/0.71  thf('83', plain,
% 0.54/0.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.71      inference('split', [status(esa)], ['51'])).
% 0.54/0.71  thf('84', plain,
% 0.54/0.71      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.54/0.71         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.54/0.71      inference('split', [status(esa)], ['0'])).
% 0.54/0.71  thf('85', plain,
% 0.54/0.71      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.54/0.71         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup-', [status(thm)], ['83', '84'])).
% 0.54/0.71  thf('86', plain,
% 0.54/0.71      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.54/0.71      inference('simplify', [status(thm)], ['63'])).
% 0.54/0.71  thf('87', plain,
% 0.54/0.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.71      inference('split', [status(esa)], ['51'])).
% 0.54/0.71  thf('88', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('89', plain,
% 0.54/0.71      (((m1_subset_1 @ sk_D @ 
% 0.54/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.54/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup+', [status(thm)], ['87', '88'])).
% 0.54/0.71  thf('90', plain,
% 0.54/0.71      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.54/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup+', [status(thm)], ['86', '89'])).
% 0.54/0.71  thf('91', plain,
% 0.54/0.71      (![X7 : $i, X8 : $i]:
% 0.54/0.71         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.71  thf('92', plain,
% 0.54/0.71      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup-', [status(thm)], ['90', '91'])).
% 0.54/0.71  thf('93', plain,
% 0.54/0.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['68', '69'])).
% 0.54/0.71  thf('94', plain,
% 0.54/0.71      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup-', [status(thm)], ['92', '93'])).
% 0.54/0.71  thf('95', plain,
% 0.54/0.71      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.54/0.71         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.54/0.71      inference('demod', [status(thm)], ['85', '94'])).
% 0.54/0.71  thf('96', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.54/0.71      inference('sat_resolution*', [status(thm)], ['4', '27', '28'])).
% 0.54/0.71  thf('97', plain,
% 0.54/0.71      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.54/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.71      inference('simpl_trail', [status(thm)], ['95', '96'])).
% 0.54/0.71  thf('98', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['82', '97'])).
% 0.54/0.71  thf('99', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.54/0.71      inference('split', [status(esa)], ['51'])).
% 0.54/0.71  thf('100', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.54/0.71      inference('sat_resolution*', [status(thm)], ['98', '99'])).
% 0.54/0.71  thf('101', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.71      inference('simpl_trail', [status(thm)], ['52', '100'])).
% 0.54/0.71  thf('102', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.54/0.71      inference('simplify_reflect-', [status(thm)], ['50', '101'])).
% 0.54/0.71  thf('103', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.54/0.71      inference('demod', [status(thm)], ['45', '102'])).
% 0.54/0.71  thf('104', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.54/0.71      inference('demod', [status(thm)], ['38', '103'])).
% 0.54/0.71  thf('105', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.54/0.71         (((X31) != (k1_relset_1 @ X31 @ X32 @ X33))
% 0.54/0.71          | (v1_funct_2 @ X33 @ X31 @ X32)
% 0.54/0.71          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.71  thf('106', plain,
% 0.54/0.71      ((((sk_A) != (sk_A))
% 0.54/0.71        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.54/0.71        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.54/0.71      inference('sup-', [status(thm)], ['104', '105'])).
% 0.54/0.71  thf('107', plain,
% 0.54/0.71      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.54/0.71        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.54/0.71      inference('simplify', [status(thm)], ['106'])).
% 0.54/0.71  thf('108', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.54/0.71      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.54/0.71  thf('109', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.54/0.71      inference('clc', [status(thm)], ['107', '108'])).
% 0.54/0.71  thf('110', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['35', '109'])).
% 0.54/0.71  thf('111', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 0.54/0.71      inference('demod', [status(thm)], ['30', '110'])).
% 0.54/0.71  thf('112', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['9', '24'])).
% 0.54/0.71  thf('113', plain,
% 0.54/0.71      (![X7 : $i, X8 : $i]:
% 0.54/0.71         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.71  thf('114', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.54/0.71      inference('sup-', [status(thm)], ['112', '113'])).
% 0.54/0.71  thf('115', plain,
% 0.54/0.71      (![X0 : $i, X2 : $i]:
% 0.54/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.71  thf('116', plain,
% 0.54/0.71      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 0.54/0.71        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['114', '115'])).
% 0.54/0.71  thf('117', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['35', '109'])).
% 0.54/0.71  thf('118', plain,
% 0.54/0.71      (![X5 : $i, X6 : $i]:
% 0.54/0.71         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.71  thf('119', plain,
% 0.54/0.71      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.71      inference('simplify', [status(thm)], ['118'])).
% 0.54/0.71  thf('120', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.71  thf('121', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['35', '109'])).
% 0.54/0.71  thf('122', plain,
% 0.54/0.71      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.71      inference('simplify', [status(thm)], ['118'])).
% 0.54/0.71  thf('123', plain, (((k1_xboole_0) = (sk_D))),
% 0.54/0.71      inference('demod', [status(thm)],
% 0.54/0.71                ['116', '117', '119', '120', '121', '122'])).
% 0.54/0.71  thf('124', plain,
% 0.54/0.71      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.54/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.71  thf('125', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.54/0.71      inference('demod', [status(thm)], ['45', '102'])).
% 0.54/0.71  thf('126', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_A))),
% 0.54/0.71      inference('demod', [status(thm)], ['124', '125'])).
% 0.54/0.71  thf('127', plain, (((k1_xboole_0) = (sk_D))),
% 0.54/0.71      inference('demod', [status(thm)],
% 0.54/0.71                ['116', '117', '119', '120', '121', '122'])).
% 0.54/0.71  thf('128', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.71      inference('demod', [status(thm)], ['57', '71'])).
% 0.54/0.71  thf('129', plain, (((k1_xboole_0) = (sk_A))),
% 0.54/0.71      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.54/0.71  thf('130', plain,
% 0.54/0.71      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.54/0.71      inference('demod', [status(thm)], ['75', '81'])).
% 0.54/0.71  thf('131', plain, ($false),
% 0.54/0.71      inference('demod', [status(thm)], ['111', '123', '129', '130'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
