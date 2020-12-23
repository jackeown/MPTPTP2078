%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.37opnJFQJs

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:07 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  177 (2062 expanded)
%              Number of leaves         :   38 ( 598 expanded)
%              Depth                    :   24
%              Number of atoms          : 1191 (27798 expanded)
%              Number of equality atoms :   95 (1660 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X29 )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('53',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('58',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('63',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['61','65'])).

thf('67',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','70'])).

thf('72',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('78',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['74','80'])).

thf('82',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('90',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('92',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('97',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('98',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('99',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('105',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','95','102','103','104'])).

thf('106',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['51','105'])).

thf('107',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['49','106'])).

thf('108',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['44','107'])).

thf('109',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','108'])).

thf('110',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('111',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('114',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['34','114'])).

thf('116',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','115'])).

thf('117',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('119',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('120',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('122',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','115'])).

thf('124',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('125',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('127',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','115'])).

thf('128',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('129',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['122','123','125','126','127','128'])).

thf('130',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('131',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['44','107'])).

thf('132',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['122','123','125','126','127','128'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','70'])).

thf('135',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['74','80'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['117','129','135','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.37opnJFQJs
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.76  % Solved by: fo/fo7.sh
% 0.55/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.76  % done 456 iterations in 0.308s
% 0.55/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.76  % SZS output start Refutation
% 0.55/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.55/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.55/0.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.55/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.76  thf(t8_funct_2, conjecture,
% 0.55/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.76       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.55/0.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.55/0.76           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.55/0.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.76        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.76            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.76          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.55/0.76            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.55/0.76              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.55/0.76                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.55/0.76    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.55/0.76  thf('0', plain,
% 0.55/0.76      ((~ (v1_funct_1 @ sk_D)
% 0.55/0.76        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.55/0.76        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('1', plain,
% 0.55/0.76      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.55/0.76         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.55/0.76      inference('split', [status(esa)], ['0'])).
% 0.55/0.76  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.55/0.76      inference('split', [status(esa)], ['0'])).
% 0.55/0.76  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.55/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.76  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('6', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(redefinition_k2_relset_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.55/0.76  thf('7', plain,
% 0.55/0.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.55/0.76         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.55/0.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.76  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.55/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.55/0.76  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.55/0.76      inference('demod', [status(thm)], ['5', '8'])).
% 0.55/0.76  thf('10', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(cc2_relset_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.76  thf('11', plain,
% 0.55/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.76         ((v4_relat_1 @ X18 @ X19)
% 0.55/0.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.55/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.76  thf('12', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.55/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.55/0.76  thf(d18_relat_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( v1_relat_1 @ B ) =>
% 0.55/0.76       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.55/0.76  thf('13', plain,
% 0.55/0.76      (![X12 : $i, X13 : $i]:
% 0.55/0.76         (~ (v4_relat_1 @ X12 @ X13)
% 0.55/0.76          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.55/0.76          | ~ (v1_relat_1 @ X12))),
% 0.55/0.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.55/0.76  thf('14', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.76  thf('15', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(cc2_relat_1, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( v1_relat_1 @ A ) =>
% 0.55/0.76       ( ![B:$i]:
% 0.55/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.55/0.76  thf('16', plain,
% 0.55/0.76      (![X10 : $i, X11 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.55/0.76          | (v1_relat_1 @ X10)
% 0.55/0.76          | ~ (v1_relat_1 @ X11))),
% 0.55/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.76  thf('17', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.55/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.55/0.76  thf(fc6_relat_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.55/0.76  thf('18', plain,
% 0.55/0.76      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.55/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.76  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 0.55/0.76      inference('demod', [status(thm)], ['17', '18'])).
% 0.55/0.76  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.55/0.76      inference('demod', [status(thm)], ['14', '19'])).
% 0.55/0.76  thf(t11_relset_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( v1_relat_1 @ C ) =>
% 0.55/0.76       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.55/0.76           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.55/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.55/0.76  thf('21', plain,
% 0.55/0.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.76         (~ (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 0.55/0.76          | ~ (r1_tarski @ (k2_relat_1 @ X27) @ X29)
% 0.55/0.76          | (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.55/0.76          | ~ (v1_relat_1 @ X27))),
% 0.55/0.76      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.55/0.76  thf('22', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ sk_D)
% 0.55/0.76          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.55/0.76          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.55/0.76  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.55/0.76      inference('demod', [status(thm)], ['17', '18'])).
% 0.55/0.76  thf('24', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.55/0.76          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.55/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('25', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['9', '24'])).
% 0.55/0.76  thf('26', plain,
% 0.55/0.76      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.55/0.76         <= (~
% 0.55/0.76             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.55/0.76      inference('split', [status(esa)], ['0'])).
% 0.55/0.76  thf('27', plain,
% 0.55/0.76      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['25', '26'])).
% 0.55/0.76  thf('28', plain,
% 0.55/0.76      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.55/0.76       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.55/0.76       ~ ((v1_funct_1 @ sk_D))),
% 0.55/0.76      inference('split', [status(esa)], ['0'])).
% 0.55/0.76  thf('29', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.55/0.76      inference('sat_resolution*', [status(thm)], ['4', '27', '28'])).
% 0.55/0.76  thf('30', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.55/0.76      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.55/0.76  thf(d1_funct_2, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.55/0.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.55/0.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.55/0.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_1, axiom,
% 0.55/0.76    (![B:$i,A:$i]:
% 0.55/0.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.76       ( zip_tseitin_0 @ B @ A ) ))).
% 0.55/0.76  thf('31', plain,
% 0.55/0.76      (![X30 : $i, X31 : $i]:
% 0.55/0.76         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.76  thf('32', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['9', '24'])).
% 0.55/0.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.55/0.76  thf(zf_stmt_3, axiom,
% 0.55/0.76    (![C:$i,B:$i,A:$i]:
% 0.55/0.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.55/0.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.55/0.76  thf(zf_stmt_5, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.55/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.55/0.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.55/0.76  thf('33', plain,
% 0.55/0.76      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.55/0.76         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.55/0.76          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.55/0.76          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.55/0.76  thf('34', plain,
% 0.55/0.76      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.76  thf('35', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['9', '24'])).
% 0.55/0.76  thf(redefinition_k1_relset_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.55/0.76  thf('36', plain,
% 0.55/0.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.76         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.55/0.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.76  thf('37', plain,
% 0.55/0.76      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.55/0.76      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.76  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('39', plain,
% 0.55/0.76      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.55/0.76         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.55/0.76          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.55/0.77          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.77  thf('40', plain,
% 0.55/0.77      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.55/0.77        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.55/0.77  thf('41', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('42', plain,
% 0.55/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.77         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.55/0.77          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.55/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.77  thf('43', plain,
% 0.55/0.77      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.55/0.77      inference('sup-', [status(thm)], ['41', '42'])).
% 0.55/0.77  thf('44', plain,
% 0.55/0.77      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.55/0.77      inference('demod', [status(thm)], ['40', '43'])).
% 0.55/0.77  thf('45', plain,
% 0.55/0.77      (![X30 : $i, X31 : $i]:
% 0.55/0.77         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.77  thf('46', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('47', plain,
% 0.55/0.77      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.55/0.77         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.55/0.77          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.55/0.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.55/0.77  thf('48', plain,
% 0.55/0.77      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.77  thf('49', plain,
% 0.55/0.77      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['45', '48'])).
% 0.55/0.77  thf('50', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('51', plain,
% 0.55/0.77      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.55/0.77      inference('split', [status(esa)], ['50'])).
% 0.55/0.77  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.55/0.77  thf('52', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.55/0.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.55/0.77  thf(t3_subset, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.77  thf('53', plain,
% 0.55/0.77      (![X7 : $i, X9 : $i]:
% 0.55/0.77         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.55/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.77  thf('54', plain,
% 0.55/0.77      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.77  thf('55', plain,
% 0.55/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.77         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.55/0.77          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.55/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.77  thf('56', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['54', '55'])).
% 0.55/0.77  thf('57', plain,
% 0.55/0.77      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.77  thf('58', plain,
% 0.55/0.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.77         ((v4_relat_1 @ X18 @ X19)
% 0.55/0.77          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.55/0.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.77  thf('59', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.55/0.77      inference('sup-', [status(thm)], ['57', '58'])).
% 0.55/0.77  thf('60', plain,
% 0.55/0.77      (![X12 : $i, X13 : $i]:
% 0.55/0.77         (~ (v4_relat_1 @ X12 @ X13)
% 0.55/0.77          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.55/0.77          | ~ (v1_relat_1 @ X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.55/0.77  thf('61', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ k1_xboole_0)
% 0.55/0.77          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['59', '60'])).
% 0.55/0.77  thf(t113_zfmisc_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.55/0.77       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.77  thf('62', plain,
% 0.55/0.77      (![X5 : $i, X6 : $i]:
% 0.55/0.77         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.55/0.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.77  thf('63', plain,
% 0.55/0.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.55/0.77      inference('simplify', [status(thm)], ['62'])).
% 0.55/0.77  thf('64', plain,
% 0.55/0.77      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.55/0.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.77  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.55/0.77      inference('sup+', [status(thm)], ['63', '64'])).
% 0.55/0.77  thf('66', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.55/0.77      inference('demod', [status(thm)], ['61', '65'])).
% 0.55/0.77  thf('67', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.55/0.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.55/0.77  thf(d10_xboole_0, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.77  thf('68', plain,
% 0.55/0.77      (![X0 : $i, X2 : $i]:
% 0.55/0.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.55/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.77  thf('69', plain,
% 0.55/0.77      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['67', '68'])).
% 0.55/0.77  thf('70', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['66', '69'])).
% 0.55/0.77  thf('71', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.77      inference('demod', [status(thm)], ['56', '70'])).
% 0.55/0.77  thf('72', plain,
% 0.55/0.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.55/0.77         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 0.55/0.77          | (v1_funct_2 @ X34 @ X32 @ X33)
% 0.55/0.77          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.77  thf('73', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         (((X1) != (k1_xboole_0))
% 0.55/0.77          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.55/0.77          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['71', '72'])).
% 0.55/0.77  thf('74', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.55/0.77          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.77      inference('simplify', [status(thm)], ['73'])).
% 0.55/0.77  thf('75', plain,
% 0.55/0.77      (![X30 : $i, X31 : $i]:
% 0.55/0.77         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.77  thf('76', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 0.55/0.77      inference('simplify', [status(thm)], ['75'])).
% 0.55/0.77  thf('77', plain,
% 0.55/0.77      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.77  thf('78', plain,
% 0.55/0.77      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.55/0.77         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.55/0.77          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.55/0.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.55/0.77  thf('79', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.55/0.77      inference('sup-', [status(thm)], ['77', '78'])).
% 0.55/0.77  thf('80', plain,
% 0.55/0.77      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.55/0.77      inference('sup-', [status(thm)], ['76', '79'])).
% 0.55/0.77  thf('81', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.55/0.77      inference('demod', [status(thm)], ['74', '80'])).
% 0.55/0.77  thf('82', plain,
% 0.55/0.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.55/0.77      inference('simplify', [status(thm)], ['62'])).
% 0.55/0.77  thf('83', plain,
% 0.55/0.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('split', [status(esa)], ['50'])).
% 0.55/0.77  thf('84', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('85', plain,
% 0.55/0.77      (((m1_subset_1 @ sk_D @ 
% 0.55/0.77         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.55/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('sup+', [status(thm)], ['83', '84'])).
% 0.55/0.77  thf('86', plain,
% 0.55/0.77      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.55/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('sup+', [status(thm)], ['82', '85'])).
% 0.55/0.77  thf('87', plain,
% 0.55/0.77      (![X7 : $i, X8 : $i]:
% 0.55/0.77         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.55/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.77  thf('88', plain,
% 0.55/0.77      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['86', '87'])).
% 0.55/0.77  thf('89', plain,
% 0.55/0.77      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['67', '68'])).
% 0.55/0.77  thf('90', plain,
% 0.55/0.77      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['88', '89'])).
% 0.55/0.77  thf('91', plain,
% 0.55/0.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('split', [status(esa)], ['50'])).
% 0.55/0.77  thf('92', plain,
% 0.55/0.77      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.55/0.77         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.55/0.77      inference('split', [status(esa)], ['0'])).
% 0.55/0.77  thf('93', plain,
% 0.55/0.77      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.55/0.77         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['91', '92'])).
% 0.55/0.77  thf('94', plain,
% 0.55/0.77      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.55/0.77         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['90', '93'])).
% 0.55/0.77  thf('95', plain,
% 0.55/0.77      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['81', '94'])).
% 0.55/0.77  thf('96', plain,
% 0.55/0.77      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.55/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('sup+', [status(thm)], ['82', '85'])).
% 0.55/0.77  thf('97', plain,
% 0.55/0.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.55/0.77      inference('simplify', [status(thm)], ['62'])).
% 0.55/0.77  thf('98', plain,
% 0.55/0.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('split', [status(esa)], ['50'])).
% 0.55/0.77  thf('99', plain,
% 0.55/0.77      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.55/0.77         <= (~
% 0.55/0.77             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.55/0.77      inference('split', [status(esa)], ['0'])).
% 0.55/0.77  thf('100', plain,
% 0.55/0.77      ((~ (m1_subset_1 @ sk_D @ 
% 0.55/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.55/0.77         <= (~
% 0.55/0.77             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.55/0.77             (((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['98', '99'])).
% 0.55/0.77  thf('101', plain,
% 0.55/0.77      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.55/0.77         <= (~
% 0.55/0.77             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.55/0.77             (((sk_A) = (k1_xboole_0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['97', '100'])).
% 0.55/0.77  thf('102', plain,
% 0.55/0.77      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.55/0.77       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['96', '101'])).
% 0.55/0.77  thf('103', plain,
% 0.55/0.77      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.55/0.77       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.55/0.77      inference('split', [status(esa)], ['0'])).
% 0.55/0.77  thf('104', plain,
% 0.55/0.77      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.55/0.77      inference('split', [status(esa)], ['50'])).
% 0.55/0.77  thf('105', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.55/0.77      inference('sat_resolution*', [status(thm)],
% 0.55/0.77                ['4', '95', '102', '103', '104'])).
% 0.55/0.77  thf('106', plain, (((sk_B) != (k1_xboole_0))),
% 0.55/0.77      inference('simpl_trail', [status(thm)], ['51', '105'])).
% 0.55/0.77  thf('107', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.55/0.77      inference('simplify_reflect-', [status(thm)], ['49', '106'])).
% 0.55/0.77  thf('108', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['44', '107'])).
% 0.55/0.77  thf('109', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.55/0.77      inference('demod', [status(thm)], ['37', '108'])).
% 0.55/0.77  thf('110', plain,
% 0.55/0.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.55/0.77         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 0.55/0.77          | (v1_funct_2 @ X34 @ X32 @ X33)
% 0.55/0.77          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.77  thf('111', plain,
% 0.55/0.77      ((((sk_A) != (sk_A))
% 0.55/0.77        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.55/0.77        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.55/0.77      inference('sup-', [status(thm)], ['109', '110'])).
% 0.55/0.77  thf('112', plain,
% 0.55/0.77      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.55/0.77        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['111'])).
% 0.55/0.77  thf('113', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.55/0.77      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.55/0.77  thf('114', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.55/0.77      inference('clc', [status(thm)], ['112', '113'])).
% 0.55/0.77  thf('115', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 0.55/0.77      inference('clc', [status(thm)], ['34', '114'])).
% 0.55/0.77  thf('116', plain, (((sk_C) = (k1_xboole_0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['31', '115'])).
% 0.55/0.77  thf('117', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 0.55/0.77      inference('demod', [status(thm)], ['30', '116'])).
% 0.55/0.77  thf('118', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['9', '24'])).
% 0.55/0.77  thf('119', plain,
% 0.55/0.77      (![X7 : $i, X8 : $i]:
% 0.55/0.77         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.55/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.77  thf('120', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.55/0.77      inference('sup-', [status(thm)], ['118', '119'])).
% 0.55/0.77  thf('121', plain,
% 0.55/0.77      (![X0 : $i, X2 : $i]:
% 0.55/0.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.55/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.77  thf('122', plain,
% 0.55/0.77      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 0.55/0.77        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['120', '121'])).
% 0.55/0.77  thf('123', plain, (((sk_C) = (k1_xboole_0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['31', '115'])).
% 0.55/0.77  thf('124', plain,
% 0.55/0.77      (![X5 : $i, X6 : $i]:
% 0.55/0.77         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.55/0.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.77  thf('125', plain,
% 0.55/0.77      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.77      inference('simplify', [status(thm)], ['124'])).
% 0.55/0.77  thf('126', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.55/0.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.55/0.77  thf('127', plain, (((sk_C) = (k1_xboole_0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['31', '115'])).
% 0.55/0.77  thf('128', plain,
% 0.55/0.77      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.77      inference('simplify', [status(thm)], ['124'])).
% 0.55/0.77  thf('129', plain, (((k1_xboole_0) = (sk_D))),
% 0.55/0.77      inference('demod', [status(thm)],
% 0.55/0.77                ['122', '123', '125', '126', '127', '128'])).
% 0.55/0.77  thf('130', plain,
% 0.55/0.77      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.55/0.77      inference('sup-', [status(thm)], ['41', '42'])).
% 0.55/0.77  thf('131', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['44', '107'])).
% 0.55/0.77  thf('132', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_A))),
% 0.55/0.77      inference('demod', [status(thm)], ['130', '131'])).
% 0.55/0.77  thf('133', plain, (((k1_xboole_0) = (sk_D))),
% 0.55/0.77      inference('demod', [status(thm)],
% 0.55/0.77                ['122', '123', '125', '126', '127', '128'])).
% 0.55/0.77  thf('134', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.77      inference('demod', [status(thm)], ['56', '70'])).
% 0.55/0.77  thf('135', plain, (((k1_xboole_0) = (sk_A))),
% 0.55/0.77      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.55/0.77  thf('136', plain,
% 0.55/0.77      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.55/0.77      inference('demod', [status(thm)], ['74', '80'])).
% 0.55/0.77  thf('137', plain, ($false),
% 0.55/0.77      inference('demod', [status(thm)], ['117', '129', '135', '136'])).
% 0.55/0.77  
% 0.55/0.77  % SZS output end Refutation
% 0.55/0.77  
% 0.55/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
