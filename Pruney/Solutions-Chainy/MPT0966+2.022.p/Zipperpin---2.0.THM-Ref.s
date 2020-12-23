%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DhtrVACPco

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  162 (2030 expanded)
%              Number of leaves         :   39 ( 590 expanded)
%              Depth                    :   24
%              Number of atoms          : 1079 (28376 expanded)
%              Number of equality atoms :   90 (1531 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
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
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C_1 ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X33 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','27','28'])).

thf('30',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('58',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36
       != ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X35 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    ! [X34: $i] :
      ( zip_tseitin_0 @ X34 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('66',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['62','68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('71',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('82',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['72','84'])).

thf('86',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','27','28'])).

thf('87',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','87'])).

thf('89',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('90',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','90'])).

thf('92',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['50','91'])).

thf('93',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','92'])).

thf('94',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','93'])).

thf('95',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36
       != ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('96',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('99',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','99'])).

thf('101',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('103',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('106',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','99'])).

thf('108',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('109',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('111',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','99'])).

thf('112',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('113',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['106','107','109','110','111','112'])).

thf('114',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('115',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','92'])).

thf('116',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['106','107','109','110','111','112'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('119',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['62','68'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['101','113','119','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DhtrVACPco
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 380 iterations in 0.129s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(t8_funct_2, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.20/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.58           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.20/0.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.58            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.20/0.58            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.58              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.20/0.58                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      ((~ (v1_funct_1 @ sk_D)
% 0.20/0.58        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.20/0.58        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.20/0.58         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.58  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.58         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.20/0.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.58  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.58  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.20/0.58      inference('demod', [status(thm)], ['5', '8'])).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(cc2_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.58         ((v4_relat_1 @ X22 @ X23)
% 0.20/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.58  thf('12', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.20/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf(d18_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ B ) =>
% 0.20/0.58       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X12 : $i, X13 : $i]:
% 0.20/0.58         (~ (v4_relat_1 @ X12 @ X13)
% 0.20/0.58          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.20/0.58          | ~ (v1_relat_1 @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(cc2_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.58          | (v1_relat_1 @ X10)
% 0.20/0.58          | ~ (v1_relat_1 @ X11))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.58  thf(fc6_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.20/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.58  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.58  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.20/0.58      inference('demod', [status(thm)], ['14', '19'])).
% 0.20/0.58  thf(t11_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ C ) =>
% 0.20/0.58       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.20/0.58           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.20/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 0.20/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X31) @ X33)
% 0.20/0.58          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.20/0.58          | ~ (v1_relat_1 @ X31))),
% 0.20/0.58      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ sk_D)
% 0.20/0.58          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.58          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.58  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.58          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['9', '24'])).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.20/0.58         <= (~
% 0.20/0.58             ((m1_subset_1 @ sk_D @ 
% 0.20/0.58               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 0.20/0.58       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.20/0.58       ~ ((v1_funct_1 @ sk_D))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('29', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['4', '27', '28'])).
% 0.20/0.58  thf('30', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.20/0.58  thf(d1_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_1, axiom,
% 0.20/0.58    (![B:$i,A:$i]:
% 0.20/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X34 : $i, X35 : $i]:
% 0.20/0.58         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['9', '24'])).
% 0.20/0.58  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_3, axiom,
% 0.20/0.58    (![C:$i,B:$i,A:$i]:
% 0.20/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_5, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.58         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.20/0.58          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.20/0.58          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.20/0.58        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['31', '34'])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['9', '24'])).
% 0.20/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.58         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.20/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.58         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.20/0.58          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.20/0.58          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.20/0.58        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.58         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.20/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.20/0.58      inference('demod', [status(thm)], ['41', '44'])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      (![X34 : $i, X35 : $i]:
% 0.20/0.58         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.58         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.20/0.58          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.20/0.58          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['46', '49'])).
% 0.20/0.58  thf('51', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('52', plain,
% 0.20/0.58      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['51'])).
% 0.20/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.58  thf('53', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.58  thf(t3_subset, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      (![X7 : $i, X9 : $i]:
% 0.20/0.58         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.58  thf('55', plain,
% 0.20/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.58         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.20/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.58  thf(t60_relat_1, axiom,
% 0.20/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('58', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.58  thf('59', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.58  thf('60', plain,
% 0.20/0.58      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.58         (((X36) != (k1_relset_1 @ X36 @ X37 @ X38))
% 0.20/0.58          | (v1_funct_2 @ X38 @ X36 @ X37)
% 0.20/0.58          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((X1) != (k1_xboole_0))
% 0.20/0.58          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.20/0.58          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.58          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.58  thf('63', plain,
% 0.20/0.58      (![X34 : $i, X35 : $i]:
% 0.20/0.58         ((zip_tseitin_0 @ X34 @ X35) | ((X35) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.58  thf('64', plain, (![X34 : $i]: (zip_tseitin_0 @ X34 @ k1_xboole_0)),
% 0.20/0.58      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.58         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.20/0.58          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.20/0.58          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.58  thf('67', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.58  thf('68', plain,
% 0.20/0.58      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['64', '67'])).
% 0.20/0.58  thf('69', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.58      inference('demod', [status(thm)], ['62', '68'])).
% 0.20/0.58  thf('70', plain,
% 0.20/0.58      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['51'])).
% 0.20/0.58  thf('71', plain,
% 0.20/0.58      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.20/0.58         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('72', plain,
% 0.20/0.58      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.20/0.58         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.20/0.58             (((sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.58  thf(t113_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf('73', plain,
% 0.20/0.58      (![X5 : $i, X6 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.58  thf('74', plain,
% 0.20/0.58      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.58  thf('75', plain,
% 0.20/0.58      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['51'])).
% 0.20/0.58  thf('76', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('77', plain,
% 0.20/0.58      (((m1_subset_1 @ sk_D @ 
% 0.20/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.20/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['75', '76'])).
% 0.20/0.58  thf('78', plain,
% 0.20/0.58      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.20/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['74', '77'])).
% 0.20/0.58  thf('79', plain,
% 0.20/0.58      (![X7 : $i, X8 : $i]:
% 0.20/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.58  thf('80', plain,
% 0.20/0.58      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.58  thf('81', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.58  thf(d10_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.58  thf('82', plain,
% 0.20/0.58      (![X0 : $i, X2 : $i]:
% 0.20/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('83', plain,
% 0.20/0.58      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.58  thf('84', plain,
% 0.20/0.58      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['80', '83'])).
% 0.20/0.58  thf('85', plain,
% 0.20/0.58      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 0.20/0.58         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.20/0.58             (((sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('demod', [status(thm)], ['72', '84'])).
% 0.20/0.58  thf('86', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['4', '27', '28'])).
% 0.20/0.58  thf('87', plain,
% 0.20/0.58      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 0.20/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.20/0.58  thf('88', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['69', '87'])).
% 0.20/0.58  thf('89', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.20/0.58      inference('split', [status(esa)], ['51'])).
% 0.20/0.58  thf('90', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 0.20/0.58  thf('91', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['52', '90'])).
% 0.20/0.58  thf('92', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['50', '91'])).
% 0.20/0.58  thf('93', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.20/0.58      inference('demod', [status(thm)], ['45', '92'])).
% 0.20/0.58  thf('94', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 0.20/0.58      inference('demod', [status(thm)], ['38', '93'])).
% 0.20/0.58  thf('95', plain,
% 0.20/0.58      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.58         (((X36) != (k1_relset_1 @ X36 @ X37 @ X38))
% 0.20/0.58          | (v1_funct_2 @ X38 @ X36 @ X37)
% 0.20/0.58          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.58  thf('96', plain,
% 0.20/0.58      ((((sk_A) != (sk_A))
% 0.20/0.58        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.20/0.58        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.58  thf('97', plain,
% 0.20/0.58      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.20/0.58        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 0.20/0.58      inference('simplify', [status(thm)], ['96'])).
% 0.20/0.58  thf('98', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.20/0.58  thf('99', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 0.20/0.58      inference('clc', [status(thm)], ['97', '98'])).
% 0.20/0.58  thf('100', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['35', '99'])).
% 0.20/0.58  thf('101', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 0.20/0.58      inference('demod', [status(thm)], ['30', '100'])).
% 0.20/0.58  thf('102', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['9', '24'])).
% 0.20/0.58  thf('103', plain,
% 0.20/0.58      (![X7 : $i, X8 : $i]:
% 0.20/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.58  thf('104', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.58  thf('105', plain,
% 0.20/0.58      (![X0 : $i, X2 : $i]:
% 0.20/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('106', plain,
% 0.20/0.58      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ sk_D)
% 0.20/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_C_1) = (sk_D)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['104', '105'])).
% 0.20/0.58  thf('107', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['35', '99'])).
% 0.20/0.58  thf('108', plain,
% 0.20/0.58      (![X5 : $i, X6 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.58  thf('109', plain,
% 0.20/0.58      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['108'])).
% 0.20/0.58  thf('110', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.58  thf('111', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['35', '99'])).
% 0.20/0.58  thf('112', plain,
% 0.20/0.58      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['108'])).
% 0.20/0.58  thf('113', plain, (((k1_xboole_0) = (sk_D))),
% 0.20/0.58      inference('demod', [status(thm)],
% 0.20/0.59                ['106', '107', '109', '110', '111', '112'])).
% 0.20/0.59  thf('114', plain,
% 0.20/0.59      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.59  thf('115', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.20/0.59      inference('demod', [status(thm)], ['45', '92'])).
% 0.20/0.59  thf('116', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['114', '115'])).
% 0.20/0.59  thf('117', plain, (((k1_xboole_0) = (sk_D))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['106', '107', '109', '110', '111', '112'])).
% 0.20/0.59  thf('118', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.59      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.59  thf('119', plain, (((k1_xboole_0) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.20/0.59  thf('120', plain,
% 0.20/0.59      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.59      inference('demod', [status(thm)], ['62', '68'])).
% 0.20/0.59  thf('121', plain, ($false),
% 0.20/0.59      inference('demod', [status(thm)], ['101', '113', '119', '120'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
