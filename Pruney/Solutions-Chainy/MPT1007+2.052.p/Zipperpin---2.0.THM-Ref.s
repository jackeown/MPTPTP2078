%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OvOPGwDTPN

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:22 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 206 expanded)
%              Number of leaves         :   49 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  780 (2116 expanded)
%              Number of equality atoms :   47 ( 106 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( sk_B @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X41 )
       != X39 )
      | ~ ( r2_hidden @ X42 @ X39 )
      | ( r2_hidden @ ( k4_tarski @ X42 @ ( sk_E @ X42 @ X41 ) ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C_1 )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_1 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_0 @ X49 @ X50 )
      | ( zip_tseitin_1 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C_1 ) ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v5_relat_1 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X27: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X27 ) @ ( sk_C @ X27 ) ) @ X27 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('28',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 = X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X9 ) @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X27: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X27 ) @ ( sk_C @ X27 ) ) @ X27 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('34',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X25 ) @ X26 )
      | ( r2_hidden @ X24 @ ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('39',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('41',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X29 @ X28 ) @ X30 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('45',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','51'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('53',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['52','55'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('57',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r1_tarski @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('58',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OvOPGwDTPN
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.61  % Solved by: fo/fo7.sh
% 0.35/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.61  % done 213 iterations in 0.159s
% 0.35/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.61  % SZS output start Refutation
% 0.35/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.61  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.35/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.61  thf(sk_C_type, type, sk_C: $i > $i).
% 0.35/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.61  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.35/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.35/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.61  thf(existence_m1_subset_1, axiom,
% 0.35/0.61    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.35/0.61  thf('0', plain, (![X14 : $i]: (m1_subset_1 @ (sk_B @ X14) @ X14)),
% 0.35/0.61      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.35/0.61  thf(t2_subset, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.61       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.61  thf('1', plain,
% 0.35/0.61      (![X19 : $i, X20 : $i]:
% 0.35/0.61         ((r2_hidden @ X19 @ X20)
% 0.35/0.61          | (v1_xboole_0 @ X20)
% 0.35/0.61          | ~ (m1_subset_1 @ X19 @ X20))),
% 0.35/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.61  thf('2', plain,
% 0.35/0.61      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.61  thf(t61_funct_2, conjecture,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.61         ( m1_subset_1 @
% 0.35/0.61           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.61       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.61         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.35/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.61            ( m1_subset_1 @
% 0.35/0.61              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.61          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.61            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.35/0.61    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.35/0.61  thf('3', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(t22_relset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.35/0.61       ( ( ![D:$i]:
% 0.35/0.61           ( ~( ( r2_hidden @ D @ B ) & 
% 0.35/0.61                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.35/0.61         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.35/0.61  thf('4', plain,
% 0.35/0.61      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.35/0.61         (((k1_relset_1 @ X39 @ X40 @ X41) != (X39))
% 0.35/0.61          | ~ (r2_hidden @ X42 @ X39)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X42 @ (sk_E @ X42 @ X41)) @ X41)
% 0.35/0.61          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.35/0.61      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.35/0.61  thf('5', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C_1)) @ sk_C_1)
% 0.35/0.61          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.35/0.61          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1)
% 0.35/0.61              != (k1_tarski @ sk_A)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.61  thf('6', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(d1_funct_2, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_1, axiom,
% 0.35/0.61    (![C:$i,B:$i,A:$i]:
% 0.35/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.61  thf('7', plain,
% 0.35/0.61      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.35/0.61         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.35/0.61          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 0.35/0.61          | ~ (zip_tseitin_1 @ X48 @ X47 @ X46))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.61  thf('8', plain,
% 0.35/0.61      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.35/0.61        | ((k1_tarski @ sk_A)
% 0.35/0.61            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.61  thf(zf_stmt_2, axiom,
% 0.35/0.61    (![B:$i,A:$i]:
% 0.35/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.61  thf('9', plain,
% 0.35/0.61      (![X44 : $i, X45 : $i]:
% 0.35/0.61         ((zip_tseitin_0 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.61  thf('10', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.61  thf(zf_stmt_5, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.61  thf('11', plain,
% 0.35/0.61      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.35/0.61         (~ (zip_tseitin_0 @ X49 @ X50)
% 0.35/0.61          | (zip_tseitin_1 @ X51 @ X49 @ X50)
% 0.35/0.61          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.61  thf('12', plain,
% 0.35/0.61      (((zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.35/0.61        | ~ (zip_tseitin_0 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.61  thf('13', plain,
% 0.35/0.61      ((((sk_B_2) = (k1_xboole_0))
% 0.35/0.61        | (zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['9', '12'])).
% 0.35/0.61  thf('14', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('15', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.35/0.61      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.35/0.61  thf('16', plain,
% 0.35/0.61      (((k1_tarski @ sk_A)
% 0.35/0.61         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1))),
% 0.35/0.61      inference('demod', [status(thm)], ['8', '15'])).
% 0.35/0.61  thf('17', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C_1)) @ sk_C_1)
% 0.35/0.61          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.35/0.61          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['5', '16'])).
% 0.35/0.61  thf('18', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C_1)) @ sk_C_1))),
% 0.35/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.61  thf('19', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(cc2_relset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.61  thf('20', plain,
% 0.35/0.61      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.35/0.61         ((v5_relat_1 @ X36 @ X38)
% 0.35/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.35/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.61  thf('21', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.35/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.61  thf(t56_relat_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( v1_relat_1 @ A ) =>
% 0.35/0.61       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.35/0.61         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.61  thf('22', plain,
% 0.35/0.61      (![X27 : $i]:
% 0.35/0.61         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X27) @ (sk_C @ X27)) @ X27)
% 0.35/0.61          | ((X27) = (k1_xboole_0))
% 0.35/0.61          | ~ (v1_relat_1 @ X27))),
% 0.35/0.61      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.35/0.61  thf('23', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(l3_subset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.35/0.61  thf('24', plain,
% 0.35/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X15 @ X16)
% 0.35/0.61          | (r2_hidden @ X15 @ X17)
% 0.35/0.61          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.35/0.61      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.35/0.61  thf('25', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.35/0.61          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.61  thf('26', plain,
% 0.35/0.61      ((~ (v1_relat_1 @ sk_C_1)
% 0.35/0.61        | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.61        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.35/0.61           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['22', '25'])).
% 0.35/0.61  thf('27', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(cc1_relset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.61       ( v1_relat_1 @ C ) ))).
% 0.35/0.61  thf('28', plain,
% 0.35/0.61      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.61         ((v1_relat_1 @ X33)
% 0.35/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.35/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.61  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.61  thf('30', plain,
% 0.35/0.61      ((((sk_C_1) = (k1_xboole_0))
% 0.35/0.61        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.35/0.61           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.61      inference('demod', [status(thm)], ['26', '29'])).
% 0.35/0.61  thf(t128_zfmisc_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.61     ( ( r2_hidden @
% 0.35/0.61         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.35/0.61       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.35/0.61  thf('31', plain,
% 0.35/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.61         (((X10) = (X9))
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ 
% 0.35/0.61               (k2_zfmisc_1 @ (k1_tarski @ X9) @ X12)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.35/0.61  thf('32', plain,
% 0.35/0.61      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1 @ sk_C_1) = (sk_A)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.61  thf('33', plain,
% 0.35/0.61      (![X27 : $i]:
% 0.35/0.61         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X27) @ (sk_C @ X27)) @ X27)
% 0.35/0.61          | ((X27) = (k1_xboole_0))
% 0.35/0.61          | ~ (v1_relat_1 @ X27))),
% 0.35/0.61      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.35/0.61  thf('34', plain,
% 0.35/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.35/0.61        | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.61        | ~ (v1_relat_1 @ sk_C_1)
% 0.35/0.61        | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.35/0.61  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.61  thf('36', plain,
% 0.35/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.35/0.61        | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.61        | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.35/0.61  thf('37', plain,
% 0.35/0.61      ((((sk_C_1) = (k1_xboole_0))
% 0.35/0.61        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1))),
% 0.35/0.61      inference('simplify', [status(thm)], ['36'])).
% 0.35/0.61  thf(t20_relat_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( v1_relat_1 @ C ) =>
% 0.35/0.61       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.35/0.61         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.35/0.61           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.35/0.61  thf('38', plain,
% 0.35/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.61         (~ (r2_hidden @ (k4_tarski @ X24 @ X25) @ X26)
% 0.35/0.61          | (r2_hidden @ X24 @ (k1_relat_1 @ X26))
% 0.35/0.61          | ~ (v1_relat_1 @ X26))),
% 0.35/0.61      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.35/0.61  thf('39', plain,
% 0.35/0.61      ((((sk_C_1) = (k1_xboole_0))
% 0.35/0.61        | ~ (v1_relat_1 @ sk_C_1)
% 0.35/0.61        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.61  thf('40', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.61  thf('41', plain,
% 0.35/0.61      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.35/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.61  thf(t172_funct_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.61       ( ![C:$i]:
% 0.35/0.61         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.61           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.35/0.61  thf('42', plain,
% 0.35/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.35/0.61          | (r2_hidden @ (k1_funct_1 @ X29 @ X28) @ X30)
% 0.35/0.61          | ~ (v1_funct_1 @ X29)
% 0.35/0.61          | ~ (v5_relat_1 @ X29 @ X30)
% 0.35/0.61          | ~ (v1_relat_1 @ X29))),
% 0.35/0.61      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.35/0.61  thf('43', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (((sk_C_1) = (k1_xboole_0))
% 0.35/0.61          | ~ (v1_relat_1 @ sk_C_1)
% 0.35/0.61          | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ sk_C_1)
% 0.35/0.61          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.35/0.61  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.61  thf('45', plain, ((v1_funct_1 @ sk_C_1)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('46', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (((sk_C_1) = (k1_xboole_0))
% 0.35/0.61          | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.35/0.61          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.35/0.61  thf('47', plain,
% 0.35/0.61      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)
% 0.35/0.61        | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['21', '46'])).
% 0.35/0.61  thf('48', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('49', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.35/0.61      inference('clc', [status(thm)], ['47', '48'])).
% 0.35/0.61  thf('50', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.35/0.61      inference('clc', [status(thm)], ['47', '48'])).
% 0.35/0.61  thf('51', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.35/0.61             k1_xboole_0))),
% 0.35/0.61      inference('demod', [status(thm)], ['18', '49', '50'])).
% 0.35/0.61  thf('52', plain,
% 0.35/0.61      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.35/0.61        | (r2_hidden @ 
% 0.35/0.61           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.35/0.61            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.35/0.61           k1_xboole_0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['2', '51'])).
% 0.35/0.61  thf(t69_enumset1, axiom,
% 0.35/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.61  thf('53', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.35/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.61  thf(fc3_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.35/0.61  thf('54', plain,
% 0.35/0.61      (![X7 : $i, X8 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X7 @ X8))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.35/0.61  thf('55', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.35/0.61  thf('56', plain,
% 0.35/0.61      ((r2_hidden @ 
% 0.35/0.61        (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.35/0.61         (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.35/0.61        k1_xboole_0)),
% 0.35/0.61      inference('clc', [status(thm)], ['52', '55'])).
% 0.35/0.61  thf(t7_ordinal1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.61  thf('57', plain,
% 0.35/0.61      (![X31 : $i, X32 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X31 @ X32) | ~ (r1_tarski @ X32 @ X31))),
% 0.35/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.61  thf('58', plain,
% 0.35/0.61      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.35/0.61          (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.35/0.61           (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.35/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.61  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.35/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.61  thf('60', plain, ($false), inference('demod', [status(thm)], ['58', '59'])).
% 0.35/0.61  
% 0.35/0.61  % SZS output end Refutation
% 0.35/0.61  
% 0.35/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
