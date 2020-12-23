%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONpIeHd2fE

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:22 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 202 expanded)
%              Number of leaves         :   47 (  81 expanded)
%              Depth                    :   20
%              Number of atoms          :  763 (2099 expanded)
%              Number of equality atoms :   45 ( 104 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X40 )
       != X38 )
      | ~ ( r2_hidden @ X41 @ X38 )
      | ( r2_hidden @ ( k4_tarski @ X41 @ ( sk_E @ X41 @ X40 ) ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
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
    ! [X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X26 ) @ ( sk_C @ X26 ) ) @ X26 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X26 ) @ ( sk_C @ X26 ) ) @ X26 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X24 ) @ X25 )
      | ( r2_hidden @ X23 @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X27 ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('53',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('54',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['52','53'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('55',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONpIeHd2fE
% 0.13/0.36  % Computer   : n020.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:08:52 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 213 iterations in 0.157s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i > $i).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.42/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.60  thf(existence_m1_subset_1, axiom,
% 0.42/0.60    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.42/0.60  thf('0', plain, (![X13 : $i]: (m1_subset_1 @ (sk_B @ X13) @ X13)),
% 0.42/0.60      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.42/0.60  thf(t2_subset, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ A @ B ) =>
% 0.42/0.60       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i]:
% 0.42/0.60         ((r2_hidden @ X18 @ X19)
% 0.42/0.60          | (v1_xboole_0 @ X19)
% 0.42/0.60          | ~ (m1_subset_1 @ X18 @ X19))),
% 0.42/0.60      inference('cnf', [status(esa)], [t2_subset])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.60  thf(t61_funct_2, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.60         ( m1_subset_1 @
% 0.42/0.60           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.60       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.60         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.60            ( m1_subset_1 @
% 0.42/0.60              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.60          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.60            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t22_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.42/0.60       ( ( ![D:$i]:
% 0.42/0.60           ( ~( ( r2_hidden @ D @ B ) & 
% 0.42/0.60                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.42/0.60         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.42/0.60         (((k1_relset_1 @ X38 @ X39 @ X40) != (X38))
% 0.42/0.60          | ~ (r2_hidden @ X41 @ X38)
% 0.42/0.60          | (r2_hidden @ (k4_tarski @ X41 @ (sk_E @ X41 @ X40)) @ X40)
% 0.42/0.60          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.42/0.60      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C_1)) @ sk_C_1)
% 0.42/0.60          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.42/0.60          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1)
% 0.42/0.60              != (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.60  thf('6', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(d1_funct_2, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_1, axiom,
% 0.42/0.60    (![C:$i,B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.42/0.60         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.42/0.60          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 0.42/0.60          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.42/0.60        | ((k1_tarski @ sk_A)
% 0.42/0.60            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.60  thf(zf_stmt_2, axiom,
% 0.42/0.60    (![B:$i,A:$i]:
% 0.42/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X43 : $i, X44 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_5, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.42/0.60         (~ (zip_tseitin_0 @ X48 @ X49)
% 0.42/0.60          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 0.42/0.60          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (((zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.42/0.60        | ~ (zip_tseitin_0 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      ((((sk_B_2) = (k1_xboole_0))
% 0.42/0.60        | (zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['9', '12'])).
% 0.42/0.60  thf('14', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('15', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (((k1_tarski @ sk_A)
% 0.42/0.60         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1))),
% 0.42/0.60      inference('demod', [status(thm)], ['8', '15'])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C_1)) @ sk_C_1)
% 0.42/0.60          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.42/0.60          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['5', '16'])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.42/0.60          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C_1)) @ sk_C_1))),
% 0.42/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc2_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.42/0.60         ((v5_relat_1 @ X35 @ X37)
% 0.42/0.60          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.60  thf('21', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.42/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.60  thf(t56_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.42/0.60         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X26 : $i]:
% 0.42/0.60         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X26) @ (sk_C @ X26)) @ X26)
% 0.42/0.60          | ((X26) = (k1_xboole_0))
% 0.42/0.60          | ~ (v1_relat_1 @ X26))),
% 0.42/0.60      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(l3_subset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X14 @ X15)
% 0.42/0.60          | (r2_hidden @ X14 @ X16)
% 0.42/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.42/0.60      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_C_1)
% 0.42/0.60        | ((sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.42/0.60           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['22', '25'])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc1_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( v1_relat_1 @ C ) ))).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.42/0.60         ((v1_relat_1 @ X32)
% 0.42/0.60          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.60  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.42/0.60           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.60      inference('demod', [status(thm)], ['26', '29'])).
% 0.42/0.60  thf(t128_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( r2_hidden @
% 0.42/0.60         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.42/0.60       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.60         (((X9) = (X8))
% 0.42/0.60          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 0.42/0.60               (k2_zfmisc_1 @ (k1_tarski @ X8) @ X11)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1 @ sk_C_1) = (sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X26 : $i]:
% 0.42/0.60         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X26) @ (sk_C @ X26)) @ X26)
% 0.42/0.60          | ((X26) = (k1_xboole_0))
% 0.42/0.60          | ~ (v1_relat_1 @ X26))),
% 0.42/0.60      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.42/0.60        | ((sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | ~ (v1_relat_1 @ sk_C_1)
% 0.42/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['32', '33'])).
% 0.42/0.60  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.42/0.60        | ((sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1))),
% 0.42/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.42/0.60  thf(t20_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ C ) =>
% 0.42/0.60       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.42/0.60         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.42/0.60           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.42/0.60         (~ (r2_hidden @ (k4_tarski @ X23 @ X24) @ X25)
% 0.42/0.60          | (r2_hidden @ X23 @ (k1_relat_1 @ X25))
% 0.42/0.60          | ~ (v1_relat_1 @ X25))),
% 0.42/0.60      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | ~ (v1_relat_1 @ sk_C_1)
% 0.42/0.60        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.60  thf('40', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.42/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf(t172_funct_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.60       ( ![C:$i]:
% 0.42/0.60         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.60           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X27 @ (k1_relat_1 @ X28))
% 0.42/0.60          | (r2_hidden @ (k1_funct_1 @ X28 @ X27) @ X29)
% 0.42/0.60          | ~ (v1_funct_1 @ X28)
% 0.42/0.60          | ~ (v5_relat_1 @ X28 @ X29)
% 0.42/0.60          | ~ (v1_relat_1 @ X28))),
% 0.42/0.60      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.42/0.60  thf('43', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((sk_C_1) = (k1_xboole_0))
% 0.42/0.60          | ~ (v1_relat_1 @ sk_C_1)
% 0.42/0.60          | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ sk_C_1)
% 0.42/0.60          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.60  thf('45', plain, ((v1_funct_1 @ sk_C_1)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((sk_C_1) = (k1_xboole_0))
% 0.42/0.60          | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.42/0.60          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)
% 0.42/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['21', '46'])).
% 0.42/0.60  thf('48', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('49', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.42/0.60      inference('clc', [status(thm)], ['47', '48'])).
% 0.42/0.60  thf('50', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.42/0.60      inference('clc', [status(thm)], ['47', '48'])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.42/0.60          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.42/0.60             k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['18', '49', '50'])).
% 0.42/0.60  thf('52', plain,
% 0.42/0.60      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.42/0.60        | (r2_hidden @ 
% 0.42/0.60           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.42/0.60            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.42/0.60           k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['2', '51'])).
% 0.42/0.60  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.42/0.60  thf('53', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.42/0.60  thf('54', plain,
% 0.42/0.60      ((r2_hidden @ 
% 0.42/0.60        (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.42/0.60         (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.42/0.60        k1_xboole_0)),
% 0.42/0.60      inference('clc', [status(thm)], ['52', '53'])).
% 0.42/0.60  thf(t7_ordinal1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.60  thf('55', plain,
% 0.42/0.60      (![X30 : $i, X31 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X30 @ X31) | ~ (r1_tarski @ X31 @ X30))),
% 0.42/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.60  thf('56', plain,
% 0.42/0.60      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.42/0.60          (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.42/0.60           (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.42/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.60  thf('57', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.42/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.60  thf('58', plain, ($false), inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
