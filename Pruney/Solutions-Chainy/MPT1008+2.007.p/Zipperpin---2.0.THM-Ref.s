%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KnpNwTaZq9

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:32 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 742 expanded)
%              Number of leaves         :   47 ( 237 expanded)
%              Depth                    :   20
%              Number of atoms          :  861 (9802 expanded)
%              Number of equality atoms :   74 ( 754 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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

thf('1',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ( X44
        = ( k1_relset_1 @ X44 @ X45 @ X46 ) )
      | ~ ( zip_tseitin_1 @ X46 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X42: $i,X43: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( zip_tseitin_0 @ X47 @ X48 )
      | ( zip_tseitin_1 @ X49 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k11_relat_1 @ X26 @ X27 )
        = k1_xboole_0 )
      | ( r2_hidden @ X27 @ ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k11_relat_1 @ X29 @ X28 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k11_relat_1 @ sk_C @ sk_A ) )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k11_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ X17 @ ( k1_tarski @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X25: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('43',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('45',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('48',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','51','53'])).

thf('55',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('62',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','51','53'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('66',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v5_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('75',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','76'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('78',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KnpNwTaZq9
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.12  % Solved by: fo/fo7.sh
% 0.90/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.12  % done 742 iterations in 0.666s
% 0.90/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.12  % SZS output start Refutation
% 0.90/1.12  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.12  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.90/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.12  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.12  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.90/1.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.12  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.12  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.90/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.12  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.90/1.12  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.90/1.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.12  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.12  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.90/1.12  thf(t62_funct_2, conjecture,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.90/1.12         ( m1_subset_1 @
% 0.90/1.12           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.90/1.12       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.90/1.12         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.90/1.12           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.12    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.12        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.90/1.12            ( m1_subset_1 @
% 0.90/1.12              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.90/1.12          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.90/1.12            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.90/1.12              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.90/1.12    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.90/1.12  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(d1_funct_2, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.12           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.90/1.12             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.90/1.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.12           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.90/1.12             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_1, axiom,
% 0.90/1.12    (![C:$i,B:$i,A:$i]:
% 0.90/1.12     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.90/1.12       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.90/1.12  thf('1', plain,
% 0.90/1.12      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.90/1.12         (~ (v1_funct_2 @ X46 @ X44 @ X45)
% 0.90/1.12          | ((X44) = (k1_relset_1 @ X44 @ X45 @ X46))
% 0.90/1.12          | ~ (zip_tseitin_1 @ X46 @ X45 @ X44))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.12  thf('2', plain,
% 0.90/1.12      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.90/1.12        | ((k1_tarski @ sk_A)
% 0.90/1.12            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.12  thf('3', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ 
% 0.90/1.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.12  thf('4', plain,
% 0.90/1.12      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.90/1.12         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 0.90/1.12          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.12  thf('5', plain,
% 0.90/1.12      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.90/1.12      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.12  thf('6', plain,
% 0.90/1.12      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.90/1.12        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['2', '5'])).
% 0.90/1.12  thf(zf_stmt_2, axiom,
% 0.90/1.12    (![B:$i,A:$i]:
% 0.90/1.12     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.12       ( zip_tseitin_0 @ B @ A ) ))).
% 0.90/1.12  thf('7', plain,
% 0.90/1.12      (![X42 : $i, X43 : $i]:
% 0.90/1.12         ((zip_tseitin_0 @ X42 @ X43) | ((X42) = (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.12  thf('8', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ 
% 0.90/1.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.90/1.12  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.12  thf(zf_stmt_5, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.90/1.12         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.12           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.90/1.12             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.90/1.12  thf('9', plain,
% 0.90/1.12      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.90/1.12         (~ (zip_tseitin_0 @ X47 @ X48)
% 0.90/1.12          | (zip_tseitin_1 @ X49 @ X47 @ X48)
% 0.90/1.12          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47))))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.12  thf('10', plain,
% 0.90/1.12      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.90/1.12        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.12  thf('11', plain,
% 0.90/1.12      ((((sk_B) = (k1_xboole_0))
% 0.90/1.12        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['7', '10'])).
% 0.90/1.12  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('13', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.90/1.12  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['6', '13'])).
% 0.90/1.12  thf(t3_funct_2, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.12       ( ( v1_funct_1 @ A ) & 
% 0.90/1.12         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.90/1.12         ( m1_subset_1 @
% 0.90/1.12           A @ 
% 0.90/1.12           ( k1_zfmisc_1 @
% 0.90/1.12             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.12  thf('15', plain,
% 0.90/1.12      (![X50 : $i]:
% 0.90/1.12         ((m1_subset_1 @ X50 @ 
% 0.90/1.12           (k1_zfmisc_1 @ 
% 0.90/1.12            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 0.90/1.12          | ~ (v1_funct_1 @ X50)
% 0.90/1.12          | ~ (v1_relat_1 @ X50))),
% 0.90/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.90/1.12  thf('16', plain,
% 0.90/1.12      (((m1_subset_1 @ sk_C @ 
% 0.90/1.12         (k1_zfmisc_1 @ 
% 0.90/1.12          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_C))))
% 0.90/1.12        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.12        | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.12      inference('sup+', [status(thm)], ['14', '15'])).
% 0.90/1.12  thf('17', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ 
% 0.90/1.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(cc1_relset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( v1_relat_1 @ C ) ))).
% 0.90/1.12  thf('18', plain,
% 0.90/1.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.90/1.12         ((v1_relat_1 @ X30)
% 0.90/1.12          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.90/1.12      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.12  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.12  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('21', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ 
% 0.90/1.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.90/1.12      inference('demod', [status(thm)], ['16', '19', '20'])).
% 0.90/1.12  thf('22', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['6', '13'])).
% 0.90/1.12  thf(t205_relat_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( v1_relat_1 @ B ) =>
% 0.90/1.12       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.90/1.12         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.90/1.12  thf('23', plain,
% 0.90/1.12      (![X26 : $i, X27 : $i]:
% 0.90/1.12         (((k11_relat_1 @ X26 @ X27) = (k1_xboole_0))
% 0.90/1.12          | (r2_hidden @ X27 @ (k1_relat_1 @ X26))
% 0.90/1.12          | ~ (v1_relat_1 @ X26))),
% 0.90/1.12      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.90/1.12  thf('24', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.90/1.12          | ~ (v1_relat_1 @ sk_C)
% 0.90/1.12          | ((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup+', [status(thm)], ['22', '23'])).
% 0.90/1.12  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.12  thf('26', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.90/1.12          | ((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0)))),
% 0.90/1.12      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.12  thf('27', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['6', '13'])).
% 0.90/1.12  thf(t117_funct_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.12       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.90/1.12         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.90/1.12  thf('28', plain,
% 0.90/1.12      (![X28 : $i, X29 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.90/1.12          | ((k11_relat_1 @ X29 @ X28) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.90/1.12          | ~ (v1_funct_1 @ X29)
% 0.90/1.12          | ~ (v1_relat_1 @ X29))),
% 0.90/1.12      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.90/1.12  thf('29', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.90/1.12          | ~ (v1_relat_1 @ sk_C)
% 0.90/1.12          | ~ (v1_funct_1 @ sk_C)
% 0.90/1.12          | ((k11_relat_1 @ sk_C @ X0) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.12  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.12  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('32', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.90/1.12          | ((k11_relat_1 @ sk_C @ X0) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 0.90/1.12      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.90/1.12  thf('33', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.90/1.12          | ((k11_relat_1 @ sk_C @ X0) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['26', '32'])).
% 0.90/1.12  thf('34', plain,
% 0.90/1.12      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.90/1.12         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('35', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ 
% 0.90/1.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(redefinition_k2_relset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.90/1.12  thf('36', plain,
% 0.90/1.12      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.90/1.12         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 0.90/1.12          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.12  thf('37', plain,
% 0.90/1.12      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.90/1.12      inference('sup-', [status(thm)], ['35', '36'])).
% 0.90/1.12  thf('38', plain,
% 0.90/1.12      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.90/1.12      inference('demod', [status(thm)], ['34', '37'])).
% 0.90/1.12  thf('39', plain,
% 0.90/1.12      ((((k2_relat_1 @ sk_C) != (k11_relat_1 @ sk_C @ sk_A))
% 0.90/1.12        | ((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['33', '38'])).
% 0.90/1.12  thf(d16_relat_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v1_relat_1 @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.90/1.12  thf('40', plain,
% 0.90/1.12      (![X17 : $i, X18 : $i]:
% 0.90/1.12         (((k11_relat_1 @ X17 @ X18) = (k9_relat_1 @ X17 @ (k1_tarski @ X18)))
% 0.90/1.12          | ~ (v1_relat_1 @ X17))),
% 0.90/1.12      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.90/1.12  thf('41', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['6', '13'])).
% 0.90/1.12  thf(t146_relat_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v1_relat_1 @ A ) =>
% 0.90/1.12       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.90/1.12  thf('42', plain,
% 0.90/1.12      (![X25 : $i]:
% 0.90/1.12         (((k9_relat_1 @ X25 @ (k1_relat_1 @ X25)) = (k2_relat_1 @ X25))
% 0.90/1.12          | ~ (v1_relat_1 @ X25))),
% 0.90/1.12      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.90/1.12  thf('43', plain,
% 0.90/1.12      ((((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_C))
% 0.90/1.12        | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.12      inference('sup+', [status(thm)], ['41', '42'])).
% 0.90/1.12  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.12  thf('45', plain,
% 0.90/1.12      (((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['43', '44'])).
% 0.90/1.12  thf('46', plain,
% 0.90/1.12      ((((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 0.90/1.12        | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.12      inference('sup+', [status(thm)], ['40', '45'])).
% 0.90/1.12  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.12  thf('48', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['46', '47'])).
% 0.90/1.12  thf('49', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['46', '47'])).
% 0.90/1.12  thf('50', plain,
% 0.90/1.12      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.90/1.12        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.90/1.12      inference('demod', [status(thm)], ['39', '48', '49'])).
% 0.90/1.12  thf('51', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.90/1.12      inference('simplify', [status(thm)], ['50'])).
% 0.90/1.12  thf(t113_zfmisc_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.90/1.12       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.90/1.12  thf('52', plain,
% 0.90/1.12      (![X11 : $i, X12 : $i]:
% 0.90/1.12         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.90/1.12          | ((X12) != (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.90/1.12  thf('53', plain,
% 0.90/1.12      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.12      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.12  thf('54', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.90/1.12      inference('demod', [status(thm)], ['21', '51', '53'])).
% 0.90/1.12  thf('55', plain,
% 0.90/1.12      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.12      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.12  thf(cc2_relset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.90/1.12  thf('56', plain,
% 0.90/1.12      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.90/1.12         ((v4_relat_1 @ X33 @ X34)
% 0.90/1.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.90/1.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.90/1.12  thf('57', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.90/1.12          | (v4_relat_1 @ X1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['55', '56'])).
% 0.90/1.12  thf('58', plain, (![X0 : $i]: (v4_relat_1 @ sk_C @ X0)),
% 0.90/1.12      inference('sup-', [status(thm)], ['54', '57'])).
% 0.90/1.12  thf(d18_relat_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( v1_relat_1 @ B ) =>
% 0.90/1.12       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.90/1.12  thf('59', plain,
% 0.90/1.12      (![X19 : $i, X20 : $i]:
% 0.90/1.12         (~ (v4_relat_1 @ X19 @ X20)
% 0.90/1.12          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.90/1.12          | ~ (v1_relat_1 @ X19))),
% 0.90/1.12      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.90/1.12  thf('60', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.12  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.12  thf('62', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['6', '13'])).
% 0.90/1.12  thf('63', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.90/1.12      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.90/1.12  thf('64', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.90/1.12      inference('demod', [status(thm)], ['21', '51', '53'])).
% 0.90/1.12  thf('65', plain,
% 0.90/1.12      (![X11 : $i, X12 : $i]:
% 0.90/1.12         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.90/1.12          | ((X11) != (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.90/1.12  thf('66', plain,
% 0.90/1.12      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.90/1.12      inference('simplify', [status(thm)], ['65'])).
% 0.90/1.12  thf('67', plain,
% 0.90/1.12      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.90/1.12         ((v5_relat_1 @ X33 @ X35)
% 0.90/1.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.90/1.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.90/1.12  thf('68', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.90/1.12          | (v5_relat_1 @ X1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['66', '67'])).
% 0.90/1.12  thf('69', plain, (![X0 : $i]: (v5_relat_1 @ sk_C @ X0)),
% 0.90/1.12      inference('sup-', [status(thm)], ['64', '68'])).
% 0.90/1.12  thf(d19_relat_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( v1_relat_1 @ B ) =>
% 0.90/1.12       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.90/1.12  thf('70', plain,
% 0.90/1.12      (![X21 : $i, X22 : $i]:
% 0.90/1.12         (~ (v5_relat_1 @ X21 @ X22)
% 0.90/1.12          | (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 0.90/1.12          | ~ (v1_relat_1 @ X21))),
% 0.90/1.12      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.90/1.12  thf('71', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.12  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.12  thf('73', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.90/1.12      inference('simplify', [status(thm)], ['50'])).
% 0.90/1.12  thf('74', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.12      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.90/1.12  thf(d10_xboole_0, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.12  thf('75', plain,
% 0.90/1.12      (![X0 : $i, X2 : $i]:
% 0.90/1.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.12  thf('76', plain,
% 0.90/1.12      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['74', '75'])).
% 0.90/1.12  thf('77', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['63', '76'])).
% 0.90/1.12  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.90/1.12  thf('78', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X9))),
% 0.90/1.12      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.90/1.12  thf('79', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.12      inference('sup-', [status(thm)], ['77', '78'])).
% 0.90/1.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.12  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.12  thf('81', plain, ($false), inference('demod', [status(thm)], ['79', '80'])).
% 0.90/1.12  
% 0.90/1.12  % SZS output end Refutation
% 0.90/1.12  
% 0.90/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
