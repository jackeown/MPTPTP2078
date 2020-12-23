%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yPj14N9dpx

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:42 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  238 (1773 expanded)
%              Number of leaves         :   48 ( 528 expanded)
%              Depth                    :   31
%              Number of atoms          : 1920 (27040 expanded)
%              Number of equality atoms :  137 (1435 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k9_relat_1 @ X18 @ X19 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X18 ) @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('3',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( ( k9_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['6','7'])).

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

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('34',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('53',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('54',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('55',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('58',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('60',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['61'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('63',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k9_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['60','64'])).

thf('66',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('76',plain,(
    ! [X9: $i] :
      ( ( ( k10_relat_1 @ X9 @ ( k2_relat_1 @ X9 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('77',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('79',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = sk_B )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['66','80'])).

thf('82',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('86',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
      = sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','81','82','83','84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('88',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('89',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['49'])).

thf('90',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','29','30','31'])).

thf('96',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('99',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('100',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('101',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('106',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('107',plain,(
    ! [X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('109',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('113',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','113'])).

thf('115',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('118',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('119',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('122',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['120','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['98','126'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['97','127'])).

thf('129',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('130',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('132',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('134',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('135',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('136',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('137',plain,(
    ! [X40: $i] :
      ( ( v1_funct_2 @ X40 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['134','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['132','144'])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['6','7'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['94','150'])).

thf('152',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['49'])).

thf('153',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['93','151','152'])).

thf('154',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['86','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','154','155','156','157'])).

thf('159',plain,(
    ! [X9: $i] :
      ( ( ( k10_relat_1 @ X9 @ ( k2_relat_1 @ X9 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('160',plain,
    ( ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','164'])).

thf('166',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = sk_B )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['66','80'])).

thf('167',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['93','151','152'])).

thf('168',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['165','168','169','170','171'])).

thf('173',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('174',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','154','155','156','157'])).

thf('176',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['49'])).

thf('178',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['93','151','152'])).

thf('179',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['177','178'])).

thf('180',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['176','179'])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','180'])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    $false ),
    inference(demod,[status(thm)],['185','186','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yPj14N9dpx
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:45:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.72/1.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.92  % Solved by: fo/fo7.sh
% 1.72/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.92  % done 1826 iterations in 1.458s
% 1.72/1.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.92  % SZS output start Refutation
% 1.72/1.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.72/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.72/1.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.72/1.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.72/1.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.72/1.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.72/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.72/1.92  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.72/1.92  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.72/1.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.72/1.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.72/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.72/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.72/1.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.72/1.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.72/1.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.72/1.92  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.72/1.92  thf(sk_C_type, type, sk_C: $i).
% 1.72/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.92  thf(dt_k2_funct_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.92       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.72/1.92         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.72/1.92  thf('0', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf('1', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf(t154_funct_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.72/1.92       ( ( v2_funct_1 @ B ) =>
% 1.72/1.92         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.72/1.92  thf('2', plain,
% 1.72/1.92      (![X18 : $i, X19 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X18)
% 1.72/1.92          | ((k9_relat_1 @ X18 @ X19)
% 1.72/1.92              = (k10_relat_1 @ (k2_funct_1 @ X18) @ X19))
% 1.72/1.92          | ~ (v1_funct_1 @ X18)
% 1.72/1.92          | ~ (v1_relat_1 @ X18))),
% 1.72/1.92      inference('cnf', [status(esa)], [t154_funct_1])).
% 1.72/1.92  thf('3', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf(t31_funct_2, conjecture,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.92       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.72/1.92         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.72/1.92           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.72/1.92           ( m1_subset_1 @
% 1.72/1.92             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.72/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.92    (~( ![A:$i,B:$i,C:$i]:
% 1.72/1.92        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.92            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.92          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.72/1.92            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.72/1.92              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.72/1.92              ( m1_subset_1 @
% 1.72/1.92                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.72/1.92    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.72/1.92  thf('4', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(redefinition_k2_relset_1, axiom,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.72/1.92  thf('5', plain,
% 1.72/1.92      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.72/1.92         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 1.72/1.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.72/1.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.72/1.92  thf('6', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.72/1.92      inference('sup-', [status(thm)], ['4', '5'])).
% 1.72/1.92  thf('7', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('8', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.72/1.92      inference('sup+', [status(thm)], ['6', '7'])).
% 1.72/1.92  thf('9', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf(t55_funct_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.92       ( ( v2_funct_1 @ A ) =>
% 1.72/1.92         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.72/1.92           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.72/1.92  thf('10', plain,
% 1.72/1.92      (![X22 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X22)
% 1.72/1.92          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 1.72/1.92          | ~ (v1_funct_1 @ X22)
% 1.72/1.92          | ~ (v1_relat_1 @ X22))),
% 1.72/1.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.72/1.92  thf(t146_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.72/1.92  thf('11', plain,
% 1.72/1.92      (![X8 : $i]:
% 1.72/1.92         (((k9_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (k2_relat_1 @ X8))
% 1.72/1.92          | ~ (v1_relat_1 @ X8))),
% 1.72/1.92      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.72/1.92  thf('12', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.72/1.92            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['10', '11'])).
% 1.72/1.92  thf('13', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.72/1.92              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['9', '12'])).
% 1.72/1.92  thf('14', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.72/1.92            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['13'])).
% 1.72/1.92  thf('15', plain,
% 1.72/1.92      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.72/1.92          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92        | ~ (v2_funct_1 @ sk_C))),
% 1.72/1.92      inference('sup+', [status(thm)], ['8', '14'])).
% 1.72/1.92  thf('16', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.72/1.92      inference('sup+', [status(thm)], ['6', '7'])).
% 1.72/1.92  thf(d1_funct_2, axiom,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.72/1.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.72/1.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.72/1.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.72/1.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.72/1.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.72/1.92  thf(zf_stmt_1, axiom,
% 1.72/1.92    (![B:$i,A:$i]:
% 1.72/1.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.72/1.92       ( zip_tseitin_0 @ B @ A ) ))).
% 1.72/1.92  thf('17', plain,
% 1.72/1.92      (![X32 : $i, X33 : $i]:
% 1.72/1.92         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.72/1.92  thf('18', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf('19', plain,
% 1.72/1.92      (![X22 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X22)
% 1.72/1.92          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 1.72/1.92          | ~ (v1_funct_1 @ X22)
% 1.72/1.92          | ~ (v1_relat_1 @ X22))),
% 1.72/1.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.72/1.92  thf(t64_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.72/1.92           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.72/1.92         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.72/1.92  thf('20', plain,
% 1.72/1.92      (![X10 : $i]:
% 1.72/1.92         (((k1_relat_1 @ X10) != (k1_xboole_0))
% 1.72/1.92          | ((X10) = (k1_xboole_0))
% 1.72/1.92          | ~ (v1_relat_1 @ X10))),
% 1.72/1.92      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.72/1.92  thf('21', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.72/1.92          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['19', '20'])).
% 1.72/1.92  thf('22', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['18', '21'])).
% 1.72/1.92  thf('23', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['22'])).
% 1.72/1.92  thf('24', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.92         (((k2_relat_1 @ X1) != (X0))
% 1.72/1.92          | (zip_tseitin_0 @ X0 @ X2)
% 1.72/1.92          | ~ (v1_relat_1 @ X1)
% 1.72/1.92          | ~ (v1_funct_1 @ X1)
% 1.72/1.92          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 1.72/1.92          | ~ (v2_funct_1 @ X1))),
% 1.72/1.92      inference('sup-', [status(thm)], ['17', '23'])).
% 1.72/1.92  thf('25', plain,
% 1.72/1.92      (![X1 : $i, X2 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X1)
% 1.72/1.92          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 1.72/1.92          | ~ (v1_funct_1 @ X1)
% 1.72/1.92          | ~ (v1_relat_1 @ X1)
% 1.72/1.92          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 1.72/1.92      inference('simplify', [status(thm)], ['24'])).
% 1.72/1.92  thf('26', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((zip_tseitin_0 @ sk_B @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ sk_C)
% 1.72/1.92          | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 1.72/1.92          | ~ (v2_funct_1 @ sk_C))),
% 1.72/1.92      inference('sup+', [status(thm)], ['16', '25'])).
% 1.72/1.92  thf('27', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(cc1_relset_1, axiom,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.92       ( v1_relat_1 @ C ) ))).
% 1.72/1.92  thf('28', plain,
% 1.72/1.92      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.72/1.92         ((v1_relat_1 @ X23)
% 1.72/1.92          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.72/1.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.72/1.92  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('31', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('32', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 1.72/1.92      inference('demod', [status(thm)], ['26', '29', '30', '31'])).
% 1.72/1.92  thf('33', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.72/1.92  thf(zf_stmt_3, axiom,
% 1.72/1.92    (![C:$i,B:$i,A:$i]:
% 1.72/1.92     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.72/1.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.72/1.92  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.72/1.92  thf(zf_stmt_5, axiom,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.92       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.72/1.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.72/1.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.72/1.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.72/1.92  thf('34', plain,
% 1.72/1.92      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.72/1.92         (~ (zip_tseitin_0 @ X37 @ X38)
% 1.72/1.92          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 1.72/1.92          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.72/1.92  thf('35', plain,
% 1.72/1.92      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['33', '34'])).
% 1.72/1.92  thf('36', plain,
% 1.72/1.92      ((((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 1.72/1.92        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['32', '35'])).
% 1.72/1.92  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('38', plain,
% 1.72/1.92      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.72/1.92         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 1.72/1.92          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 1.72/1.92          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.72/1.92  thf('39', plain,
% 1.72/1.92      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.72/1.92        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['37', '38'])).
% 1.72/1.92  thf('40', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(redefinition_k1_relset_1, axiom,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.72/1.92  thf('41', plain,
% 1.72/1.92      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.72/1.92         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 1.72/1.92          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.72/1.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.72/1.92  thf('42', plain,
% 1.72/1.92      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.72/1.92      inference('sup-', [status(thm)], ['40', '41'])).
% 1.72/1.92  thf('43', plain,
% 1.72/1.92      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.72/1.92      inference('demod', [status(thm)], ['39', '42'])).
% 1.72/1.92  thf('44', plain,
% 1.72/1.92      ((((k2_funct_1 @ sk_C) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['36', '43'])).
% 1.72/1.92  thf('45', plain,
% 1.72/1.92      (![X32 : $i, X33 : $i]:
% 1.72/1.92         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.72/1.92  thf(t113_zfmisc_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.72/1.92       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.72/1.92  thf('46', plain,
% 1.72/1.92      (![X4 : $i, X5 : $i]:
% 1.72/1.92         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 1.72/1.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.72/1.92  thf('47', plain,
% 1.72/1.92      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['46'])).
% 1.72/1.92  thf('48', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.92         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.72/1.92      inference('sup+', [status(thm)], ['45', '47'])).
% 1.72/1.92  thf('49', plain,
% 1.72/1.92      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.72/1.92        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.72/1.92        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('50', plain,
% 1.72/1.92      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('split', [status(esa)], ['49'])).
% 1.72/1.92  thf('51', plain,
% 1.72/1.92      ((![X0 : $i]:
% 1.72/1.92          (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.72/1.92           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['48', '50'])).
% 1.72/1.92  thf('52', plain,
% 1.72/1.92      ((![X0 : $i]:
% 1.72/1.92          (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.72/1.92           | ((sk_A) = (k1_relat_1 @ sk_C))
% 1.72/1.92           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['44', '51'])).
% 1.72/1.92  thf(dt_k2_subset_1, axiom,
% 1.72/1.92    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.72/1.92  thf('53', plain,
% 1.72/1.92      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.72/1.92  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.72/1.92  thf('54', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 1.72/1.92      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.72/1.92  thf('55', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 1.72/1.92      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.92  thf('56', plain,
% 1.72/1.92      ((![X0 : $i]:
% 1.72/1.92          (((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_0 @ sk_B @ X0)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('demod', [status(thm)], ['52', '55'])).
% 1.72/1.92  thf('57', plain,
% 1.72/1.92      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['33', '34'])).
% 1.72/1.92  thf('58', plain,
% 1.72/1.92      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['56', '57'])).
% 1.72/1.92  thf('59', plain,
% 1.72/1.92      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.72/1.92      inference('demod', [status(thm)], ['39', '42'])).
% 1.72/1.92  thf('60', plain,
% 1.72/1.92      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('clc', [status(thm)], ['58', '59'])).
% 1.72/1.92  thf(d10_xboole_0, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.72/1.92  thf('61', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.72/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.72/1.92  thf('62', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.72/1.92      inference('simplify', [status(thm)], ['61'])).
% 1.72/1.92  thf(t177_funct_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.92       ( ![B:$i]:
% 1.72/1.92         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 1.72/1.92           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 1.72/1.92             ( B ) ) ) ) ))).
% 1.72/1.92  thf('63', plain,
% 1.72/1.92      (![X20 : $i, X21 : $i]:
% 1.72/1.92         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 1.72/1.92          | ((k9_relat_1 @ (k2_funct_1 @ X21) @ (k9_relat_1 @ X21 @ X20))
% 1.72/1.92              = (X20))
% 1.72/1.92          | ~ (v2_funct_1 @ X21)
% 1.72/1.92          | ~ (v1_funct_1 @ X21)
% 1.72/1.92          | ~ (v1_relat_1 @ X21))),
% 1.72/1.92      inference('cnf', [status(esa)], [t177_funct_1])).
% 1.72/1.92  thf('64', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.72/1.92              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['62', '63'])).
% 1.72/1.92  thf('65', plain,
% 1.72/1.92      (((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A))
% 1.72/1.92           = (k1_relat_1 @ sk_C))
% 1.72/1.92         | ~ (v2_funct_1 @ sk_C)
% 1.72/1.92         | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92         | ~ (v1_relat_1 @ sk_C)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('sup+', [status(thm)], ['60', '64'])).
% 1.72/1.92  thf('66', plain,
% 1.72/1.92      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('clc', [status(thm)], ['58', '59'])).
% 1.72/1.92  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.72/1.92      inference('simplify', [status(thm)], ['61'])).
% 1.72/1.92  thf('68', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.72/1.92      inference('sup+', [status(thm)], ['6', '7'])).
% 1.72/1.92  thf(t147_funct_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.72/1.92       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.72/1.92         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.72/1.92  thf('69', plain,
% 1.72/1.92      (![X16 : $i, X17 : $i]:
% 1.72/1.92         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 1.72/1.92          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 1.72/1.92          | ~ (v1_funct_1 @ X17)
% 1.72/1.92          | ~ (v1_relat_1 @ X17))),
% 1.72/1.92      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.72/1.92  thf('70', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (r1_tarski @ X0 @ sk_B)
% 1.72/1.92          | ~ (v1_relat_1 @ sk_C)
% 1.72/1.92          | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['68', '69'])).
% 1.72/1.92  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('73', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (r1_tarski @ X0 @ sk_B)
% 1.72/1.92          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.72/1.92      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.72/1.92  thf('74', plain,
% 1.72/1.92      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 1.72/1.92      inference('sup-', [status(thm)], ['67', '73'])).
% 1.72/1.92  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.72/1.92      inference('sup+', [status(thm)], ['6', '7'])).
% 1.72/1.92  thf(t169_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.72/1.92  thf('76', plain,
% 1.72/1.92      (![X9 : $i]:
% 1.72/1.92         (((k10_relat_1 @ X9 @ (k2_relat_1 @ X9)) = (k1_relat_1 @ X9))
% 1.72/1.92          | ~ (v1_relat_1 @ X9))),
% 1.72/1.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.72/1.92  thf('77', plain,
% 1.72/1.92      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_C))),
% 1.72/1.92      inference('sup+', [status(thm)], ['75', '76'])).
% 1.72/1.92  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('79', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['77', '78'])).
% 1.72/1.92  thf('80', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['74', '79'])).
% 1.72/1.92  thf('81', plain,
% 1.72/1.92      ((((k9_relat_1 @ sk_C @ sk_A) = (sk_B)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('sup+', [status(thm)], ['66', '80'])).
% 1.72/1.92  thf('82', plain,
% 1.72/1.92      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('clc', [status(thm)], ['58', '59'])).
% 1.72/1.92  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('86', plain,
% 1.72/1.92      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) = (sk_A)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('demod', [status(thm)], ['65', '81', '82', '83', '84', '85'])).
% 1.72/1.92  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('88', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf('89', plain,
% 1.72/1.92      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.72/1.92         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.72/1.92      inference('split', [status(esa)], ['49'])).
% 1.72/1.92  thf('90', plain,
% 1.72/1.92      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.72/1.92         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['88', '89'])).
% 1.72/1.92  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('92', plain,
% 1.72/1.92      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.72/1.92      inference('demod', [status(thm)], ['90', '91'])).
% 1.72/1.92  thf('93', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['87', '92'])).
% 1.72/1.92  thf('94', plain,
% 1.72/1.92      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.72/1.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.72/1.92      inference('split', [status(esa)], ['49'])).
% 1.72/1.92  thf('95', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 1.72/1.92      inference('demod', [status(thm)], ['26', '29', '30', '31'])).
% 1.72/1.92  thf('96', plain,
% 1.72/1.92      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.72/1.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.72/1.92      inference('split', [status(esa)], ['49'])).
% 1.72/1.92  thf('97', plain,
% 1.72/1.92      ((![X0 : $i]:
% 1.72/1.92          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 1.72/1.92           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.72/1.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['95', '96'])).
% 1.72/1.92  thf('98', plain,
% 1.72/1.92      (![X32 : $i, X33 : $i]:
% 1.72/1.92         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.72/1.92  thf('99', plain,
% 1.72/1.92      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['46'])).
% 1.72/1.92  thf('100', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 1.72/1.92      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.92  thf('101', plain,
% 1.72/1.92      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.72/1.92         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 1.72/1.92          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.72/1.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.72/1.92  thf('102', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.72/1.92           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['100', '101'])).
% 1.72/1.92  thf('103', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.72/1.92           = (k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['99', '102'])).
% 1.72/1.92  thf('104', plain,
% 1.72/1.92      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['46'])).
% 1.72/1.92  thf('105', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.72/1.92           = (k1_relat_1 @ k1_xboole_0))),
% 1.72/1.92      inference('demod', [status(thm)], ['103', '104'])).
% 1.72/1.92  thf(t71_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.72/1.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.72/1.92  thf('106', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 1.72/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.72/1.92  thf('107', plain,
% 1.72/1.92      (![X10 : $i]:
% 1.72/1.92         (((k1_relat_1 @ X10) != (k1_xboole_0))
% 1.72/1.92          | ((X10) = (k1_xboole_0))
% 1.72/1.92          | ~ (v1_relat_1 @ X10))),
% 1.72/1.92      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.72/1.92  thf('108', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((X0) != (k1_xboole_0))
% 1.72/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.72/1.92          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['106', '107'])).
% 1.72/1.92  thf(fc4_funct_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.72/1.92       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.72/1.92  thf('109', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 1.72/1.92      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.72/1.92  thf('110', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 1.72/1.92      inference('demod', [status(thm)], ['108', '109'])).
% 1.72/1.92  thf('111', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['110'])).
% 1.72/1.92  thf('112', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 1.72/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.72/1.92  thf('113', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['111', '112'])).
% 1.72/1.92  thf('114', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.72/1.92      inference('demod', [status(thm)], ['105', '113'])).
% 1.72/1.92  thf('115', plain,
% 1.72/1.92      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.72/1.92         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 1.72/1.92          | (v1_funct_2 @ X36 @ X34 @ X35)
% 1.72/1.92          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.72/1.92  thf('116', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k1_xboole_0) != (k1_xboole_0))
% 1.72/1.92          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.72/1.92          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.72/1.92      inference('sup-', [status(thm)], ['114', '115'])).
% 1.72/1.92  thf('117', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 1.72/1.92      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.92  thf('118', plain,
% 1.72/1.92      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['46'])).
% 1.72/1.92  thf('119', plain,
% 1.72/1.92      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.72/1.92         (~ (zip_tseitin_0 @ X37 @ X38)
% 1.72/1.92          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 1.72/1.92          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.72/1.92  thf('120', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.72/1.92          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 1.72/1.92          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 1.72/1.92      inference('sup-', [status(thm)], ['118', '119'])).
% 1.72/1.92  thf('121', plain,
% 1.72/1.92      (![X32 : $i, X33 : $i]:
% 1.72/1.92         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.72/1.92  thf('122', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 1.72/1.92      inference('simplify', [status(thm)], ['121'])).
% 1.72/1.92  thf('123', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.72/1.92          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.72/1.92      inference('demod', [status(thm)], ['120', '122'])).
% 1.72/1.92  thf('124', plain,
% 1.72/1.92      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.72/1.92      inference('sup-', [status(thm)], ['117', '123'])).
% 1.72/1.92  thf('125', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k1_xboole_0) != (k1_xboole_0))
% 1.72/1.92          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.72/1.92      inference('demod', [status(thm)], ['116', '124'])).
% 1.72/1.92  thf('126', plain,
% 1.72/1.92      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.72/1.92      inference('simplify', [status(thm)], ['125'])).
% 1.72/1.92  thf('127', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.92         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.72/1.92      inference('sup+', [status(thm)], ['98', '126'])).
% 1.72/1.92  thf('128', plain,
% 1.72/1.92      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 1.72/1.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.72/1.92      inference('clc', [status(thm)], ['97', '127'])).
% 1.72/1.92  thf('129', plain,
% 1.72/1.92      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['33', '34'])).
% 1.72/1.92  thf('130', plain,
% 1.72/1.92      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 1.72/1.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['128', '129'])).
% 1.72/1.92  thf('131', plain,
% 1.72/1.92      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.72/1.92      inference('demod', [status(thm)], ['39', '42'])).
% 1.72/1.92  thf('132', plain,
% 1.72/1.92      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.72/1.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['130', '131'])).
% 1.72/1.92  thf('133', plain,
% 1.72/1.92      (![X22 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X22)
% 1.72/1.92          | ((k1_relat_1 @ X22) = (k2_relat_1 @ (k2_funct_1 @ X22)))
% 1.72/1.92          | ~ (v1_funct_1 @ X22)
% 1.72/1.92          | ~ (v1_relat_1 @ X22))),
% 1.72/1.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.72/1.92  thf('134', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf('135', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf('136', plain,
% 1.72/1.92      (![X22 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X22)
% 1.72/1.92          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 1.72/1.92          | ~ (v1_funct_1 @ X22)
% 1.72/1.92          | ~ (v1_relat_1 @ X22))),
% 1.72/1.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.72/1.92  thf(t3_funct_2, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.92       ( ( v1_funct_1 @ A ) & 
% 1.72/1.92         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.72/1.92         ( m1_subset_1 @
% 1.72/1.92           A @ 
% 1.72/1.92           ( k1_zfmisc_1 @
% 1.72/1.92             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.72/1.92  thf('137', plain,
% 1.72/1.92      (![X40 : $i]:
% 1.72/1.92         ((v1_funct_2 @ X40 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))
% 1.72/1.92          | ~ (v1_funct_1 @ X40)
% 1.72/1.92          | ~ (v1_relat_1 @ X40))),
% 1.72/1.92      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.72/1.92  thf('138', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.72/1.92           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['136', '137'])).
% 1.72/1.92  thf('139', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.72/1.92             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['135', '138'])).
% 1.72/1.92  thf('140', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.72/1.92           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['139'])).
% 1.72/1.92  thf('141', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.72/1.92             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['134', '140'])).
% 1.72/1.92  thf('142', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.72/1.92           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['141'])).
% 1.72/1.92  thf('143', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.72/1.92           (k1_relat_1 @ X0))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['133', '142'])).
% 1.72/1.92  thf('144', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.72/1.92             (k1_relat_1 @ X0)))),
% 1.72/1.92      inference('simplify', [status(thm)], ['143'])).
% 1.72/1.92  thf('145', plain,
% 1.72/1.92      ((((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 1.72/1.92         | ~ (v1_relat_1 @ sk_C)
% 1.72/1.92         | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92         | ~ (v2_funct_1 @ sk_C)))
% 1.72/1.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['132', '144'])).
% 1.72/1.92  thf('146', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.72/1.92      inference('sup+', [status(thm)], ['6', '7'])).
% 1.72/1.92  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('150', plain,
% 1.72/1.92      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.72/1.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.72/1.92      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 1.72/1.92  thf('151', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['94', '150'])).
% 1.72/1.92  thf('152', plain,
% 1.72/1.92      (~
% 1.72/1.92       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.72/1.92       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.72/1.92       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('split', [status(esa)], ['49'])).
% 1.72/1.92  thf('153', plain,
% 1.72/1.92      (~
% 1.72/1.92       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.72/1.92      inference('sat_resolution*', [status(thm)], ['93', '151', '152'])).
% 1.72/1.92  thf('154', plain, (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) = (sk_A))),
% 1.72/1.92      inference('simpl_trail', [status(thm)], ['86', '153'])).
% 1.72/1.92  thf('155', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('157', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('158', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('demod', [status(thm)], ['15', '154', '155', '156', '157'])).
% 1.72/1.92  thf('159', plain,
% 1.72/1.92      (![X9 : $i]:
% 1.72/1.92         (((k10_relat_1 @ X9 @ (k2_relat_1 @ X9)) = (k1_relat_1 @ X9))
% 1.72/1.92          | ~ (v1_relat_1 @ X9))),
% 1.72/1.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.72/1.92  thf('160', plain,
% 1.72/1.92      ((((k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 1.72/1.92          = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.72/1.92        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['158', '159'])).
% 1.72/1.92  thf('161', plain,
% 1.72/1.92      ((~ (v1_relat_1 @ sk_C)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92        | ((k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 1.72/1.92            = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['3', '160'])).
% 1.72/1.92  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('164', plain,
% 1.72/1.92      (((k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 1.72/1.92         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('demod', [status(thm)], ['161', '162', '163'])).
% 1.72/1.92  thf('165', plain,
% 1.72/1.92      ((((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92        | ~ (v2_funct_1 @ sk_C))),
% 1.72/1.92      inference('sup+', [status(thm)], ['2', '164'])).
% 1.72/1.92  thf('166', plain,
% 1.72/1.92      ((((k9_relat_1 @ sk_C @ sk_A) = (sk_B)))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('sup+', [status(thm)], ['66', '80'])).
% 1.72/1.92  thf('167', plain,
% 1.72/1.92      (~
% 1.72/1.92       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.72/1.92      inference('sat_resolution*', [status(thm)], ['93', '151', '152'])).
% 1.72/1.92  thf('168', plain, (((k9_relat_1 @ sk_C @ sk_A) = (sk_B))),
% 1.72/1.92      inference('simpl_trail', [status(thm)], ['166', '167'])).
% 1.72/1.92  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('172', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('demod', [status(thm)], ['165', '168', '169', '170', '171'])).
% 1.72/1.92  thf('173', plain,
% 1.72/1.92      (![X40 : $i]:
% 1.72/1.92         ((m1_subset_1 @ X40 @ 
% 1.72/1.92           (k1_zfmisc_1 @ 
% 1.72/1.92            (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 1.72/1.92          | ~ (v1_funct_1 @ X40)
% 1.72/1.92          | ~ (v1_relat_1 @ X40))),
% 1.72/1.92      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.72/1.92  thf('174', plain,
% 1.72/1.92      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92         (k1_zfmisc_1 @ 
% 1.72/1.92          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 1.72/1.92        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.72/1.92        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['172', '173'])).
% 1.72/1.92  thf('175', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('demod', [status(thm)], ['15', '154', '155', '156', '157'])).
% 1.72/1.92  thf('176', plain,
% 1.72/1.92      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.92        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.72/1.92        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('demod', [status(thm)], ['174', '175'])).
% 1.72/1.92  thf('177', plain,
% 1.72/1.92      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.72/1.92         <= (~
% 1.72/1.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('split', [status(esa)], ['49'])).
% 1.72/1.92  thf('178', plain,
% 1.72/1.92      (~
% 1.72/1.92       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.72/1.92      inference('sat_resolution*', [status(thm)], ['93', '151', '152'])).
% 1.72/1.92  thf('179', plain,
% 1.72/1.92      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.72/1.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('simpl_trail', [status(thm)], ['177', '178'])).
% 1.72/1.92  thf('180', plain,
% 1.72/1.92      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.72/1.92        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('clc', [status(thm)], ['176', '179'])).
% 1.72/1.92  thf('181', plain,
% 1.72/1.92      ((~ (v1_relat_1 @ sk_C)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['1', '180'])).
% 1.72/1.92  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('184', plain, (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['181', '182', '183'])).
% 1.72/1.92  thf('185', plain, ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.92      inference('sup-', [status(thm)], ['0', '184'])).
% 1.72/1.92  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('188', plain, ($false),
% 1.72/1.92      inference('demod', [status(thm)], ['185', '186', '187'])).
% 1.72/1.92  
% 1.72/1.92  % SZS output end Refutation
% 1.72/1.92  
% 1.72/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
