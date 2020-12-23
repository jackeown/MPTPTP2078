%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vIXHpntiES

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:41 EST 2020

% Result     : Theorem 9.52s
% Output     : Refutation 9.52s
% Verified   : 
% Statistics : Number of formulae       :  235 (1476 expanded)
%              Number of leaves         :   53 ( 454 expanded)
%              Depth                    :   31
%              Number of atoms          : 1886 (23376 expanded)
%              Number of equality atoms :  114 ( 964 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k9_relat_1 @ X20 @ X21 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X20 ) @ X21 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('3',plain,(
    ! [X38: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X38 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('4',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

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

thf(zf_stmt_1,negated_conjecture,(
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

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('11',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( zip_tseitin_0 @ X47 @ X48 )
      | ( zip_tseitin_1 @ X49 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ( X44
        = ( k1_relset_1 @ X44 @ X45 @ X46 ) )
      | ~ ( zip_tseitin_1 @ X46 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('28',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X52: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['35','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','52'])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('57',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('58',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('60',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('61',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['54'])).

thf('62',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('67',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','52'])).

thf('68',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('69',plain,
    ( ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X38: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X38 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('72',plain,(
    ! [X50: $i,X51: $i] :
      ( m1_subset_1 @ ( sk_C @ X50 @ X51 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('73',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X50: $i,X51: $i] :
      ( v1_funct_2 @ ( sk_C @ X50 @ X51 ) @ X51 @ X50 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['69','80'])).

thf('82',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('84',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('85',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('86',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('87',plain,(
    ! [X52: $i] :
      ( ( v1_funct_2 @ X52 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['83','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('95',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('96',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('97',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['82','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('100',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('102',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','102'])).

thf('104',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['66','103'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['54'])).

thf('106',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['65','104','105'])).

thf('107',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['58','106'])).

thf('108',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('109',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('110',plain,(
    ! [X14: $i] :
      ( ( ( k10_relat_1 @ X14 @ ( k2_relat_1 @ X14 ) )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['107','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('116',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('117',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('118',plain,
    ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['2','118'])).

thf('120',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('122',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('124',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k2_relat_1 @ X19 ) )
      | ( ( k9_relat_1 @ X19 @ ( k10_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('127',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['122','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('131',plain,(
    ! [X14: $i] :
      ( ( ( k10_relat_1 @ X14 @ ( k2_relat_1 @ X14 ) )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('132',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ sk_B_1 )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('134',plain,
    ( ( k10_relat_1 @ sk_C_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['129','134'])).

thf('136',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = sk_B_1 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['120','135'])).

thf('137',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['65','104','105'])).

thf('138',plain,
    ( ( k9_relat_1 @ sk_C_1 @ sk_A )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('140',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('141',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('142',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['119','138','139','140','141'])).

thf('143',plain,(
    ! [X52: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('144',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('146',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('147',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('148',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['145','151'])).

thf('153',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['129','134'])).

thf('154',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['121'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('155',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X23 ) @ ( k9_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['153','156'])).

thf('158',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('159',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('160',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('161',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['58','106'])).

thf('163',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('165',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('166',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('167',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['152','163','164','165','166'])).

thf('168',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['144','167'])).

thf('169',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf('170',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['65','104','105'])).

thf('171',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['168','171'])).

thf('173',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('175',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('176',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('179',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['177','178','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vIXHpntiES
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.52/9.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.52/9.70  % Solved by: fo/fo7.sh
% 9.52/9.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.52/9.70  % done 6580 iterations in 9.251s
% 9.52/9.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.52/9.70  % SZS output start Refutation
% 9.52/9.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 9.52/9.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 9.52/9.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.52/9.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.52/9.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.52/9.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.52/9.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.52/9.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.52/9.70  thf(sk_B_type, type, sk_B: $i > $i).
% 9.52/9.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.52/9.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.52/9.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 9.52/9.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.52/9.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 9.52/9.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 9.52/9.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 9.52/9.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 9.52/9.70  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 9.52/9.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.52/9.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 9.52/9.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.52/9.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 9.52/9.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.52/9.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 9.52/9.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 9.52/9.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 9.52/9.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 9.52/9.70  thf(sk_A_type, type, sk_A: $i).
% 9.52/9.70  thf(dt_k2_funct_1, axiom,
% 9.52/9.70    (![A:$i]:
% 9.52/9.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.52/9.70       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 9.52/9.70         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 9.52/9.70  thf('0', plain,
% 9.52/9.70      (![X15 : $i]:
% 9.52/9.70         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 9.52/9.70          | ~ (v1_funct_1 @ X15)
% 9.52/9.70          | ~ (v1_relat_1 @ X15))),
% 9.52/9.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.52/9.70  thf('1', plain,
% 9.52/9.70      (![X15 : $i]:
% 9.52/9.70         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 9.52/9.70          | ~ (v1_funct_1 @ X15)
% 9.52/9.70          | ~ (v1_relat_1 @ X15))),
% 9.52/9.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.52/9.70  thf(t154_funct_1, axiom,
% 9.52/9.70    (![A:$i,B:$i]:
% 9.52/9.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.52/9.70       ( ( v2_funct_1 @ B ) =>
% 9.52/9.70         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 9.52/9.70  thf('2', plain,
% 9.52/9.70      (![X20 : $i, X21 : $i]:
% 9.52/9.70         (~ (v2_funct_1 @ X20)
% 9.52/9.70          | ((k9_relat_1 @ X20 @ X21)
% 9.52/9.70              = (k10_relat_1 @ (k2_funct_1 @ X20) @ X21))
% 9.52/9.70          | ~ (v1_funct_1 @ X20)
% 9.52/9.70          | ~ (v1_relat_1 @ X20))),
% 9.52/9.70      inference('cnf', [status(esa)], [t154_funct_1])).
% 9.52/9.70  thf(t29_mcart_1, axiom,
% 9.52/9.70    (![A:$i]:
% 9.52/9.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 9.52/9.70          ( ![B:$i]:
% 9.52/9.70            ( ~( ( r2_hidden @ B @ A ) & 
% 9.52/9.70                 ( ![C:$i,D:$i,E:$i]:
% 9.52/9.70                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 9.52/9.70                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 9.52/9.70  thf('3', plain,
% 9.52/9.70      (![X38 : $i]:
% 9.52/9.70         (((X38) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X38) @ X38))),
% 9.52/9.70      inference('cnf', [status(esa)], [t29_mcart_1])).
% 9.52/9.70  thf('4', plain,
% 9.52/9.70      (![X15 : $i]:
% 9.52/9.70         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 9.52/9.70          | ~ (v1_funct_1 @ X15)
% 9.52/9.70          | ~ (v1_relat_1 @ X15))),
% 9.52/9.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.52/9.70  thf('5', plain,
% 9.52/9.70      (![X15 : $i]:
% 9.52/9.70         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 9.52/9.70          | ~ (v1_funct_1 @ X15)
% 9.52/9.70          | ~ (v1_relat_1 @ X15))),
% 9.52/9.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.52/9.70  thf(d1_funct_2, axiom,
% 9.52/9.70    (![A:$i,B:$i,C:$i]:
% 9.52/9.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.52/9.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.52/9.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 9.52/9.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 9.52/9.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.52/9.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 9.52/9.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 9.52/9.70  thf(zf_stmt_0, axiom,
% 9.52/9.70    (![B:$i,A:$i]:
% 9.52/9.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.52/9.70       ( zip_tseitin_0 @ B @ A ) ))).
% 9.52/9.70  thf('6', plain,
% 9.52/9.70      (![X42 : $i, X43 : $i]:
% 9.52/9.70         ((zip_tseitin_0 @ X42 @ X43) | ((X42) = (k1_xboole_0)))),
% 9.52/9.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.70  thf(t113_zfmisc_1, axiom,
% 9.52/9.70    (![A:$i,B:$i]:
% 9.52/9.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 9.52/9.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.52/9.70  thf('7', plain,
% 9.52/9.70      (![X4 : $i, X5 : $i]:
% 9.52/9.70         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 9.52/9.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.52/9.70  thf('8', plain,
% 9.52/9.70      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 9.52/9.70      inference('simplify', [status(thm)], ['7'])).
% 9.52/9.70  thf('9', plain,
% 9.52/9.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.52/9.70         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 9.52/9.70      inference('sup+', [status(thm)], ['6', '8'])).
% 9.52/9.70  thf(t31_funct_2, conjecture,
% 9.52/9.70    (![A:$i,B:$i,C:$i]:
% 9.52/9.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.52/9.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.52/9.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 9.52/9.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 9.52/9.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 9.52/9.70           ( m1_subset_1 @
% 9.52/9.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 9.52/9.70  thf(zf_stmt_1, negated_conjecture,
% 9.52/9.70    (~( ![A:$i,B:$i,C:$i]:
% 9.52/9.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.52/9.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.52/9.70          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 9.52/9.70            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 9.52/9.70              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 9.52/9.70              ( m1_subset_1 @
% 9.52/9.70                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 9.52/9.70    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 9.52/9.70  thf('10', plain,
% 9.52/9.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.52/9.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 9.52/9.70  thf(zf_stmt_3, axiom,
% 9.52/9.70    (![C:$i,B:$i,A:$i]:
% 9.52/9.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 9.52/9.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 9.52/9.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 9.52/9.70  thf(zf_stmt_5, axiom,
% 9.52/9.70    (![A:$i,B:$i,C:$i]:
% 9.52/9.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.52/9.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 9.52/9.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.52/9.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 9.52/9.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 9.52/9.70  thf('11', plain,
% 9.52/9.70      (![X47 : $i, X48 : $i, X49 : $i]:
% 9.52/9.70         (~ (zip_tseitin_0 @ X47 @ X48)
% 9.52/9.70          | (zip_tseitin_1 @ X49 @ X47 @ X48)
% 9.52/9.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47))))),
% 9.52/9.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.52/9.70  thf('12', plain,
% 9.52/9.70      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 9.52/9.70        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 9.52/9.70      inference('sup-', [status(thm)], ['10', '11'])).
% 9.52/9.70  thf('13', plain,
% 9.52/9.70      (![X0 : $i]:
% 9.52/9.70         (((k2_zfmisc_1 @ sk_B_1 @ X0) = (k1_xboole_0))
% 9.52/9.70          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 9.52/9.70      inference('sup-', [status(thm)], ['9', '12'])).
% 9.52/9.70  thf('14', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 9.52/9.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.70  thf('15', plain,
% 9.52/9.70      (![X44 : $i, X45 : $i, X46 : $i]:
% 9.52/9.70         (~ (v1_funct_2 @ X46 @ X44 @ X45)
% 9.52/9.70          | ((X44) = (k1_relset_1 @ X44 @ X45 @ X46))
% 9.52/9.70          | ~ (zip_tseitin_1 @ X46 @ X45 @ X44))),
% 9.52/9.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 9.52/9.70  thf('16', plain,
% 9.52/9.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 9.52/9.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 9.52/9.70      inference('sup-', [status(thm)], ['14', '15'])).
% 9.52/9.70  thf('17', plain,
% 9.52/9.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.52/9.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.70  thf(redefinition_k1_relset_1, axiom,
% 9.52/9.70    (![A:$i,B:$i,C:$i]:
% 9.52/9.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.52/9.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 9.52/9.70  thf('18', plain,
% 9.52/9.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 9.52/9.70         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 9.52/9.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 9.52/9.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.52/9.70  thf('19', plain,
% 9.52/9.70      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 9.52/9.70      inference('sup-', [status(thm)], ['17', '18'])).
% 9.52/9.70  thf('20', plain,
% 9.52/9.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 9.52/9.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 9.52/9.70      inference('demod', [status(thm)], ['16', '19'])).
% 9.52/9.70  thf('21', plain,
% 9.52/9.70      (![X0 : $i]:
% 9.52/9.70         (((k2_zfmisc_1 @ sk_B_1 @ X0) = (k1_xboole_0))
% 9.52/9.70          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 9.52/9.70      inference('sup-', [status(thm)], ['13', '20'])).
% 9.52/9.70  thf('22', plain,
% 9.52/9.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.52/9.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.70  thf(redefinition_k2_relset_1, axiom,
% 9.52/9.70    (![A:$i,B:$i,C:$i]:
% 9.52/9.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.52/9.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 9.52/9.70  thf('23', plain,
% 9.52/9.70      (![X35 : $i, X36 : $i, X37 : $i]:
% 9.52/9.70         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 9.52/9.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 9.52/9.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 9.52/9.70  thf('24', plain,
% 9.52/9.70      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 9.52/9.70      inference('sup-', [status(thm)], ['22', '23'])).
% 9.52/9.70  thf('25', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 9.52/9.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.70  thf('26', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 9.52/9.70      inference('sup+', [status(thm)], ['24', '25'])).
% 9.52/9.70  thf(t55_funct_1, axiom,
% 9.52/9.70    (![A:$i]:
% 9.52/9.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.52/9.71       ( ( v2_funct_1 @ A ) =>
% 9.52/9.71         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 9.52/9.71           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 9.52/9.71  thf('27', plain,
% 9.52/9.71      (![X24 : $i]:
% 9.52/9.71         (~ (v2_funct_1 @ X24)
% 9.52/9.71          | ((k1_relat_1 @ X24) = (k2_relat_1 @ (k2_funct_1 @ X24)))
% 9.52/9.71          | ~ (v1_funct_1 @ X24)
% 9.52/9.71          | ~ (v1_relat_1 @ X24))),
% 9.52/9.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 9.52/9.71  thf('28', plain,
% 9.52/9.71      (![X24 : $i]:
% 9.52/9.71         (~ (v2_funct_1 @ X24)
% 9.52/9.71          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 9.52/9.71          | ~ (v1_funct_1 @ X24)
% 9.52/9.71          | ~ (v1_relat_1 @ X24))),
% 9.52/9.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 9.52/9.71  thf(t3_funct_2, axiom,
% 9.52/9.71    (![A:$i]:
% 9.52/9.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.52/9.71       ( ( v1_funct_1 @ A ) & 
% 9.52/9.71         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 9.52/9.71         ( m1_subset_1 @
% 9.52/9.71           A @ 
% 9.52/9.71           ( k1_zfmisc_1 @
% 9.52/9.71             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 9.52/9.71  thf('29', plain,
% 9.52/9.71      (![X52 : $i]:
% 9.52/9.71         ((m1_subset_1 @ X52 @ 
% 9.52/9.71           (k1_zfmisc_1 @ 
% 9.52/9.71            (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52))))
% 9.52/9.71          | ~ (v1_funct_1 @ X52)
% 9.52/9.71          | ~ (v1_relat_1 @ X52))),
% 9.52/9.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.52/9.71  thf(t5_subset, axiom,
% 9.52/9.71    (![A:$i,B:$i,C:$i]:
% 9.52/9.71     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 9.52/9.71          ( v1_xboole_0 @ C ) ) ))).
% 9.52/9.71  thf('30', plain,
% 9.52/9.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.52/9.71         (~ (r2_hidden @ X10 @ X11)
% 9.52/9.71          | ~ (v1_xboole_0 @ X12)
% 9.52/9.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 9.52/9.71      inference('cnf', [status(esa)], [t5_subset])).
% 9.52/9.71  thf('31', plain,
% 9.52/9.71      (![X0 : $i, X1 : $i]:
% 9.52/9.71         (~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_xboole_0 @ 
% 9.52/9.71               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 9.52/9.71          | ~ (r2_hidden @ X1 @ X0))),
% 9.52/9.71      inference('sup-', [status(thm)], ['29', '30'])).
% 9.52/9.71  thf('32', plain,
% 9.52/9.71      (![X0 : $i, X1 : $i]:
% 9.52/9.71         (~ (v1_xboole_0 @ 
% 9.52/9.71             (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 9.52/9.71              (k2_relat_1 @ (k2_funct_1 @ X0))))
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (r2_hidden @ X1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['28', '31'])).
% 9.52/9.71  thf('33', plain,
% 9.52/9.71      (![X0 : $i, X1 : $i]:
% 9.52/9.71         (~ (v1_xboole_0 @ 
% 9.52/9.71             (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (r2_hidden @ X1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0))),
% 9.52/9.71      inference('sup-', [status(thm)], ['27', '32'])).
% 9.52/9.71  thf('34', plain,
% 9.52/9.71      (![X0 : $i, X1 : $i]:
% 9.52/9.71         (~ (r2_hidden @ X1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_xboole_0 @ 
% 9.52/9.71               (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 9.52/9.71      inference('simplify', [status(thm)], ['33'])).
% 9.52/9.71  thf('35', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C_1)))
% 9.52/9.71          | ~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71          | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71          | ~ (v2_funct_1 @ sk_C_1)
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['26', '34'])).
% 9.52/9.71  thf('36', plain,
% 9.52/9.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf(cc1_relset_1, axiom,
% 9.52/9.71    (![A:$i,B:$i,C:$i]:
% 9.52/9.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.52/9.71       ( v1_relat_1 @ C ) ))).
% 9.52/9.71  thf('37', plain,
% 9.52/9.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 9.52/9.71         ((v1_relat_1 @ X26)
% 9.52/9.71          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 9.52/9.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 9.52/9.71  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('39', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('40', plain, ((v2_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('41', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C_1)))
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['35', '38', '39', '40'])).
% 9.52/9.71  thf('42', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_xboole_0 @ k1_xboole_0)
% 9.52/9.71          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['21', '41'])).
% 9.52/9.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 9.52/9.71  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.52/9.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.52/9.71  thf('44', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['42', '43'])).
% 9.52/9.71  thf('45', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71          | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['5', '44'])).
% 9.52/9.71  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('47', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('48', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['45', '46', '47'])).
% 9.52/9.71  thf('49', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71          | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['4', '48'])).
% 9.52/9.71  thf('50', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('51', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('52', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['49', '50', '51'])).
% 9.52/9.71  thf('53', plain,
% 9.52/9.71      ((((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 9.52/9.71        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['3', '52'])).
% 9.52/9.71  thf('54', plain,
% 9.52/9.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 9.52/9.71        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('55', plain,
% 9.52/9.71      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 9.52/9.71         <= (~
% 9.52/9.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 9.52/9.71      inference('split', [status(esa)], ['54'])).
% 9.52/9.71  thf('56', plain,
% 9.52/9.71      (((~ (m1_subset_1 @ k1_xboole_0 @ 
% 9.52/9.71            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 9.52/9.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 9.52/9.71         <= (~
% 9.52/9.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 9.52/9.71      inference('sup-', [status(thm)], ['53', '55'])).
% 9.52/9.71  thf(t4_subset_1, axiom,
% 9.52/9.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 9.52/9.71  thf('57', plain,
% 9.52/9.71      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 9.52/9.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 9.52/9.71  thf('58', plain,
% 9.52/9.71      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 9.52/9.71         <= (~
% 9.52/9.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 9.52/9.71      inference('demod', [status(thm)], ['56', '57'])).
% 9.52/9.71  thf('59', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('60', plain,
% 9.52/9.71      (![X15 : $i]:
% 9.52/9.71         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 9.52/9.71          | ~ (v1_funct_1 @ X15)
% 9.52/9.71          | ~ (v1_relat_1 @ X15))),
% 9.52/9.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.52/9.71  thf('61', plain,
% 9.52/9.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 9.52/9.71         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 9.52/9.71      inference('split', [status(esa)], ['54'])).
% 9.52/9.71  thf('62', plain,
% 9.52/9.71      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 9.52/9.71         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 9.52/9.71      inference('sup-', [status(thm)], ['60', '61'])).
% 9.52/9.71  thf('63', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('64', plain,
% 9.52/9.71      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 9.52/9.71      inference('demod', [status(thm)], ['62', '63'])).
% 9.52/9.71  thf('65', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['59', '64'])).
% 9.52/9.71  thf('66', plain,
% 9.52/9.71      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 9.52/9.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 9.52/9.71      inference('split', [status(esa)], ['54'])).
% 9.52/9.71  thf('67', plain,
% 9.52/9.71      ((((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 9.52/9.71        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['3', '52'])).
% 9.52/9.71  thf('68', plain,
% 9.52/9.71      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 9.52/9.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 9.52/9.71      inference('split', [status(esa)], ['54'])).
% 9.52/9.71  thf('69', plain,
% 9.52/9.71      (((~ (v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A)
% 9.52/9.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 9.52/9.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['67', '68'])).
% 9.52/9.71  thf('70', plain,
% 9.52/9.71      (![X38 : $i]:
% 9.52/9.71         (((X38) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X38) @ X38))),
% 9.52/9.71      inference('cnf', [status(esa)], [t29_mcart_1])).
% 9.52/9.71  thf('71', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (((k2_zfmisc_1 @ sk_B_1 @ X0) = (k1_xboole_0))
% 9.52/9.71          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['13', '20'])).
% 9.52/9.71  thf(rc1_funct_2, axiom,
% 9.52/9.71    (![A:$i,B:$i]:
% 9.52/9.71     ( ?[C:$i]:
% 9.52/9.71       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 9.52/9.71         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 9.52/9.71         ( v1_relat_1 @ C ) & 
% 9.52/9.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 9.52/9.71  thf('72', plain,
% 9.52/9.71      (![X50 : $i, X51 : $i]:
% 9.52/9.71         (m1_subset_1 @ (sk_C @ X50 @ X51) @ 
% 9.52/9.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))),
% 9.52/9.71      inference('cnf', [status(esa)], [rc1_funct_2])).
% 9.52/9.71  thf('73', plain,
% 9.52/9.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.52/9.71         (~ (r2_hidden @ X10 @ X11)
% 9.52/9.71          | ~ (v1_xboole_0 @ X12)
% 9.52/9.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 9.52/9.71      inference('cnf', [status(esa)], [t5_subset])).
% 9.52/9.71  thf('74', plain,
% 9.52/9.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.52/9.71         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 9.52/9.71          | ~ (r2_hidden @ X2 @ (sk_C @ X0 @ X1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['72', '73'])).
% 9.52/9.71  thf('75', plain,
% 9.52/9.71      (![X0 : $i, X1 : $i]:
% 9.52/9.71         (~ (v1_xboole_0 @ k1_xboole_0)
% 9.52/9.71          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X1 @ (sk_C @ X0 @ sk_B_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['71', '74'])).
% 9.52/9.71  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.52/9.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.52/9.71  thf('77', plain,
% 9.52/9.71      (![X0 : $i, X1 : $i]:
% 9.52/9.71         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 9.52/9.71          | ~ (r2_hidden @ X1 @ (sk_C @ X0 @ sk_B_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['75', '76'])).
% 9.52/9.71  thf('78', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (((sk_C @ X0 @ sk_B_1) = (k1_xboole_0))
% 9.52/9.71          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['70', '77'])).
% 9.52/9.71  thf('79', plain,
% 9.52/9.71      (![X50 : $i, X51 : $i]: (v1_funct_2 @ (sk_C @ X50 @ X51) @ X51 @ X50)),
% 9.52/9.71      inference('cnf', [status(esa)], [rc1_funct_2])).
% 9.52/9.71  thf('80', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         ((v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ X0)
% 9.52/9.71          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup+', [status(thm)], ['78', '79'])).
% 9.52/9.71  thf('81', plain,
% 9.52/9.71      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 9.52/9.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 9.52/9.71      inference('clc', [status(thm)], ['69', '80'])).
% 9.52/9.71  thf('82', plain,
% 9.52/9.71      (![X24 : $i]:
% 9.52/9.71         (~ (v2_funct_1 @ X24)
% 9.52/9.71          | ((k1_relat_1 @ X24) = (k2_relat_1 @ (k2_funct_1 @ X24)))
% 9.52/9.71          | ~ (v1_funct_1 @ X24)
% 9.52/9.71          | ~ (v1_relat_1 @ X24))),
% 9.52/9.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 9.52/9.71  thf('83', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['24', '25'])).
% 9.52/9.71  thf('84', plain,
% 9.52/9.71      (![X15 : $i]:
% 9.52/9.71         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 9.52/9.71          | ~ (v1_funct_1 @ X15)
% 9.52/9.71          | ~ (v1_relat_1 @ X15))),
% 9.52/9.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.52/9.71  thf('85', plain,
% 9.52/9.71      (![X15 : $i]:
% 9.52/9.71         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 9.52/9.71          | ~ (v1_funct_1 @ X15)
% 9.52/9.71          | ~ (v1_relat_1 @ X15))),
% 9.52/9.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.52/9.71  thf('86', plain,
% 9.52/9.71      (![X24 : $i]:
% 9.52/9.71         (~ (v2_funct_1 @ X24)
% 9.52/9.71          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 9.52/9.71          | ~ (v1_funct_1 @ X24)
% 9.52/9.71          | ~ (v1_relat_1 @ X24))),
% 9.52/9.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 9.52/9.71  thf('87', plain,
% 9.52/9.71      (![X52 : $i]:
% 9.52/9.71         ((v1_funct_2 @ X52 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52))
% 9.52/9.71          | ~ (v1_funct_1 @ X52)
% 9.52/9.71          | ~ (v1_relat_1 @ X52))),
% 9.52/9.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.52/9.71  thf('88', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 9.52/9.71           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 9.52/9.71      inference('sup+', [status(thm)], ['86', '87'])).
% 9.52/9.71  thf('89', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 9.52/9.71             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 9.52/9.71      inference('sup-', [status(thm)], ['85', '88'])).
% 9.52/9.71  thf('90', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 9.52/9.71           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0))),
% 9.52/9.71      inference('simplify', [status(thm)], ['89'])).
% 9.52/9.71  thf('91', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 9.52/9.71             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 9.52/9.71      inference('sup-', [status(thm)], ['84', '90'])).
% 9.52/9.71  thf('92', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 9.52/9.71           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0))),
% 9.52/9.71      inference('simplify', [status(thm)], ['91'])).
% 9.52/9.71  thf('93', plain,
% 9.52/9.71      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 9.52/9.71         (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 9.52/9.71        | ~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71        | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71        | ~ (v2_funct_1 @ sk_C_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['83', '92'])).
% 9.52/9.71  thf('94', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('95', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('96', plain, ((v2_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('97', plain,
% 9.52/9.71      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 9.52/9.71        (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 9.52/9.71  thf('98', plain,
% 9.52/9.71      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ (k1_relat_1 @ sk_C_1))
% 9.52/9.71        | ~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71        | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71        | ~ (v2_funct_1 @ sk_C_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['82', '97'])).
% 9.52/9.71  thf('99', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('100', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('101', plain, ((v2_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('102', plain,
% 9.52/9.71      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ (k1_relat_1 @ sk_C_1))),
% 9.52/9.71      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 9.52/9.71  thf('103', plain,
% 9.52/9.71      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 9.52/9.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 9.52/9.71      inference('sup+', [status(thm)], ['81', '102'])).
% 9.52/9.71  thf('104', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))),
% 9.52/9.71      inference('demod', [status(thm)], ['66', '103'])).
% 9.52/9.71  thf('105', plain,
% 9.52/9.71      (~
% 9.52/9.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 9.52/9.71       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)) | 
% 9.52/9.71       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('split', [status(esa)], ['54'])).
% 9.52/9.71  thf('106', plain,
% 9.52/9.71      (~
% 9.52/9.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 9.52/9.71      inference('sat_resolution*', [status(thm)], ['65', '104', '105'])).
% 9.52/9.71  thf('107', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 9.52/9.71      inference('simpl_trail', [status(thm)], ['58', '106'])).
% 9.52/9.71  thf('108', plain,
% 9.52/9.71      (![X15 : $i]:
% 9.52/9.71         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 9.52/9.71          | ~ (v1_funct_1 @ X15)
% 9.52/9.71          | ~ (v1_relat_1 @ X15))),
% 9.52/9.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.52/9.71  thf('109', plain,
% 9.52/9.71      (![X24 : $i]:
% 9.52/9.71         (~ (v2_funct_1 @ X24)
% 9.52/9.71          | ((k1_relat_1 @ X24) = (k2_relat_1 @ (k2_funct_1 @ X24)))
% 9.52/9.71          | ~ (v1_funct_1 @ X24)
% 9.52/9.71          | ~ (v1_relat_1 @ X24))),
% 9.52/9.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 9.52/9.71  thf(t169_relat_1, axiom,
% 9.52/9.71    (![A:$i]:
% 9.52/9.71     ( ( v1_relat_1 @ A ) =>
% 9.52/9.71       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 9.52/9.71  thf('110', plain,
% 9.52/9.71      (![X14 : $i]:
% 9.52/9.71         (((k10_relat_1 @ X14 @ (k2_relat_1 @ X14)) = (k1_relat_1 @ X14))
% 9.52/9.71          | ~ (v1_relat_1 @ X14))),
% 9.52/9.71      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.52/9.71  thf('111', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 9.52/9.71            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 9.52/9.71      inference('sup+', [status(thm)], ['109', '110'])).
% 9.52/9.71  thf('112', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 9.52/9.71              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 9.52/9.71      inference('sup-', [status(thm)], ['108', '111'])).
% 9.52/9.71  thf('113', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 9.52/9.71            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0))),
% 9.52/9.71      inference('simplify', [status(thm)], ['112'])).
% 9.52/9.71  thf('114', plain,
% 9.52/9.71      ((((k10_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_A)
% 9.52/9.71          = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 9.52/9.71        | ~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71        | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71        | ~ (v2_funct_1 @ sk_C_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['107', '113'])).
% 9.52/9.71  thf('115', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('116', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('117', plain, ((v2_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('118', plain,
% 9.52/9.71      (((k10_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_A)
% 9.52/9.71         = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 9.52/9.71  thf('119', plain,
% 9.52/9.71      ((((k9_relat_1 @ sk_C_1 @ sk_A) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 9.52/9.71        | ~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71        | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71        | ~ (v2_funct_1 @ sk_C_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['2', '118'])).
% 9.52/9.71  thf('120', plain,
% 9.52/9.71      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 9.52/9.71         <= (~
% 9.52/9.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 9.52/9.71      inference('demod', [status(thm)], ['56', '57'])).
% 9.52/9.71  thf(d10_xboole_0, axiom,
% 9.52/9.71    (![A:$i,B:$i]:
% 9.52/9.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.52/9.71  thf('121', plain,
% 9.52/9.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.52/9.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.52/9.71  thf('122', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.52/9.71      inference('simplify', [status(thm)], ['121'])).
% 9.52/9.71  thf('123', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['24', '25'])).
% 9.52/9.71  thf(t147_funct_1, axiom,
% 9.52/9.71    (![A:$i,B:$i]:
% 9.52/9.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.52/9.71       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 9.52/9.71         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 9.52/9.71  thf('124', plain,
% 9.52/9.71      (![X18 : $i, X19 : $i]:
% 9.52/9.71         (~ (r1_tarski @ X18 @ (k2_relat_1 @ X19))
% 9.52/9.71          | ((k9_relat_1 @ X19 @ (k10_relat_1 @ X19 @ X18)) = (X18))
% 9.52/9.71          | ~ (v1_funct_1 @ X19)
% 9.52/9.71          | ~ (v1_relat_1 @ X19))),
% 9.52/9.71      inference('cnf', [status(esa)], [t147_funct_1])).
% 9.52/9.71  thf('125', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (r1_tarski @ X0 @ sk_B_1)
% 9.52/9.71          | ~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71          | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71          | ((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['123', '124'])).
% 9.52/9.71  thf('126', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('127', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('128', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (r1_tarski @ X0 @ sk_B_1)
% 9.52/9.71          | ((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 9.52/9.71      inference('demod', [status(thm)], ['125', '126', '127'])).
% 9.52/9.71  thf('129', plain,
% 9.52/9.71      (((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_B_1)) = (sk_B_1))),
% 9.52/9.71      inference('sup-', [status(thm)], ['122', '128'])).
% 9.52/9.71  thf('130', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['24', '25'])).
% 9.52/9.71  thf('131', plain,
% 9.52/9.71      (![X14 : $i]:
% 9.52/9.71         (((k10_relat_1 @ X14 @ (k2_relat_1 @ X14)) = (k1_relat_1 @ X14))
% 9.52/9.71          | ~ (v1_relat_1 @ X14))),
% 9.52/9.71      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.52/9.71  thf('132', plain,
% 9.52/9.71      ((((k10_relat_1 @ sk_C_1 @ sk_B_1) = (k1_relat_1 @ sk_C_1))
% 9.52/9.71        | ~ (v1_relat_1 @ sk_C_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['130', '131'])).
% 9.52/9.71  thf('133', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('134', plain,
% 9.52/9.71      (((k10_relat_1 @ sk_C_1 @ sk_B_1) = (k1_relat_1 @ sk_C_1))),
% 9.52/9.71      inference('demod', [status(thm)], ['132', '133'])).
% 9.52/9.71  thf('135', plain,
% 9.52/9.71      (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)) = (sk_B_1))),
% 9.52/9.71      inference('demod', [status(thm)], ['129', '134'])).
% 9.52/9.71  thf('136', plain,
% 9.52/9.71      ((((k9_relat_1 @ sk_C_1 @ sk_A) = (sk_B_1)))
% 9.52/9.71         <= (~
% 9.52/9.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 9.52/9.71      inference('sup+', [status(thm)], ['120', '135'])).
% 9.52/9.71  thf('137', plain,
% 9.52/9.71      (~
% 9.52/9.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 9.52/9.71      inference('sat_resolution*', [status(thm)], ['65', '104', '105'])).
% 9.52/9.71  thf('138', plain, (((k9_relat_1 @ sk_C_1 @ sk_A) = (sk_B_1))),
% 9.52/9.71      inference('simpl_trail', [status(thm)], ['136', '137'])).
% 9.52/9.71  thf('139', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('140', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('141', plain, ((v2_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('142', plain, (((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['119', '138', '139', '140', '141'])).
% 9.52/9.71  thf('143', plain,
% 9.52/9.71      (![X52 : $i]:
% 9.52/9.71         ((m1_subset_1 @ X52 @ 
% 9.52/9.71           (k1_zfmisc_1 @ 
% 9.52/9.71            (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52))))
% 9.52/9.71          | ~ (v1_funct_1 @ X52)
% 9.52/9.71          | ~ (v1_relat_1 @ X52))),
% 9.52/9.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.52/9.71  thf('144', plain,
% 9.52/9.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71         (k1_zfmisc_1 @ 
% 9.52/9.71          (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 9.52/9.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup+', [status(thm)], ['142', '143'])).
% 9.52/9.71  thf('145', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['24', '25'])).
% 9.52/9.71  thf('146', plain,
% 9.52/9.71      (![X15 : $i]:
% 9.52/9.71         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 9.52/9.71          | ~ (v1_funct_1 @ X15)
% 9.52/9.71          | ~ (v1_relat_1 @ X15))),
% 9.52/9.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.52/9.71  thf('147', plain,
% 9.52/9.71      (![X24 : $i]:
% 9.52/9.71         (~ (v2_funct_1 @ X24)
% 9.52/9.71          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 9.52/9.71          | ~ (v1_funct_1 @ X24)
% 9.52/9.71          | ~ (v1_relat_1 @ X24))),
% 9.52/9.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 9.52/9.71  thf(t146_relat_1, axiom,
% 9.52/9.71    (![A:$i]:
% 9.52/9.71     ( ( v1_relat_1 @ A ) =>
% 9.52/9.71       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 9.52/9.71  thf('148', plain,
% 9.52/9.71      (![X13 : $i]:
% 9.52/9.71         (((k9_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (k2_relat_1 @ X13))
% 9.52/9.71          | ~ (v1_relat_1 @ X13))),
% 9.52/9.71      inference('cnf', [status(esa)], [t146_relat_1])).
% 9.52/9.71  thf('149', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 9.52/9.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 9.52/9.71      inference('sup+', [status(thm)], ['147', '148'])).
% 9.52/9.71  thf('150', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0)
% 9.52/9.71          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 9.52/9.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 9.52/9.71      inference('sup-', [status(thm)], ['146', '149'])).
% 9.52/9.71  thf('151', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 9.52/9.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v1_relat_1 @ X0))),
% 9.52/9.71      inference('simplify', [status(thm)], ['150'])).
% 9.52/9.71  thf('152', plain,
% 9.52/9.71      ((((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B_1)
% 9.52/9.71          = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 9.52/9.71        | ~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71        | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71        | ~ (v2_funct_1 @ sk_C_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['145', '151'])).
% 9.52/9.71  thf('153', plain,
% 9.52/9.71      (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)) = (sk_B_1))),
% 9.52/9.71      inference('demod', [status(thm)], ['129', '134'])).
% 9.52/9.71  thf('154', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.52/9.71      inference('simplify', [status(thm)], ['121'])).
% 9.52/9.71  thf(t177_funct_1, axiom,
% 9.52/9.71    (![A:$i]:
% 9.52/9.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.52/9.71       ( ![B:$i]:
% 9.52/9.71         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 9.52/9.71           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 9.52/9.71             ( B ) ) ) ) ))).
% 9.52/9.71  thf('155', plain,
% 9.52/9.71      (![X22 : $i, X23 : $i]:
% 9.52/9.71         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 9.52/9.71          | ((k9_relat_1 @ (k2_funct_1 @ X23) @ (k9_relat_1 @ X23 @ X22))
% 9.52/9.71              = (X22))
% 9.52/9.71          | ~ (v2_funct_1 @ X23)
% 9.52/9.71          | ~ (v1_funct_1 @ X23)
% 9.52/9.71          | ~ (v1_relat_1 @ X23))),
% 9.52/9.71      inference('cnf', [status(esa)], [t177_funct_1])).
% 9.52/9.71  thf('156', plain,
% 9.52/9.71      (![X0 : $i]:
% 9.52/9.71         (~ (v1_relat_1 @ X0)
% 9.52/9.71          | ~ (v1_funct_1 @ X0)
% 9.52/9.71          | ~ (v2_funct_1 @ X0)
% 9.52/9.71          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 9.52/9.71              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['154', '155'])).
% 9.52/9.71  thf('157', plain,
% 9.52/9.71      ((((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B_1) = (k1_relat_1 @ sk_C_1))
% 9.52/9.71        | ~ (v2_funct_1 @ sk_C_1)
% 9.52/9.71        | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71        | ~ (v1_relat_1 @ sk_C_1))),
% 9.52/9.71      inference('sup+', [status(thm)], ['153', '156'])).
% 9.52/9.71  thf('158', plain, ((v2_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('159', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('160', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('161', plain,
% 9.52/9.71      (((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B_1) = (k1_relat_1 @ sk_C_1))),
% 9.52/9.71      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 9.52/9.71  thf('162', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 9.52/9.71      inference('simpl_trail', [status(thm)], ['58', '106'])).
% 9.52/9.71  thf('163', plain, (((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B_1) = (sk_A))),
% 9.52/9.71      inference('demod', [status(thm)], ['161', '162'])).
% 9.52/9.71  thf('164', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('165', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('166', plain, ((v2_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('167', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['152', '163', '164', '165', '166'])).
% 9.52/9.71  thf('168', plain,
% 9.52/9.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 9.52/9.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('demod', [status(thm)], ['144', '167'])).
% 9.52/9.71  thf('169', plain,
% 9.52/9.71      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 9.52/9.71         <= (~
% 9.52/9.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 9.52/9.71      inference('split', [status(esa)], ['54'])).
% 9.52/9.71  thf('170', plain,
% 9.52/9.71      (~
% 9.52/9.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 9.52/9.71      inference('sat_resolution*', [status(thm)], ['65', '104', '105'])).
% 9.52/9.71  thf('171', plain,
% 9.52/9.71      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 9.52/9.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 9.52/9.71      inference('simpl_trail', [status(thm)], ['169', '170'])).
% 9.52/9.71  thf('172', plain,
% 9.52/9.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 9.52/9.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('clc', [status(thm)], ['168', '171'])).
% 9.52/9.71  thf('173', plain,
% 9.52/9.71      ((~ (v1_relat_1 @ sk_C_1)
% 9.52/9.71        | ~ (v1_funct_1 @ sk_C_1)
% 9.52/9.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 9.52/9.71      inference('sup-', [status(thm)], ['1', '172'])).
% 9.52/9.71  thf('174', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('175', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('176', plain, (~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 9.52/9.71      inference('demod', [status(thm)], ['173', '174', '175'])).
% 9.52/9.71  thf('177', plain, ((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1))),
% 9.52/9.71      inference('sup-', [status(thm)], ['0', '176'])).
% 9.52/9.71  thf('178', plain, ((v1_relat_1 @ sk_C_1)),
% 9.52/9.71      inference('sup-', [status(thm)], ['36', '37'])).
% 9.52/9.71  thf('179', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.52/9.71  thf('180', plain, ($false),
% 9.52/9.71      inference('demod', [status(thm)], ['177', '178', '179'])).
% 9.52/9.71  
% 9.52/9.71  % SZS output end Refutation
% 9.52/9.71  
% 9.52/9.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
