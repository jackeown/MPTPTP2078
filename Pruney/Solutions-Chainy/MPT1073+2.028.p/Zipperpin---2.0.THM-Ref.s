%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eI9a0QBk8z

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:17 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 826 expanded)
%              Number of leaves         :   44 ( 257 expanded)
%              Depth                    :   20
%              Number of atoms          :  940 (10868 expanded)
%              Number of equality atoms :   67 ( 582 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('3',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_2 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('20',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_2 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['21','22','25'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','30'])).

thf('32',plain,(
    ! [X41: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_3 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_A @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('35',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_2 @ X14 @ X11 ) ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('36',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_2 @ X14 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_A @ sk_D_3 ) ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('40',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_A @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','42'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k7_relset_1 @ X30 @ X31 @ X32 @ X30 )
        = ( k2_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('45',plain,
    ( ( k7_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3 @ sk_B_1 )
    = ( k2_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','42'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('47',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('50',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k9_relat_1 @ sk_D_3 @ sk_B_1 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ X7 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['60','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','42'])).

thf('68',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_D_3 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('73',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_D_3 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( k9_relat_1 @ sk_D_3 @ sk_B_1 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('76',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('77',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) )
    | ~ ( v1_xboole_0 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) )
    | ~ ( v1_xboole_0 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_D_3 ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','85'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['66','88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eI9a0QBk8z
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.46/1.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.46/1.69  % Solved by: fo/fo7.sh
% 1.46/1.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.46/1.69  % done 761 iterations in 1.235s
% 1.46/1.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.46/1.69  % SZS output start Refutation
% 1.46/1.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.46/1.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.46/1.69  thf(sk_B_type, type, sk_B: $i > $i).
% 1.46/1.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.46/1.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.46/1.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.46/1.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.46/1.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.46/1.69  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.46/1.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.46/1.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.46/1.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.46/1.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.46/1.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.46/1.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.46/1.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.46/1.69  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 1.46/1.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.46/1.69  thf(sk_A_type, type, sk_A: $i).
% 1.46/1.69  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.46/1.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.46/1.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.46/1.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.46/1.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.46/1.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.46/1.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.46/1.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.46/1.69  thf(t190_funct_2, conjecture,
% 1.46/1.69    (![A:$i,B:$i,C:$i,D:$i]:
% 1.46/1.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.46/1.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.46/1.69       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 1.46/1.69            ( ![E:$i]:
% 1.46/1.69              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 1.46/1.69  thf(zf_stmt_0, negated_conjecture,
% 1.46/1.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.46/1.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.46/1.69            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.46/1.69          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 1.46/1.69               ( ![E:$i]:
% 1.46/1.69                 ( ( m1_subset_1 @ E @ B ) =>
% 1.46/1.69                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 1.46/1.69    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 1.46/1.69  thf('0', plain,
% 1.46/1.69      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf(d1_funct_2, axiom,
% 1.46/1.69    (![A:$i,B:$i,C:$i]:
% 1.46/1.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.46/1.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.46/1.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.46/1.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.46/1.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.46/1.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.46/1.69  thf(zf_stmt_1, axiom,
% 1.46/1.69    (![B:$i,A:$i]:
% 1.46/1.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.46/1.69       ( zip_tseitin_0 @ B @ A ) ))).
% 1.46/1.69  thf('1', plain,
% 1.46/1.69      (![X33 : $i, X34 : $i]:
% 1.46/1.69         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.69  thf('2', plain,
% 1.46/1.69      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.46/1.69  thf(zf_stmt_3, axiom,
% 1.46/1.69    (![C:$i,B:$i,A:$i]:
% 1.46/1.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.46/1.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.46/1.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.46/1.69  thf(zf_stmt_5, axiom,
% 1.46/1.69    (![A:$i,B:$i,C:$i]:
% 1.46/1.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.46/1.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.46/1.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.46/1.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.46/1.69  thf('3', plain,
% 1.46/1.69      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.46/1.69         (~ (zip_tseitin_0 @ X38 @ X39)
% 1.46/1.69          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 1.46/1.69          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.46/1.69  thf('4', plain,
% 1.46/1.69      (((zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1)
% 1.46/1.69        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 1.46/1.69      inference('sup-', [status(thm)], ['2', '3'])).
% 1.46/1.69  thf('5', plain,
% 1.46/1.69      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1))),
% 1.46/1.69      inference('sup-', [status(thm)], ['1', '4'])).
% 1.46/1.69  thf('6', plain, ((v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1)),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf('7', plain,
% 1.46/1.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.46/1.69         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 1.46/1.69          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 1.46/1.69          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.46/1.69  thf('8', plain,
% 1.46/1.69      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1)
% 1.46/1.69        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3)))),
% 1.46/1.69      inference('sup-', [status(thm)], ['6', '7'])).
% 1.46/1.69  thf('9', plain,
% 1.46/1.69      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf(redefinition_k1_relset_1, axiom,
% 1.46/1.69    (![A:$i,B:$i,C:$i]:
% 1.46/1.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.46/1.69  thf('10', plain,
% 1.46/1.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.46/1.69         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.46/1.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.46/1.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.46/1.69  thf('11', plain,
% 1.46/1.69      (((k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('sup-', [status(thm)], ['9', '10'])).
% 1.46/1.69  thf('12', plain,
% 1.46/1.69      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B_1)
% 1.46/1.69        | ((sk_B_1) = (k1_relat_1 @ sk_D_3)))),
% 1.46/1.69      inference('demod', [status(thm)], ['8', '11'])).
% 1.46/1.69  thf('13', plain,
% 1.46/1.69      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_relat_1 @ sk_D_3)))),
% 1.46/1.69      inference('sup-', [status(thm)], ['5', '12'])).
% 1.46/1.69  thf('14', plain,
% 1.46/1.69      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf('15', plain,
% 1.46/1.69      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf(redefinition_k2_relset_1, axiom,
% 1.46/1.69    (![A:$i,B:$i,C:$i]:
% 1.46/1.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.46/1.69  thf('16', plain,
% 1.46/1.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.46/1.69         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 1.46/1.69          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.46/1.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.46/1.69  thf('17', plain,
% 1.46/1.69      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('sup-', [status(thm)], ['15', '16'])).
% 1.46/1.69  thf('18', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('demod', [status(thm)], ['14', '17'])).
% 1.46/1.69  thf(d5_funct_1, axiom,
% 1.46/1.69    (![A:$i]:
% 1.46/1.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.46/1.69       ( ![B:$i]:
% 1.46/1.69         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.46/1.69           ( ![C:$i]:
% 1.46/1.69             ( ( r2_hidden @ C @ B ) <=>
% 1.46/1.69               ( ?[D:$i]:
% 1.46/1.69                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.46/1.69                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.46/1.69  thf('19', plain,
% 1.46/1.69      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.46/1.69         (((X13) != (k2_relat_1 @ X11))
% 1.46/1.69          | (r2_hidden @ (sk_D_2 @ X14 @ X11) @ (k1_relat_1 @ X11))
% 1.46/1.69          | ~ (r2_hidden @ X14 @ X13)
% 1.46/1.69          | ~ (v1_funct_1 @ X11)
% 1.46/1.69          | ~ (v1_relat_1 @ X11))),
% 1.46/1.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.46/1.69  thf('20', plain,
% 1.46/1.69      (![X11 : $i, X14 : $i]:
% 1.46/1.69         (~ (v1_relat_1 @ X11)
% 1.46/1.69          | ~ (v1_funct_1 @ X11)
% 1.46/1.69          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 1.46/1.69          | (r2_hidden @ (sk_D_2 @ X14 @ X11) @ (k1_relat_1 @ X11)))),
% 1.46/1.69      inference('simplify', [status(thm)], ['19'])).
% 1.46/1.69  thf('21', plain,
% 1.46/1.69      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))
% 1.46/1.69        | ~ (v1_funct_1 @ sk_D_3)
% 1.46/1.69        | ~ (v1_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('sup-', [status(thm)], ['18', '20'])).
% 1.46/1.69  thf('22', plain, ((v1_funct_1 @ sk_D_3)),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf('23', plain,
% 1.46/1.69      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf(cc1_relset_1, axiom,
% 1.46/1.69    (![A:$i,B:$i,C:$i]:
% 1.46/1.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.69       ( v1_relat_1 @ C ) ))).
% 1.46/1.69  thf('24', plain,
% 1.46/1.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.46/1.69         ((v1_relat_1 @ X17)
% 1.46/1.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.46/1.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.46/1.69  thf('25', plain, ((v1_relat_1 @ sk_D_3)),
% 1.46/1.69      inference('sup-', [status(thm)], ['23', '24'])).
% 1.46/1.69  thf('26', plain,
% 1.46/1.69      ((r2_hidden @ (sk_D_2 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('demod', [status(thm)], ['21', '22', '25'])).
% 1.46/1.69  thf(d2_subset_1, axiom,
% 1.46/1.69    (![A:$i,B:$i]:
% 1.46/1.69     ( ( ( v1_xboole_0 @ A ) =>
% 1.46/1.69         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.46/1.69       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.46/1.69         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.46/1.69  thf('27', plain,
% 1.46/1.69      (![X3 : $i, X4 : $i]:
% 1.46/1.69         (~ (r2_hidden @ X3 @ X4)
% 1.46/1.69          | (m1_subset_1 @ X3 @ X4)
% 1.46/1.69          | (v1_xboole_0 @ X4))),
% 1.46/1.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.46/1.69  thf(d1_xboole_0, axiom,
% 1.46/1.69    (![A:$i]:
% 1.46/1.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.46/1.69  thf('28', plain,
% 1.46/1.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.46/1.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.46/1.69  thf('29', plain,
% 1.46/1.69      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 1.46/1.69      inference('clc', [status(thm)], ['27', '28'])).
% 1.46/1.69  thf('30', plain,
% 1.46/1.69      ((m1_subset_1 @ (sk_D_2 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('sup-', [status(thm)], ['26', '29'])).
% 1.46/1.69  thf('31', plain,
% 1.46/1.69      (((m1_subset_1 @ (sk_D_2 @ sk_A @ sk_D_3) @ sk_B_1)
% 1.46/1.69        | ((sk_C_1) = (k1_xboole_0)))),
% 1.46/1.69      inference('sup+', [status(thm)], ['13', '30'])).
% 1.46/1.69  thf('32', plain,
% 1.46/1.69      (![X41 : $i]:
% 1.46/1.69         (((sk_A) != (k1_funct_1 @ sk_D_3 @ X41))
% 1.46/1.69          | ~ (m1_subset_1 @ X41 @ sk_B_1))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf('33', plain,
% 1.46/1.69      ((((sk_C_1) = (k1_xboole_0))
% 1.46/1.69        | ((sk_A) != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_A @ sk_D_3))))),
% 1.46/1.69      inference('sup-', [status(thm)], ['31', '32'])).
% 1.46/1.69  thf('34', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('demod', [status(thm)], ['14', '17'])).
% 1.46/1.69  thf('35', plain,
% 1.46/1.69      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.46/1.69         (((X13) != (k2_relat_1 @ X11))
% 1.46/1.69          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_2 @ X14 @ X11)))
% 1.46/1.69          | ~ (r2_hidden @ X14 @ X13)
% 1.46/1.69          | ~ (v1_funct_1 @ X11)
% 1.46/1.69          | ~ (v1_relat_1 @ X11))),
% 1.46/1.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.46/1.69  thf('36', plain,
% 1.46/1.69      (![X11 : $i, X14 : $i]:
% 1.46/1.69         (~ (v1_relat_1 @ X11)
% 1.46/1.69          | ~ (v1_funct_1 @ X11)
% 1.46/1.69          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 1.46/1.69          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_2 @ X14 @ X11))))),
% 1.46/1.69      inference('simplify', [status(thm)], ['35'])).
% 1.46/1.69  thf('37', plain,
% 1.46/1.69      ((((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_A @ sk_D_3)))
% 1.46/1.69        | ~ (v1_funct_1 @ sk_D_3)
% 1.46/1.69        | ~ (v1_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('sup-', [status(thm)], ['34', '36'])).
% 1.46/1.69  thf('38', plain, ((v1_funct_1 @ sk_D_3)),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf('39', plain, ((v1_relat_1 @ sk_D_3)),
% 1.46/1.69      inference('sup-', [status(thm)], ['23', '24'])).
% 1.46/1.69  thf('40', plain,
% 1.46/1.69      (((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_A @ sk_D_3)))),
% 1.46/1.69      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.46/1.69  thf('41', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 1.46/1.69      inference('demod', [status(thm)], ['33', '40'])).
% 1.46/1.69  thf('42', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.46/1.69      inference('simplify', [status(thm)], ['41'])).
% 1.46/1.69  thf('43', plain,
% 1.46/1.69      ((m1_subset_1 @ sk_D_3 @ 
% 1.46/1.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)))),
% 1.46/1.69      inference('demod', [status(thm)], ['0', '42'])).
% 1.46/1.69  thf(t38_relset_1, axiom,
% 1.46/1.69    (![A:$i,B:$i,C:$i]:
% 1.46/1.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.69       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.46/1.69         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.46/1.69  thf('44', plain,
% 1.46/1.69      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.46/1.69         (((k7_relset_1 @ X30 @ X31 @ X32 @ X30)
% 1.46/1.69            = (k2_relset_1 @ X30 @ X31 @ X32))
% 1.46/1.69          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.46/1.69      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.46/1.69  thf('45', plain,
% 1.46/1.69      (((k7_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3 @ sk_B_1)
% 1.46/1.69         = (k2_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3))),
% 1.46/1.69      inference('sup-', [status(thm)], ['43', '44'])).
% 1.46/1.69  thf('46', plain,
% 1.46/1.69      ((m1_subset_1 @ sk_D_3 @ 
% 1.46/1.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)))),
% 1.46/1.69      inference('demod', [status(thm)], ['0', '42'])).
% 1.46/1.69  thf(redefinition_k7_relset_1, axiom,
% 1.46/1.69    (![A:$i,B:$i,C:$i,D:$i]:
% 1.46/1.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.69       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.46/1.69  thf('47', plain,
% 1.46/1.69      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.46/1.69         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.46/1.69          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 1.46/1.69      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.46/1.69  thf('48', plain,
% 1.46/1.69      (![X0 : $i]:
% 1.46/1.69         ((k7_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3 @ X0)
% 1.46/1.69           = (k9_relat_1 @ sk_D_3 @ X0))),
% 1.46/1.69      inference('sup-', [status(thm)], ['46', '47'])).
% 1.46/1.69  thf('49', plain,
% 1.46/1.69      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('sup-', [status(thm)], ['15', '16'])).
% 1.46/1.69  thf('50', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.46/1.69      inference('simplify', [status(thm)], ['41'])).
% 1.46/1.69  thf('51', plain,
% 1.46/1.69      (((k2_relset_1 @ sk_B_1 @ k1_xboole_0 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('demod', [status(thm)], ['49', '50'])).
% 1.46/1.69  thf('52', plain, (((k9_relat_1 @ sk_D_3 @ sk_B_1) = (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('demod', [status(thm)], ['45', '48', '51'])).
% 1.46/1.69  thf('53', plain,
% 1.46/1.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.46/1.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.46/1.69  thf(t143_relat_1, axiom,
% 1.46/1.69    (![A:$i,B:$i,C:$i]:
% 1.46/1.69     ( ( v1_relat_1 @ C ) =>
% 1.46/1.69       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.46/1.69         ( ?[D:$i]:
% 1.46/1.69           ( ( r2_hidden @ D @ B ) & 
% 1.46/1.69             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.46/1.69             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.46/1.69  thf('54', plain,
% 1.46/1.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.46/1.69         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 1.46/1.69          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ X7)
% 1.46/1.69          | ~ (v1_relat_1 @ X9))),
% 1.46/1.69      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.46/1.69  thf('55', plain,
% 1.46/1.69      (![X0 : $i, X1 : $i]:
% 1.46/1.69         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.46/1.69          | ~ (v1_relat_1 @ X1)
% 1.46/1.69          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.46/1.69             X0))),
% 1.46/1.69      inference('sup-', [status(thm)], ['53', '54'])).
% 1.46/1.69  thf('56', plain,
% 1.46/1.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.46/1.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.46/1.69  thf('57', plain,
% 1.46/1.69      (![X0 : $i, X1 : $i]:
% 1.46/1.69         (~ (v1_relat_1 @ X1)
% 1.46/1.69          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.46/1.69          | ~ (v1_xboole_0 @ X0))),
% 1.46/1.69      inference('sup-', [status(thm)], ['55', '56'])).
% 1.46/1.69  thf('58', plain,
% 1.46/1.69      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_3))
% 1.46/1.69        | ~ (v1_xboole_0 @ sk_B_1)
% 1.46/1.69        | ~ (v1_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('sup+', [status(thm)], ['52', '57'])).
% 1.46/1.69  thf('59', plain, ((v1_relat_1 @ sk_D_3)),
% 1.46/1.69      inference('sup-', [status(thm)], ['23', '24'])).
% 1.46/1.69  thf('60', plain,
% 1.46/1.69      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_3)) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.46/1.69      inference('demod', [status(thm)], ['58', '59'])).
% 1.46/1.69  thf('61', plain,
% 1.46/1.69      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf('62', plain,
% 1.46/1.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.46/1.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.46/1.69  thf('63', plain,
% 1.46/1.69      (~ (v1_xboole_0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3))),
% 1.46/1.69      inference('sup-', [status(thm)], ['61', '62'])).
% 1.46/1.69  thf('64', plain,
% 1.46/1.69      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('sup-', [status(thm)], ['15', '16'])).
% 1.46/1.69  thf('65', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('demod', [status(thm)], ['63', '64'])).
% 1.46/1.69  thf('66', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.46/1.69      inference('clc', [status(thm)], ['60', '65'])).
% 1.46/1.69  thf('67', plain,
% 1.46/1.69      ((m1_subset_1 @ sk_D_3 @ 
% 1.46/1.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)))),
% 1.46/1.69      inference('demod', [status(thm)], ['0', '42'])).
% 1.46/1.69  thf('68', plain,
% 1.46/1.69      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.46/1.69         (((X38) != (k1_xboole_0))
% 1.46/1.69          | ((X39) = (k1_xboole_0))
% 1.46/1.69          | ((X40) = (k1_xboole_0))
% 1.46/1.69          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.46/1.69          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.46/1.69  thf('69', plain,
% 1.46/1.69      (![X39 : $i, X40 : $i]:
% 1.46/1.69         (~ (m1_subset_1 @ X40 @ 
% 1.46/1.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ k1_xboole_0)))
% 1.46/1.69          | ~ (v1_funct_2 @ X40 @ X39 @ k1_xboole_0)
% 1.46/1.69          | ((X40) = (k1_xboole_0))
% 1.46/1.69          | ((X39) = (k1_xboole_0)))),
% 1.46/1.69      inference('simplify', [status(thm)], ['68'])).
% 1.46/1.69  thf('70', plain,
% 1.46/1.69      ((((sk_B_1) = (k1_xboole_0))
% 1.46/1.69        | ((sk_D_3) = (k1_xboole_0))
% 1.46/1.69        | ~ (v1_funct_2 @ sk_D_3 @ sk_B_1 @ k1_xboole_0))),
% 1.46/1.69      inference('sup-', [status(thm)], ['67', '69'])).
% 1.46/1.69  thf('71', plain, ((v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1)),
% 1.46/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.69  thf('72', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.46/1.69      inference('simplify', [status(thm)], ['41'])).
% 1.46/1.69  thf('73', plain, ((v1_funct_2 @ sk_D_3 @ sk_B_1 @ k1_xboole_0)),
% 1.46/1.69      inference('demod', [status(thm)], ['71', '72'])).
% 1.46/1.69  thf('74', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_D_3) = (k1_xboole_0)))),
% 1.46/1.69      inference('demod', [status(thm)], ['70', '73'])).
% 1.46/1.69  thf('75', plain, (((k9_relat_1 @ sk_D_3 @ sk_B_1) = (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('demod', [status(thm)], ['45', '48', '51'])).
% 1.46/1.69  thf('76', plain,
% 1.46/1.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.46/1.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.46/1.69  thf('77', plain,
% 1.46/1.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.46/1.69         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 1.46/1.69          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ X8) @ X9)
% 1.46/1.69          | ~ (v1_relat_1 @ X9))),
% 1.46/1.69      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.46/1.69  thf('78', plain,
% 1.46/1.69      (![X0 : $i, X1 : $i]:
% 1.46/1.69         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.46/1.69          | ~ (v1_relat_1 @ X1)
% 1.46/1.69          | (r2_hidden @ 
% 1.46/1.69             (k4_tarski @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.46/1.69              (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.46/1.69             X1))),
% 1.46/1.69      inference('sup-', [status(thm)], ['76', '77'])).
% 1.46/1.69  thf('79', plain,
% 1.46/1.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.46/1.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.46/1.69  thf('80', plain,
% 1.46/1.69      (![X0 : $i, X1 : $i]:
% 1.46/1.69         (~ (v1_relat_1 @ X0)
% 1.46/1.69          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 1.46/1.69          | ~ (v1_xboole_0 @ X0))),
% 1.46/1.69      inference('sup-', [status(thm)], ['78', '79'])).
% 1.46/1.69  thf('81', plain,
% 1.46/1.69      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_3))
% 1.46/1.69        | ~ (v1_xboole_0 @ sk_D_3)
% 1.46/1.69        | ~ (v1_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('sup+', [status(thm)], ['75', '80'])).
% 1.46/1.69  thf('82', plain, ((v1_relat_1 @ sk_D_3)),
% 1.46/1.69      inference('sup-', [status(thm)], ['23', '24'])).
% 1.46/1.69  thf('83', plain,
% 1.46/1.69      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_3)) | ~ (v1_xboole_0 @ sk_D_3))),
% 1.46/1.69      inference('demod', [status(thm)], ['81', '82'])).
% 1.46/1.69  thf('84', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_D_3))),
% 1.46/1.69      inference('demod', [status(thm)], ['63', '64'])).
% 1.46/1.69  thf('85', plain, (~ (v1_xboole_0 @ sk_D_3)),
% 1.46/1.69      inference('clc', [status(thm)], ['83', '84'])).
% 1.46/1.69  thf('86', plain,
% 1.46/1.69      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) = (k1_xboole_0)))),
% 1.46/1.69      inference('sup-', [status(thm)], ['74', '85'])).
% 1.46/1.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.46/1.69  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.46/1.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.46/1.69  thf('88', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.46/1.69      inference('demod', [status(thm)], ['86', '87'])).
% 1.46/1.69  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.46/1.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.46/1.69  thf('90', plain, ($false),
% 1.46/1.69      inference('demod', [status(thm)], ['66', '88', '89'])).
% 1.46/1.69  
% 1.46/1.69  % SZS output end Refutation
% 1.46/1.69  
% 1.46/1.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
