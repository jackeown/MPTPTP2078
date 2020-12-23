%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2v39J2kcbr

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:47 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 169 expanded)
%              Number of leaves         :   47 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  835 (2003 expanded)
%              Number of equality atoms :   42 (  80 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k9_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k9_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X26 @ X24 @ X25 ) @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_2 ),
    inference(demod,[status(thm)],['6','9'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ X28 )
      | ( X29
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('14',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k9_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( sk_D_1 @ X26 @ X24 @ X25 ) @ X24 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X52: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_2 @ X52 ) )
      | ~ ( r2_hidden @ X52 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X52 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k9_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( sk_D_1 @ X26 @ X24 @ X25 ) @ ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
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

thf('28',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_1 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r2_hidden @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X18: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_tarski @ X16 @ X14 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('38',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_E @ ( k2_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    r2_hidden @ sk_E @ sk_B ),
    inference('sup+',[status(thm)],['41','45'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('51',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_0 @ X49 @ X50 )
      | ( zip_tseitin_1 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
      | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ sk_B )
      | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference(condensation,[status(thm)],['56'])).

thf('58',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('60',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('61',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['29','58','61'])).

thf('63',plain,(
    r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference(demod,[status(thm)],['25','26','62'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('65',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['22','65'])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2v39J2kcbr
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.07/1.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.24  % Solved by: fo/fo7.sh
% 1.07/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.24  % done 440 iterations in 0.792s
% 1.07/1.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.24  % SZS output start Refutation
% 1.07/1.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.24  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.07/1.24  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.07/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.24  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.07/1.24  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.07/1.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.24  thf(sk_E_type, type, sk_E: $i).
% 1.07/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.07/1.24  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.07/1.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.24  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.07/1.24  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.07/1.24  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.07/1.24  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.07/1.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.24  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.07/1.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.24  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.07/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.24  thf(t116_funct_2, conjecture,
% 1.07/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.24     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.24       ( ![E:$i]:
% 1.07/1.24         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.07/1.24              ( ![F:$i]:
% 1.07/1.24                ( ( m1_subset_1 @ F @ A ) =>
% 1.07/1.24                  ( ~( ( r2_hidden @ F @ C ) & 
% 1.07/1.24                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 1.07/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.24    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.24        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.24            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.24          ( ![E:$i]:
% 1.07/1.24            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.07/1.24                 ( ![F:$i]:
% 1.07/1.24                   ( ( m1_subset_1 @ F @ A ) =>
% 1.07/1.24                     ( ~( ( r2_hidden @ F @ C ) & 
% 1.07/1.24                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 1.07/1.24    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 1.07/1.24  thf('0', plain,
% 1.07/1.24      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C_1))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('1', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(redefinition_k7_relset_1, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.24       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.07/1.24  thf('2', plain,
% 1.07/1.24      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.07/1.24         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.07/1.24          | ((k7_relset_1 @ X41 @ X42 @ X40 @ X43) = (k9_relat_1 @ X40 @ X43)))),
% 1.07/1.24      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.07/1.24  thf('3', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 1.07/1.24           = (k9_relat_1 @ sk_D_2 @ X0))),
% 1.07/1.24      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.24  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_2 @ sk_C_1))),
% 1.07/1.24      inference('demod', [status(thm)], ['0', '3'])).
% 1.07/1.24  thf(t143_relat_1, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( v1_relat_1 @ C ) =>
% 1.07/1.24       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.07/1.24         ( ?[D:$i]:
% 1.07/1.24           ( ( r2_hidden @ D @ B ) & 
% 1.07/1.24             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.07/1.24             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.07/1.24  thf('5', plain,
% 1.07/1.24      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.07/1.24         (~ (r2_hidden @ X25 @ (k9_relat_1 @ X26 @ X24))
% 1.07/1.24          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X26 @ X24 @ X25) @ X25) @ X26)
% 1.07/1.24          | ~ (v1_relat_1 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.07/1.24  thf('6', plain,
% 1.07/1.24      ((~ (v1_relat_1 @ sk_D_2)
% 1.07/1.24        | (r2_hidden @ 
% 1.07/1.24           (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E) @ sk_E) @ sk_D_2))),
% 1.07/1.24      inference('sup-', [status(thm)], ['4', '5'])).
% 1.07/1.24  thf('7', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(cc1_relset_1, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.24       ( v1_relat_1 @ C ) ))).
% 1.07/1.24  thf('8', plain,
% 1.07/1.24      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.07/1.24         ((v1_relat_1 @ X30)
% 1.07/1.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.07/1.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.07/1.24  thf('9', plain, ((v1_relat_1 @ sk_D_2)),
% 1.07/1.24      inference('sup-', [status(thm)], ['7', '8'])).
% 1.07/1.24  thf('10', plain,
% 1.07/1.24      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 1.07/1.24        sk_D_2)),
% 1.07/1.24      inference('demod', [status(thm)], ['6', '9'])).
% 1.07/1.24  thf(t8_funct_1, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.07/1.24       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.07/1.24         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.07/1.24           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.07/1.24  thf('11', plain,
% 1.07/1.24      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.07/1.24         (~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ X28)
% 1.07/1.24          | ((X29) = (k1_funct_1 @ X28 @ X27))
% 1.07/1.24          | ~ (v1_funct_1 @ X28)
% 1.07/1.24          | ~ (v1_relat_1 @ X28))),
% 1.07/1.24      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.07/1.24  thf('12', plain,
% 1.07/1.24      ((~ (v1_relat_1 @ sk_D_2)
% 1.07/1.24        | ~ (v1_funct_1 @ sk_D_2)
% 1.07/1.24        | ((sk_E) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.07/1.24  thf('13', plain, ((v1_relat_1 @ sk_D_2)),
% 1.07/1.24      inference('sup-', [status(thm)], ['7', '8'])).
% 1.07/1.24  thf('14', plain, ((v1_funct_1 @ sk_D_2)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('15', plain,
% 1.07/1.24      (((sk_E) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E)))),
% 1.07/1.24      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.07/1.24  thf('16', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_2 @ sk_C_1))),
% 1.07/1.24      inference('demod', [status(thm)], ['0', '3'])).
% 1.07/1.24  thf('17', plain,
% 1.07/1.24      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.07/1.24         (~ (r2_hidden @ X25 @ (k9_relat_1 @ X26 @ X24))
% 1.07/1.24          | (r2_hidden @ (sk_D_1 @ X26 @ X24 @ X25) @ X24)
% 1.07/1.24          | ~ (v1_relat_1 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.07/1.24  thf('18', plain,
% 1.07/1.24      ((~ (v1_relat_1 @ sk_D_2)
% 1.07/1.24        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 1.07/1.24      inference('sup-', [status(thm)], ['16', '17'])).
% 1.07/1.24  thf('19', plain, ((v1_relat_1 @ sk_D_2)),
% 1.07/1.24      inference('sup-', [status(thm)], ['7', '8'])).
% 1.07/1.24  thf('20', plain, ((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 1.07/1.24      inference('demod', [status(thm)], ['18', '19'])).
% 1.07/1.24  thf('21', plain,
% 1.07/1.24      (![X52 : $i]:
% 1.07/1.24         (((sk_E) != (k1_funct_1 @ sk_D_2 @ X52))
% 1.07/1.24          | ~ (r2_hidden @ X52 @ sk_C_1)
% 1.07/1.24          | ~ (m1_subset_1 @ X52 @ sk_A))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('22', plain,
% 1.07/1.24      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E) @ sk_A)
% 1.07/1.24        | ((sk_E) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['20', '21'])).
% 1.07/1.24  thf('23', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_2 @ sk_C_1))),
% 1.07/1.24      inference('demod', [status(thm)], ['0', '3'])).
% 1.07/1.24  thf('24', plain,
% 1.07/1.24      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.07/1.24         (~ (r2_hidden @ X25 @ (k9_relat_1 @ X26 @ X24))
% 1.07/1.24          | (r2_hidden @ (sk_D_1 @ X26 @ X24 @ X25) @ (k1_relat_1 @ X26))
% 1.07/1.24          | ~ (v1_relat_1 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.07/1.24  thf('25', plain,
% 1.07/1.24      ((~ (v1_relat_1 @ sk_D_2)
% 1.07/1.24        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E) @ 
% 1.07/1.24           (k1_relat_1 @ sk_D_2)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['23', '24'])).
% 1.07/1.24  thf('26', plain, ((v1_relat_1 @ sk_D_2)),
% 1.07/1.24      inference('sup-', [status(thm)], ['7', '8'])).
% 1.07/1.24  thf('27', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(d1_funct_2, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.24       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.24           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.07/1.24             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.07/1.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.24           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.07/1.24             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.07/1.24  thf(zf_stmt_1, axiom,
% 1.07/1.24    (![C:$i,B:$i,A:$i]:
% 1.07/1.24     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.07/1.24       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.07/1.24  thf('28', plain,
% 1.07/1.24      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.07/1.24         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 1.07/1.24          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 1.07/1.24          | ~ (zip_tseitin_1 @ X48 @ X47 @ X46))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.07/1.24  thf('29', plain,
% 1.07/1.24      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 1.07/1.25        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['27', '28'])).
% 1.07/1.25  thf('30', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(dt_k7_relset_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.25       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.07/1.25  thf('31', plain,
% 1.07/1.25      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.25         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.07/1.25          | (m1_subset_1 @ (k7_relset_1 @ X34 @ X35 @ X33 @ X36) @ 
% 1.07/1.25             (k1_zfmisc_1 @ X35)))),
% 1.07/1.25      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.07/1.25  thf('32', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0) @ 
% 1.07/1.25          (k1_zfmisc_1 @ sk_B))),
% 1.07/1.25      inference('sup-', [status(thm)], ['30', '31'])).
% 1.07/1.25  thf(t2_subset, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( m1_subset_1 @ A @ B ) =>
% 1.07/1.25       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.07/1.25  thf('33', plain,
% 1.07/1.25      (![X21 : $i, X22 : $i]:
% 1.07/1.25         ((r2_hidden @ X21 @ X22)
% 1.07/1.25          | (v1_xboole_0 @ X22)
% 1.07/1.25          | ~ (m1_subset_1 @ X21 @ X22))),
% 1.07/1.25      inference('cnf', [status(esa)], [t2_subset])).
% 1.07/1.25  thf('34', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 1.07/1.25          | (r2_hidden @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0) @ 
% 1.07/1.25             (k1_zfmisc_1 @ sk_B)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['32', '33'])).
% 1.07/1.25  thf(fc1_subset_1, axiom,
% 1.07/1.25    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.07/1.25  thf('35', plain, (![X18 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 1.07/1.25      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.07/1.25  thf('36', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (r2_hidden @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0) @ 
% 1.07/1.25          (k1_zfmisc_1 @ sk_B))),
% 1.07/1.25      inference('clc', [status(thm)], ['34', '35'])).
% 1.07/1.25  thf(d1_zfmisc_1, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.07/1.25       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.07/1.25  thf('37', plain,
% 1.07/1.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X16 @ X15)
% 1.07/1.25          | (r1_tarski @ X16 @ X14)
% 1.07/1.25          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 1.07/1.25      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.07/1.25  thf('38', plain,
% 1.07/1.25      (![X14 : $i, X16 : $i]:
% 1.07/1.25         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 1.07/1.25      inference('simplify', [status(thm)], ['37'])).
% 1.07/1.25  thf('39', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0) @ sk_B)),
% 1.07/1.25      inference('sup-', [status(thm)], ['36', '38'])).
% 1.07/1.25  thf(t12_xboole_1, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.07/1.25  thf('40', plain,
% 1.07/1.25      (![X10 : $i, X11 : $i]:
% 1.07/1.25         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 1.07/1.25      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.07/1.25  thf('41', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0) @ sk_B)
% 1.07/1.25           = (sk_B))),
% 1.07/1.25      inference('sup-', [status(thm)], ['39', '40'])).
% 1.07/1.25  thf('42', plain,
% 1.07/1.25      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C_1))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(d3_xboole_0, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.07/1.25       ( ![D:$i]:
% 1.07/1.25         ( ( r2_hidden @ D @ C ) <=>
% 1.07/1.25           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.07/1.25  thf('43', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X0 @ X3)
% 1.07/1.25          | (r2_hidden @ X0 @ X2)
% 1.07/1.25          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.07/1.25      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.07/1.25  thf('44', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.07/1.25         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.07/1.25      inference('simplify', [status(thm)], ['43'])).
% 1.07/1.25  thf('45', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (r2_hidden @ sk_E @ 
% 1.07/1.25          (k2_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C_1) @ X0))),
% 1.07/1.25      inference('sup-', [status(thm)], ['42', '44'])).
% 1.07/1.25  thf('46', plain, ((r2_hidden @ sk_E @ sk_B)),
% 1.07/1.25      inference('sup+', [status(thm)], ['41', '45'])).
% 1.07/1.25  thf(zf_stmt_2, axiom,
% 1.07/1.25    (![B:$i,A:$i]:
% 1.07/1.25     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.25       ( zip_tseitin_0 @ B @ A ) ))).
% 1.07/1.25  thf('47', plain,
% 1.07/1.25      (![X44 : $i, X45 : $i]:
% 1.07/1.25         ((zip_tseitin_0 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.07/1.25  thf(t5_boole, axiom,
% 1.07/1.25    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.07/1.25  thf('48', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.07/1.25      inference('cnf', [status(esa)], [t5_boole])).
% 1.07/1.25  thf('49', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.25         (((k5_xboole_0 @ X1 @ X0) = (X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.07/1.25      inference('sup+', [status(thm)], ['47', '48'])).
% 1.07/1.25  thf('50', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.07/1.25  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.07/1.25  thf(zf_stmt_5, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.25       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.07/1.25         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.25           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.07/1.25             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.07/1.25  thf('51', plain,
% 1.07/1.25      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.07/1.25         (~ (zip_tseitin_0 @ X49 @ X50)
% 1.07/1.25          | (zip_tseitin_1 @ X51 @ X49 @ X50)
% 1.07/1.25          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.07/1.25  thf('52', plain,
% 1.07/1.25      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 1.07/1.25        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.07/1.25      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.25  thf('53', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (((k5_xboole_0 @ X0 @ sk_B) = (X0))
% 1.07/1.25          | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 1.07/1.25      inference('sup-', [status(thm)], ['49', '52'])).
% 1.07/1.25  thf(t1_xboole_0, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.07/1.25       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.07/1.25  thf('54', plain,
% 1.07/1.25      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X6 @ X7)
% 1.07/1.25          | ~ (r2_hidden @ X6 @ X8)
% 1.07/1.25          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.07/1.25  thf('55', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X1 @ X0)
% 1.07/1.25          | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 1.07/1.25          | ~ (r2_hidden @ X1 @ sk_B)
% 1.07/1.25          | ~ (r2_hidden @ X1 @ X0))),
% 1.07/1.25      inference('sup-', [status(thm)], ['53', '54'])).
% 1.07/1.25  thf('56', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X1 @ sk_B)
% 1.07/1.25          | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 1.07/1.25          | ~ (r2_hidden @ X1 @ X0))),
% 1.07/1.25      inference('simplify', [status(thm)], ['55'])).
% 1.07/1.25  thf('57', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X0 @ sk_B) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 1.07/1.25      inference('condensation', [status(thm)], ['56'])).
% 1.07/1.25  thf('58', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)),
% 1.07/1.25      inference('sup-', [status(thm)], ['46', '57'])).
% 1.07/1.25  thf('59', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(redefinition_k1_relset_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.25       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.07/1.25  thf('60', plain,
% 1.07/1.25      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.07/1.25         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 1.07/1.25          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 1.07/1.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.07/1.25  thf('61', plain,
% 1.07/1.25      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 1.07/1.25      inference('sup-', [status(thm)], ['59', '60'])).
% 1.07/1.25  thf('62', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 1.07/1.25      inference('demod', [status(thm)], ['29', '58', '61'])).
% 1.07/1.25  thf('63', plain, ((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E) @ sk_A)),
% 1.07/1.25      inference('demod', [status(thm)], ['25', '26', '62'])).
% 1.07/1.25  thf(t1_subset, axiom,
% 1.07/1.25    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.07/1.25  thf('64', plain,
% 1.07/1.25      (![X19 : $i, X20 : $i]:
% 1.07/1.25         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 1.07/1.25      inference('cnf', [status(esa)], [t1_subset])).
% 1.07/1.25  thf('65', plain, ((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E) @ sk_A)),
% 1.07/1.25      inference('sup-', [status(thm)], ['63', '64'])).
% 1.07/1.25  thf('66', plain,
% 1.07/1.25      (((sk_E) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1 @ sk_E)))),
% 1.07/1.25      inference('demod', [status(thm)], ['22', '65'])).
% 1.07/1.25  thf('67', plain, ($false),
% 1.07/1.25      inference('simplify_reflect-', [status(thm)], ['15', '66'])).
% 1.07/1.25  
% 1.07/1.25  % SZS output end Refutation
% 1.07/1.25  
% 1.07/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
