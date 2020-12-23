%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DukzS2cmAy

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:15 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 135 expanded)
%              Number of leaves         :   45 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  671 (1127 expanded)
%              Number of equality atoms :   43 (  70 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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

thf('2',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_1 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r1_tarski @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('12',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_0 @ X49 @ X50 )
      | ( zip_tseitin_1 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('17',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X41 )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['3','21','24'])).

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

thf('26',plain,(
    ! [X27: $i,X29: $i,X31: $i,X32: $i] :
      ( ( X29
       != ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ X31 @ X29 )
      | ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X27 ) )
      | ( X31
       != ( k1_funct_1 @ X27 @ X32 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('27',plain,(
    ! [X27: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X27 @ X32 ) @ ( k2_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_relat_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['28','29','32'])).

thf('34',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['0','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v5_relat_1 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v5_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('41',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('50',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('52',plain,(
    ! [X4: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( X8 = X7 )
      | ( X8 = X4 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('53',plain,(
    ! [X4: $i,X7: $i,X8: $i] :
      ( ( X8 = X4 )
      | ( X8 = X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.08  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DukzS2cmAy
% 0.07/0.27  % Computer   : n023.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 14:58:06 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  % Running portfolio for 600 s
% 0.07/0.27  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.07/0.27  % Number of cores: 8
% 0.07/0.27  % Python version: Python 3.6.8
% 0.07/0.27  % Running in FO mode
% 0.11/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.11/0.47  % Solved by: fo/fo7.sh
% 0.11/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.11/0.47  % done 232 iterations in 0.091s
% 0.11/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.11/0.47  % SZS output start Refutation
% 0.11/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.11/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.11/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.11/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.11/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.11/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.11/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.11/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.11/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.11/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.11/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.11/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.11/0.47  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.11/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.11/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.11/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.11/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.11/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.11/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.11/0.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.11/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.11/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.11/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.11/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.11/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.11/0.47  thf(t65_funct_2, conjecture,
% 0.11/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.11/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.11/0.47         ( m1_subset_1 @
% 0.11/0.47           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.11/0.47       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.11/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.11/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.11/0.47        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.11/0.47            ( m1_subset_1 @
% 0.11/0.47              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.11/0.47          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.11/0.47    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.11/0.47  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.47  thf('1', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.47  thf(d1_funct_2, axiom,
% 0.11/0.47    (![A:$i,B:$i,C:$i]:
% 0.11/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.47       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.11/0.47           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.11/0.47             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.11/0.47         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.11/0.47           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.11/0.47             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.11/0.47  thf(zf_stmt_1, axiom,
% 0.11/0.47    (![C:$i,B:$i,A:$i]:
% 0.11/0.47     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.11/0.47       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.11/0.47  thf('2', plain,
% 0.11/0.47      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.11/0.47         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.11/0.47          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 0.11/0.47          | ~ (zip_tseitin_1 @ X48 @ X47 @ X46))),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.11/0.47  thf('3', plain,
% 0.11/0.47      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.11/0.47        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)))),
% 0.11/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.11/0.47  thf(zf_stmt_2, axiom,
% 0.11/0.47    (![B:$i,A:$i]:
% 0.11/0.47     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.11/0.47       ( zip_tseitin_0 @ B @ A ) ))).
% 0.11/0.47  thf('4', plain,
% 0.11/0.47      (![X44 : $i, X45 : $i]:
% 0.11/0.47         ((zip_tseitin_0 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.11/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.11/0.47  thf('5', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.11/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.11/0.47  thf(d1_xboole_0, axiom,
% 0.11/0.47    (![A:$i]:
% 0.11/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.11/0.47  thf('6', plain,
% 0.11/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.11/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.11/0.47  thf(t7_ordinal1, axiom,
% 0.11/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.11/0.47  thf('7', plain,
% 0.11/0.47      (![X33 : $i, X34 : $i]:
% 0.11/0.47         (~ (r2_hidden @ X33 @ X34) | ~ (r1_tarski @ X34 @ X33))),
% 0.11/0.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.11/0.47  thf('8', plain,
% 0.11/0.47      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.11/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.11/0.47  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.11/0.47      inference('sup-', [status(thm)], ['5', '8'])).
% 0.11/0.47  thf('10', plain,
% 0.11/0.47      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.11/0.47      inference('sup+', [status(thm)], ['4', '9'])).
% 0.11/0.47  thf('11', plain,
% 0.11/0.47      ((m1_subset_1 @ sk_D_3 @ 
% 0.11/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.47  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.11/0.47  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.11/0.47  thf(zf_stmt_5, axiom,
% 0.11/0.47    (![A:$i,B:$i,C:$i]:
% 0.11/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.47       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.11/0.47         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.11/0.47           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.11/0.47             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.11/0.47  thf('12', plain,
% 0.11/0.47      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.11/0.47         (~ (zip_tseitin_0 @ X49 @ X50)
% 0.11/0.47          | (zip_tseitin_1 @ X51 @ X49 @ X50)
% 0.11/0.47          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.11/0.47  thf('13', plain,
% 0.11/0.47      (((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.11/0.47        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.11/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.11/0.47  thf('14', plain,
% 0.11/0.47      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.11/0.47        | (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.11/0.47      inference('sup-', [status(thm)], ['10', '13'])).
% 0.11/0.47  thf(t69_enumset1, axiom,
% 0.11/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.11/0.47  thf('15', plain,
% 0.11/0.47      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.11/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.11/0.47  thf(d2_tarski, axiom,
% 0.11/0.47    (![A:$i,B:$i,C:$i]:
% 0.11/0.47     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.11/0.47       ( ![D:$i]:
% 0.11/0.47         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.11/0.47  thf('16', plain,
% 0.11/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.11/0.47         (((X5) != (X4))
% 0.11/0.47          | (r2_hidden @ X5 @ X6)
% 0.11/0.47          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.11/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.11/0.47  thf('17', plain,
% 0.11/0.47      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.11/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.11/0.47  thf('18', plain,
% 0.11/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.11/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.11/0.47  thf('19', plain,
% 0.11/0.47      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.11/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.11/0.47  thf('20', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.11/0.47      inference('sup-', [status(thm)], ['15', '19'])).
% 0.11/0.47  thf('21', plain, ((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.11/0.47      inference('clc', [status(thm)], ['14', '20'])).
% 0.11/0.47  thf('22', plain,
% 0.11/0.47      ((m1_subset_1 @ sk_D_3 @ 
% 0.11/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.11/0.47    (![A:$i,B:$i,C:$i]:
% 0.11/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.11/0.47  thf('23', plain,
% 0.11/0.47      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.11/0.47         (((k1_relset_1 @ X42 @ X43 @ X41) = (k1_relat_1 @ X41))
% 0.11/0.47          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.11/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.11/0.47  thf('24', plain,
% 0.11/0.47      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)
% 0.11/0.47         = (k1_relat_1 @ sk_D_3))),
% 0.11/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.11/0.47  thf('25', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.11/0.47      inference('demod', [status(thm)], ['3', '21', '24'])).
% 0.11/0.47  thf(d5_funct_1, axiom,
% 0.11/0.47    (![A:$i]:
% 0.11/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.11/0.47       ( ![B:$i]:
% 0.11/0.47         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.11/0.47           ( ![C:$i]:
% 0.11/0.47             ( ( r2_hidden @ C @ B ) <=>
% 0.11/0.47               ( ?[D:$i]:
% 0.11/0.47                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.11/0.47                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.11/0.47  thf('26', plain,
% 0.11/0.47      (![X27 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 0.11/0.47         (((X29) != (k2_relat_1 @ X27))
% 0.11/0.47          | (r2_hidden @ X31 @ X29)
% 0.11/0.47          | ~ (r2_hidden @ X32 @ (k1_relat_1 @ X27))
% 0.11/0.47          | ((X31) != (k1_funct_1 @ X27 @ X32))
% 0.11/0.47          | ~ (v1_funct_1 @ X27)
% 0.11/0.47          | ~ (v1_relat_1 @ X27))),
% 0.11/0.47      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.11/0.47  thf('27', plain,
% 0.11/0.47      (![X27 : $i, X32 : $i]:
% 0.11/0.47         (~ (v1_relat_1 @ X27)
% 0.11/0.47          | ~ (v1_funct_1 @ X27)
% 0.11/0.47          | ~ (r2_hidden @ X32 @ (k1_relat_1 @ X27))
% 0.11/0.47          | (r2_hidden @ (k1_funct_1 @ X27 @ X32) @ (k2_relat_1 @ X27)))),
% 0.11/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.11/0.47  thf('28', plain,
% 0.11/0.47      (![X0 : $i]:
% 0.11/0.47         (~ (r2_hidden @ X0 @ sk_A)
% 0.11/0.47          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3))
% 0.11/0.47          | ~ (v1_funct_1 @ sk_D_3)
% 0.11/0.47          | ~ (v1_relat_1 @ sk_D_3))),
% 0.11/0.47      inference('sup-', [status(thm)], ['25', '27'])).
% 0.11/0.47  thf('29', plain, ((v1_funct_1 @ sk_D_3)),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.47  thf('30', plain,
% 0.11/0.47      ((m1_subset_1 @ sk_D_3 @ 
% 0.11/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.47  thf(cc1_relset_1, axiom,
% 0.11/0.47    (![A:$i,B:$i,C:$i]:
% 0.11/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.47       ( v1_relat_1 @ C ) ))).
% 0.11/0.47  thf('31', plain,
% 0.11/0.47      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.11/0.47         ((v1_relat_1 @ X35)
% 0.11/0.47          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.11/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.11/0.47  thf('32', plain, ((v1_relat_1 @ sk_D_3)),
% 0.11/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.11/0.47  thf('33', plain,
% 0.11/0.47      (![X0 : $i]:
% 0.11/0.47         (~ (r2_hidden @ X0 @ sk_A)
% 0.11/0.47          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3)))),
% 0.11/0.47      inference('demod', [status(thm)], ['28', '29', '32'])).
% 0.11/0.47  thf('34', plain,
% 0.11/0.47      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k2_relat_1 @ sk_D_3))),
% 0.11/0.47      inference('sup-', [status(thm)], ['0', '33'])).
% 0.11/0.47  thf('35', plain,
% 0.11/0.47      ((m1_subset_1 @ sk_D_3 @ 
% 0.11/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.47  thf(cc2_relset_1, axiom,
% 0.11/0.47    (![A:$i,B:$i,C:$i]:
% 0.11/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.11/0.47  thf('36', plain,
% 0.11/0.47      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.11/0.47         ((v5_relat_1 @ X38 @ X40)
% 0.11/0.47          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.11/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.11/0.47  thf('37', plain, ((v5_relat_1 @ sk_D_3 @ (k1_tarski @ sk_B_1))),
% 0.11/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.11/0.47  thf(d19_relat_1, axiom,
% 0.11/0.47    (![A:$i,B:$i]:
% 0.11/0.47     ( ( v1_relat_1 @ B ) =>
% 0.11/0.47       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.11/0.47  thf('38', plain,
% 0.11/0.47      (![X24 : $i, X25 : $i]:
% 0.11/0.47         (~ (v5_relat_1 @ X24 @ X25)
% 0.11/0.47          | (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.11/0.47          | ~ (v1_relat_1 @ X24))),
% 0.11/0.47      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.11/0.47  thf('39', plain,
% 0.11/0.47      ((~ (v1_relat_1 @ sk_D_3)
% 0.11/0.47        | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ (k1_tarski @ sk_B_1)))),
% 0.11/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.11/0.47  thf('40', plain, ((v1_relat_1 @ sk_D_3)),
% 0.11/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.11/0.47  thf('41', plain,
% 0.11/0.47      ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ (k1_tarski @ sk_B_1))),
% 0.11/0.47      inference('demod', [status(thm)], ['39', '40'])).
% 0.11/0.47  thf(t3_subset, axiom,
% 0.11/0.47    (![A:$i,B:$i]:
% 0.11/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.11/0.47  thf('42', plain,
% 0.11/0.47      (![X18 : $i, X20 : $i]:
% 0.11/0.47         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.11/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.11/0.47  thf('43', plain,
% 0.11/0.47      ((m1_subset_1 @ (k2_relat_1 @ sk_D_3) @ 
% 0.11/0.47        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.11/0.47      inference('sup-', [status(thm)], ['41', '42'])).
% 0.11/0.47  thf(t4_subset, axiom,
% 0.11/0.47    (![A:$i,B:$i,C:$i]:
% 0.11/0.47     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.11/0.47       ( m1_subset_1 @ A @ C ) ))).
% 0.11/0.47  thf('44', plain,
% 0.11/0.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.11/0.47         (~ (r2_hidden @ X21 @ X22)
% 0.11/0.47          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.11/0.47          | (m1_subset_1 @ X21 @ X23))),
% 0.11/0.47      inference('cnf', [status(esa)], [t4_subset])).
% 0.11/0.47  thf('45', plain,
% 0.11/0.47      (![X0 : $i]:
% 0.11/0.47         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.11/0.47          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3)))),
% 0.11/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.11/0.47  thf('46', plain,
% 0.11/0.47      ((m1_subset_1 @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.11/0.47      inference('sup-', [status(thm)], ['34', '45'])).
% 0.11/0.47  thf(t2_subset, axiom,
% 0.11/0.47    (![A:$i,B:$i]:
% 0.11/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.11/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.11/0.47  thf('47', plain,
% 0.11/0.47      (![X16 : $i, X17 : $i]:
% 0.11/0.47         ((r2_hidden @ X16 @ X17)
% 0.11/0.47          | (v1_xboole_0 @ X17)
% 0.11/0.47          | ~ (m1_subset_1 @ X16 @ X17))),
% 0.11/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.11/0.47  thf('48', plain,
% 0.11/0.47      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.11/0.47        | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.11/0.47      inference('sup-', [status(thm)], ['46', '47'])).
% 0.11/0.47  thf('49', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.11/0.47      inference('sup-', [status(thm)], ['15', '19'])).
% 0.11/0.47  thf('50', plain,
% 0.11/0.47      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.11/0.47      inference('clc', [status(thm)], ['48', '49'])).
% 0.11/0.47  thf('51', plain,
% 0.11/0.47      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.11/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.11/0.47  thf('52', plain,
% 0.11/0.47      (![X4 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.11/0.47         (~ (r2_hidden @ X8 @ X6)
% 0.11/0.47          | ((X8) = (X7))
% 0.11/0.47          | ((X8) = (X4))
% 0.11/0.47          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.11/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.11/0.47  thf('53', plain,
% 0.11/0.47      (![X4 : $i, X7 : $i, X8 : $i]:
% 0.11/0.47         (((X8) = (X4))
% 0.11/0.47          | ((X8) = (X7))
% 0.11/0.47          | ~ (r2_hidden @ X8 @ (k2_tarski @ X7 @ X4)))),
% 0.11/0.47      inference('simplify', [status(thm)], ['52'])).
% 0.11/0.47  thf('54', plain,
% 0.11/0.47      (![X0 : $i, X1 : $i]:
% 0.11/0.47         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.11/0.47      inference('sup-', [status(thm)], ['51', '53'])).
% 0.11/0.47  thf('55', plain,
% 0.11/0.47      (![X0 : $i, X1 : $i]:
% 0.11/0.47         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.11/0.47      inference('simplify', [status(thm)], ['54'])).
% 0.11/0.47  thf('56', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) = (sk_B_1))),
% 0.11/0.47      inference('sup-', [status(thm)], ['50', '55'])).
% 0.11/0.47  thf('57', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) != (sk_B_1))),
% 0.11/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.47  thf('58', plain, ($false),
% 0.11/0.47      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.11/0.47  
% 0.11/0.47  % SZS output end Refutation
% 0.11/0.47  
% 0.11/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
