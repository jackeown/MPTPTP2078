%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7oVZ3LB3wm

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:29 EST 2020

% Result     : Theorem 3.93s
% Output     : Refutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  216 (2030 expanded)
%              Number of leaves         :   46 ( 653 expanded)
%              Depth                    :   29
%              Number of atoms          : 1486 (19907 expanded)
%              Number of equality atoms :   92 ( 862 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('12',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

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

thf('45',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['29','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('70',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('71',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['26'])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('77',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('78',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['75','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('87',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('88',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_relset_1 @ X31 @ X32 @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','91'])).

thf('93',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['84','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['50','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X0 @ sk_B_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','96'])).

thf('98',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('103',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('107',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('109',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('112',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['105','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X0 @ sk_B_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','96'])).

thf('115',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('118',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('121',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['116','121'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('123',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X21 = X20 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ X21 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('127',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['116','121'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['124','127','128','129'])).

thf('131',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['113','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('134',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['131','134','135'])).

thf('137',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('140',plain,(
    v4_relat_1 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['125','126'])).

thf('144',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('146',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('147',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['116','121'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( sk_C_2 = sk_D )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['137','150'])).

thf('152',plain,(
    ! [X43: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X43 )
        = ( k1_funct_1 @ sk_D @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['153'])).

thf('155',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X21 = X20 )
      | ( ( k1_funct_1 @ X21 @ ( sk_C_1 @ X20 @ X21 ) )
       != ( k1_funct_1 @ X20 @ ( sk_C_1 @ X20 @ X21 ) ) )
      | ( ( k1_relat_1 @ X21 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('156',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['125','126'])).

thf('158',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['116','121'])).

thf('160',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['105','112'])).

thf('161',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('163',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['156','157','158','159','160','161','162'])).

thf('164',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['88'])).

thf('167',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    $false ),
    inference(demod,[status(thm)],['0','164','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7oVZ3LB3wm
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.93/4.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.93/4.14  % Solved by: fo/fo7.sh
% 3.93/4.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.93/4.14  % done 4930 iterations in 3.687s
% 3.93/4.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.93/4.14  % SZS output start Refutation
% 3.93/4.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.93/4.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.93/4.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.93/4.14  thf(sk_A_type, type, sk_A: $i).
% 3.93/4.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.93/4.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.93/4.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.93/4.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.93/4.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.93/4.14  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.93/4.14  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.93/4.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.93/4.14  thf(sk_B_type, type, sk_B: $i > $i).
% 3.93/4.14  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.93/4.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.93/4.14  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.93/4.14  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.93/4.14  thf(sk_D_type, type, sk_D: $i).
% 3.93/4.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.93/4.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.93/4.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.93/4.14  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.93/4.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.93/4.14  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.93/4.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.93/4.14  thf(t113_funct_2, conjecture,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.93/4.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14       ( ![D:$i]:
% 3.93/4.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.93/4.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14           ( ( ![E:$i]:
% 3.93/4.14               ( ( m1_subset_1 @ E @ A ) =>
% 3.93/4.14                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.93/4.14             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.93/4.14  thf(zf_stmt_0, negated_conjecture,
% 3.93/4.14    (~( ![A:$i,B:$i,C:$i]:
% 3.93/4.14        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.93/4.14            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14          ( ![D:$i]:
% 3.93/4.14            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.93/4.14                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14              ( ( ![E:$i]:
% 3.93/4.14                  ( ( m1_subset_1 @ E @ A ) =>
% 3.93/4.14                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.93/4.14                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.93/4.14    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 3.93/4.14  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.93/4.14  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.93/4.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.93/4.14  thf(t2_tarski, axiom,
% 3.93/4.14    (![A:$i,B:$i]:
% 3.93/4.14     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 3.93/4.14       ( ( A ) = ( B ) ) ))).
% 3.93/4.14  thf('2', plain,
% 3.93/4.14      (![X3 : $i, X4 : $i]:
% 3.93/4.14         (((X4) = (X3))
% 3.93/4.14          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 3.93/4.14          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 3.93/4.14      inference('cnf', [status(esa)], [t2_tarski])).
% 3.93/4.14  thf(d1_xboole_0, axiom,
% 3.93/4.14    (![A:$i]:
% 3.93/4.14     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.93/4.14  thf('3', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.93/4.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.93/4.14  thf('4', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 3.93/4.14          | ((X1) = (X0))
% 3.93/4.14          | ~ (v1_xboole_0 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['2', '3'])).
% 3.93/4.14  thf('5', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.93/4.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.93/4.14  thf('6', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['4', '5'])).
% 3.93/4.14  thf('7', plain,
% 3.93/4.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['1', '6'])).
% 3.93/4.14  thf('8', plain,
% 3.93/4.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['1', '6'])).
% 3.93/4.14  thf('9', plain,
% 3.93/4.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.93/4.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.93/4.14  thf(t4_subset_1, axiom,
% 3.93/4.14    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.93/4.14  thf('10', plain,
% 3.93/4.14      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 3.93/4.14      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.93/4.14  thf(cc2_relset_1, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.93/4.14       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.93/4.14  thf('11', plain,
% 3.93/4.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.93/4.14         ((v4_relat_1 @ X25 @ X26)
% 3.93/4.14          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.93/4.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.93/4.14  thf('12', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 3.93/4.14      inference('sup-', [status(thm)], ['10', '11'])).
% 3.93/4.14  thf(d18_relat_1, axiom,
% 3.93/4.14    (![A:$i,B:$i]:
% 3.93/4.14     ( ( v1_relat_1 @ B ) =>
% 3.93/4.14       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.93/4.14  thf('13', plain,
% 3.93/4.14      (![X18 : $i, X19 : $i]:
% 3.93/4.14         (~ (v4_relat_1 @ X18 @ X19)
% 3.93/4.14          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 3.93/4.14          | ~ (v1_relat_1 @ X18))),
% 3.93/4.14      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.93/4.14  thf('14', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (~ (v1_relat_1 @ k1_xboole_0)
% 3.93/4.14          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['12', '13'])).
% 3.93/4.14  thf('15', plain,
% 3.93/4.14      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 3.93/4.14      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.93/4.14  thf(cc1_relset_1, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.93/4.14       ( v1_relat_1 @ C ) ))).
% 3.93/4.14  thf('16', plain,
% 3.93/4.14      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.93/4.14         ((v1_relat_1 @ X22)
% 3.93/4.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.93/4.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.93/4.14  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.93/4.14      inference('sup-', [status(thm)], ['15', '16'])).
% 3.93/4.14  thf('18', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 3.93/4.14      inference('demod', [status(thm)], ['14', '17'])).
% 3.93/4.14  thf(t3_subset, axiom,
% 3.93/4.14    (![A:$i,B:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.93/4.14  thf('19', plain,
% 3.93/4.14      (![X12 : $i, X14 : $i]:
% 3.93/4.14         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 3.93/4.14      inference('cnf', [status(esa)], [t3_subset])).
% 3.93/4.14  thf('20', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['18', '19'])).
% 3.93/4.14  thf(l3_subset_1, axiom,
% 3.93/4.14    (![A:$i,B:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.93/4.14       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 3.93/4.14  thf('21', plain,
% 3.93/4.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.93/4.14         (~ (r2_hidden @ X8 @ X9)
% 3.93/4.14          | (r2_hidden @ X8 @ X10)
% 3.93/4.14          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 3.93/4.14      inference('cnf', [status(esa)], [l3_subset_1])).
% 3.93/4.14  thf('22', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         ((r2_hidden @ X1 @ X0)
% 3.93/4.14          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ k1_xboole_0)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['20', '21'])).
% 3.93/4.14  thf('23', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 3.93/4.14          | (r2_hidden @ (sk_B @ (k1_relat_1 @ k1_xboole_0)) @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['9', '22'])).
% 3.93/4.14  thf('24', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.93/4.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.93/4.14  thf('25', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['23', '24'])).
% 3.93/4.14  thf('26', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 3.93/4.14          | ~ (v1_xboole_0 @ X0)
% 3.93/4.14          | ~ (v1_xboole_0 @ X1))),
% 3.93/4.14      inference('sup+', [status(thm)], ['8', '25'])).
% 3.93/4.14  thf('27', plain,
% 3.93/4.14      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.93/4.14      inference('condensation', [status(thm)], ['26'])).
% 3.93/4.14  thf('28', plain,
% 3.93/4.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['1', '6'])).
% 3.93/4.14  thf('29', plain,
% 3.93/4.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['27', '28'])).
% 3.93/4.14  thf(d1_funct_2, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.93/4.14       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.93/4.14           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.93/4.14             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.93/4.14         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.93/4.14           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.93/4.14             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.93/4.14  thf(zf_stmt_1, axiom,
% 3.93/4.14    (![B:$i,A:$i]:
% 3.93/4.14     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.93/4.14       ( zip_tseitin_0 @ B @ A ) ))).
% 3.93/4.14  thf('30', plain,
% 3.93/4.14      (![X35 : $i, X36 : $i]:
% 3.93/4.14         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.93/4.14  thf(t113_zfmisc_1, axiom,
% 3.93/4.14    (![A:$i,B:$i]:
% 3.93/4.14     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.93/4.14       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.93/4.14  thf('31', plain,
% 3.93/4.14      (![X6 : $i, X7 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 3.93/4.14      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.93/4.14  thf('32', plain,
% 3.93/4.14      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.93/4.14      inference('simplify', [status(thm)], ['31'])).
% 3.93/4.14  thf('33', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.93/4.14      inference('sup+', [status(thm)], ['30', '32'])).
% 3.93/4.14  thf('34', plain,
% 3.93/4.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.93/4.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.93/4.14  thf('35', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('36', plain,
% 3.93/4.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.93/4.14         (~ (r2_hidden @ X8 @ X9)
% 3.93/4.14          | (r2_hidden @ X8 @ X10)
% 3.93/4.14          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 3.93/4.14      inference('cnf', [status(esa)], [l3_subset_1])).
% 3.93/4.14  thf('37', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.93/4.14          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 3.93/4.14      inference('sup-', [status(thm)], ['35', '36'])).
% 3.93/4.14  thf('38', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_C_2)
% 3.93/4.14        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['34', '37'])).
% 3.93/4.14  thf('39', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.93/4.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.93/4.14  thf('40', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_C_2)
% 3.93/4.14        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['38', '39'])).
% 3.93/4.14  thf('41', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.93/4.14          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 3.93/4.14          | (v1_xboole_0 @ sk_C_2))),
% 3.93/4.14      inference('sup-', [status(thm)], ['33', '40'])).
% 3.93/4.14  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.93/4.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.93/4.14  thf('43', plain,
% 3.93/4.14      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 3.93/4.14      inference('demod', [status(thm)], ['41', '42'])).
% 3.93/4.14  thf('44', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['18', '19'])).
% 3.93/4.14  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.93/4.14  thf(zf_stmt_3, axiom,
% 3.93/4.14    (![C:$i,B:$i,A:$i]:
% 3.93/4.14     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.93/4.14       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.93/4.14  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.93/4.14  thf(zf_stmt_5, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.93/4.14       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.93/4.14         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.93/4.14           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.93/4.14             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.93/4.14  thf('45', plain,
% 3.93/4.14      (![X40 : $i, X41 : $i, X42 : $i]:
% 3.93/4.14         (~ (zip_tseitin_0 @ X40 @ X41)
% 3.93/4.14          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 3.93/4.14          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.93/4.14  thf('46', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         ((zip_tseitin_1 @ (k1_relat_1 @ k1_xboole_0) @ X0 @ X1)
% 3.93/4.14          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.93/4.14      inference('sup-', [status(thm)], ['44', '45'])).
% 3.93/4.14  thf('47', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         ((v1_xboole_0 @ sk_C_2)
% 3.93/4.14          | (zip_tseitin_1 @ (k1_relat_1 @ k1_xboole_0) @ sk_B_1 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['43', '46'])).
% 3.93/4.14  thf('48', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         ((zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ X0)
% 3.93/4.14          | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.93/4.14          | (v1_xboole_0 @ sk_C_2))),
% 3.93/4.14      inference('sup+', [status(thm)], ['29', '47'])).
% 3.93/4.14  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.93/4.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.93/4.14  thf('50', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         ((zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 3.93/4.14      inference('demod', [status(thm)], ['48', '49'])).
% 3.93/4.14  thf('51', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.93/4.14      inference('sup+', [status(thm)], ['30', '32'])).
% 3.93/4.14  thf('52', plain,
% 3.93/4.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.93/4.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.93/4.14  thf('53', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('54', plain,
% 3.93/4.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.93/4.14         (~ (r2_hidden @ X8 @ X9)
% 3.93/4.14          | (r2_hidden @ X8 @ X10)
% 3.93/4.14          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 3.93/4.14      inference('cnf', [status(esa)], [l3_subset_1])).
% 3.93/4.14  thf('55', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.93/4.14          | ~ (r2_hidden @ X0 @ sk_D))),
% 3.93/4.14      inference('sup-', [status(thm)], ['53', '54'])).
% 3.93/4.14  thf('56', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_D)
% 3.93/4.14        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['52', '55'])).
% 3.93/4.14  thf('57', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.93/4.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.93/4.14  thf('58', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['56', '57'])).
% 3.93/4.14  thf('59', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.93/4.14          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 3.93/4.14          | (v1_xboole_0 @ sk_D))),
% 3.93/4.14      inference('sup-', [status(thm)], ['51', '58'])).
% 3.93/4.14  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.93/4.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.93/4.14  thf('61', plain,
% 3.93/4.14      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 3.93/4.14      inference('demod', [status(thm)], ['59', '60'])).
% 3.93/4.14  thf('62', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('63', plain,
% 3.93/4.14      (![X40 : $i, X41 : $i, X42 : $i]:
% 3.93/4.14         (~ (zip_tseitin_0 @ X40 @ X41)
% 3.93/4.14          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 3.93/4.14          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.93/4.14  thf('64', plain,
% 3.93/4.14      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.93/4.14        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['62', '63'])).
% 3.93/4.14  thf('65', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['61', '64'])).
% 3.93/4.14  thf('66', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('67', plain,
% 3.93/4.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.93/4.14         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 3.93/4.14          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 3.93/4.14          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.93/4.14  thf('68', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['66', '67'])).
% 3.93/4.14  thf('69', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf(redefinition_k1_relset_1, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.93/4.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.93/4.14  thf('70', plain,
% 3.93/4.14      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.93/4.14         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 3.93/4.14          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 3.93/4.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.93/4.14  thf('71', plain,
% 3.93/4.14      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.93/4.14      inference('sup-', [status(thm)], ['69', '70'])).
% 3.93/4.14  thf('72', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.93/4.14      inference('demod', [status(thm)], ['68', '71'])).
% 3.93/4.14  thf('73', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['65', '72'])).
% 3.93/4.14  thf('74', plain,
% 3.93/4.14      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.93/4.14      inference('condensation', [status(thm)], ['26'])).
% 3.93/4.14  thf('75', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_C_2))),
% 3.93/4.14      inference('sup+', [status(thm)], ['73', '74'])).
% 3.93/4.14  thf('76', plain,
% 3.93/4.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['1', '6'])).
% 3.93/4.14  thf('77', plain,
% 3.93/4.14      (![X6 : $i, X7 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.93/4.14      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.93/4.14  thf('78', plain,
% 3.93/4.14      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 3.93/4.14      inference('simplify', [status(thm)], ['77'])).
% 3.93/4.14  thf('79', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.93/4.14      inference('sup+', [status(thm)], ['76', '78'])).
% 3.93/4.14  thf('80', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['56', '57'])).
% 3.93/4.14  thf('81', plain,
% 3.93/4.14      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.93/4.14        | ~ (v1_xboole_0 @ sk_A)
% 3.93/4.14        | (v1_xboole_0 @ sk_D))),
% 3.93/4.14      inference('sup-', [status(thm)], ['79', '80'])).
% 3.93/4.14  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.93/4.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.93/4.14  thf('83', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 3.93/4.14      inference('demod', [status(thm)], ['81', '82'])).
% 3.93/4.14  thf('84', plain, ((~ (v1_xboole_0 @ sk_C_2) | (v1_xboole_0 @ sk_D))),
% 3.93/4.14      inference('clc', [status(thm)], ['75', '83'])).
% 3.93/4.14  thf('85', plain,
% 3.93/4.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['1', '6'])).
% 3.93/4.14  thf('86', plain,
% 3.93/4.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['1', '6'])).
% 3.93/4.14  thf('87', plain,
% 3.93/4.14      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 3.93/4.14      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.93/4.14  thf(reflexivity_r2_relset_1, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i,D:$i]:
% 3.93/4.14     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.93/4.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 3.93/4.14  thf('88', plain,
% 3.93/4.14      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.93/4.14         ((r2_relset_1 @ X31 @ X32 @ X33 @ X33)
% 3.93/4.14          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.93/4.14          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 3.93/4.14      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 3.93/4.14  thf('89', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.93/4.14         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.93/4.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.93/4.14      inference('condensation', [status(thm)], ['88'])).
% 3.93/4.14  thf('90', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.93/4.14      inference('sup-', [status(thm)], ['87', '89'])).
% 3.93/4.14  thf('91', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.93/4.14         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 3.93/4.14      inference('sup+', [status(thm)], ['86', '90'])).
% 3.93/4.14  thf('92', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.93/4.14         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 3.93/4.14          | ~ (v1_xboole_0 @ X0)
% 3.93/4.14          | ~ (v1_xboole_0 @ X1))),
% 3.93/4.14      inference('sup+', [status(thm)], ['85', '91'])).
% 3.93/4.14  thf('93', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('94', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 3.93/4.14      inference('sup-', [status(thm)], ['92', '93'])).
% 3.93/4.14  thf('95', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 3.93/4.14      inference('clc', [status(thm)], ['84', '94'])).
% 3.93/4.14  thf('96', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ X0)),
% 3.93/4.14      inference('clc', [status(thm)], ['50', '95'])).
% 3.93/4.14  thf('97', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         ((zip_tseitin_1 @ X0 @ sk_B_1 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.93/4.14      inference('sup+', [status(thm)], ['7', '96'])).
% 3.93/4.14  thf('98', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('99', plain,
% 3.93/4.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.93/4.14         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 3.93/4.14          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 3.93/4.14          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.93/4.14  thf('100', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['98', '99'])).
% 3.93/4.14  thf('101', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('102', plain,
% 3.93/4.14      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.93/4.14         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 3.93/4.14          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 3.93/4.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.93/4.14  thf('103', plain,
% 3.93/4.14      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.93/4.14      inference('sup-', [status(thm)], ['101', '102'])).
% 3.93/4.14  thf('104', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('demod', [status(thm)], ['100', '103'])).
% 3.93/4.14  thf('105', plain,
% 3.93/4.14      ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['97', '104'])).
% 3.93/4.14  thf('106', plain,
% 3.93/4.14      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 3.93/4.14      inference('demod', [status(thm)], ['59', '60'])).
% 3.93/4.14  thf('107', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('108', plain,
% 3.93/4.14      (![X40 : $i, X41 : $i, X42 : $i]:
% 3.93/4.14         (~ (zip_tseitin_0 @ X40 @ X41)
% 3.93/4.14          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 3.93/4.14          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.93/4.14  thf('109', plain,
% 3.93/4.14      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.93/4.14        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['107', '108'])).
% 3.93/4.14  thf('110', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['106', '109'])).
% 3.93/4.14  thf('111', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('demod', [status(thm)], ['100', '103'])).
% 3.93/4.14  thf('112', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['110', '111'])).
% 3.93/4.14  thf('113', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.93/4.14      inference('clc', [status(thm)], ['105', '112'])).
% 3.93/4.14  thf('114', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         ((zip_tseitin_1 @ X0 @ sk_B_1 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.93/4.14      inference('sup+', [status(thm)], ['7', '96'])).
% 3.93/4.14  thf('115', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.93/4.14      inference('demod', [status(thm)], ['68', '71'])).
% 3.93/4.14  thf('116', plain,
% 3.93/4.14      ((~ (v1_xboole_0 @ sk_C_2) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['114', '115'])).
% 3.93/4.14  thf('117', plain,
% 3.93/4.14      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 3.93/4.14      inference('demod', [status(thm)], ['41', '42'])).
% 3.93/4.14  thf('118', plain,
% 3.93/4.14      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.93/4.14        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['62', '63'])).
% 3.93/4.14  thf('119', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_C_2) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['117', '118'])).
% 3.93/4.14  thf('120', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.93/4.14      inference('demod', [status(thm)], ['68', '71'])).
% 3.93/4.14  thf('121', plain,
% 3.93/4.14      (((v1_xboole_0 @ sk_C_2) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['119', '120'])).
% 3.93/4.14  thf('122', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.93/4.14      inference('clc', [status(thm)], ['116', '121'])).
% 3.93/4.14  thf(t9_funct_1, axiom,
% 3.93/4.14    (![A:$i]:
% 3.93/4.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.93/4.14       ( ![B:$i]:
% 3.93/4.14         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.93/4.14           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.93/4.14               ( ![C:$i]:
% 3.93/4.14                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.93/4.14                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.93/4.14             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.93/4.14  thf('123', plain,
% 3.93/4.14      (![X20 : $i, X21 : $i]:
% 3.93/4.14         (~ (v1_relat_1 @ X20)
% 3.93/4.14          | ~ (v1_funct_1 @ X20)
% 3.93/4.14          | ((X21) = (X20))
% 3.93/4.14          | (r2_hidden @ (sk_C_1 @ X20 @ X21) @ (k1_relat_1 @ X21))
% 3.93/4.14          | ((k1_relat_1 @ X21) != (k1_relat_1 @ X20))
% 3.93/4.14          | ~ (v1_funct_1 @ X21)
% 3.93/4.14          | ~ (v1_relat_1 @ X21))),
% 3.93/4.14      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.93/4.14  thf('124', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((sk_A) != (k1_relat_1 @ X0))
% 3.93/4.14          | ~ (v1_relat_1 @ sk_C_2)
% 3.93/4.14          | ~ (v1_funct_1 @ sk_C_2)
% 3.93/4.14          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 3.93/4.14          | ((sk_C_2) = (X0))
% 3.93/4.14          | ~ (v1_funct_1 @ X0)
% 3.93/4.14          | ~ (v1_relat_1 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['122', '123'])).
% 3.93/4.14  thf('125', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('126', plain,
% 3.93/4.14      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.93/4.14         ((v1_relat_1 @ X22)
% 3.93/4.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.93/4.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.93/4.14  thf('127', plain, ((v1_relat_1 @ sk_C_2)),
% 3.93/4.14      inference('sup-', [status(thm)], ['125', '126'])).
% 3.93/4.14  thf('128', plain, ((v1_funct_1 @ sk_C_2)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('129', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.93/4.14      inference('clc', [status(thm)], ['116', '121'])).
% 3.93/4.14  thf('130', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((sk_A) != (k1_relat_1 @ X0))
% 3.93/4.14          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 3.93/4.14          | ((sk_C_2) = (X0))
% 3.93/4.14          | ~ (v1_funct_1 @ X0)
% 3.93/4.14          | ~ (v1_relat_1 @ X0))),
% 3.93/4.14      inference('demod', [status(thm)], ['124', '127', '128', '129'])).
% 3.93/4.14  thf('131', plain,
% 3.93/4.14      ((((sk_A) != (sk_A))
% 3.93/4.14        | ~ (v1_relat_1 @ sk_D)
% 3.93/4.14        | ~ (v1_funct_1 @ sk_D)
% 3.93/4.14        | ((sk_C_2) = (sk_D))
% 3.93/4.14        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['113', '130'])).
% 3.93/4.14  thf('132', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('133', plain,
% 3.93/4.14      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.93/4.14         ((v1_relat_1 @ X22)
% 3.93/4.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.93/4.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.93/4.14  thf('134', plain, ((v1_relat_1 @ sk_D)),
% 3.93/4.14      inference('sup-', [status(thm)], ['132', '133'])).
% 3.93/4.14  thf('135', plain, ((v1_funct_1 @ sk_D)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('136', plain,
% 3.93/4.14      ((((sk_A) != (sk_A))
% 3.93/4.14        | ((sk_C_2) = (sk_D))
% 3.93/4.14        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.93/4.14      inference('demod', [status(thm)], ['131', '134', '135'])).
% 3.93/4.14  thf('137', plain,
% 3.93/4.14      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 3.93/4.14      inference('simplify', [status(thm)], ['136'])).
% 3.93/4.14  thf('138', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('139', plain,
% 3.93/4.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.93/4.14         ((v4_relat_1 @ X25 @ X26)
% 3.93/4.14          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.93/4.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.93/4.14  thf('140', plain, ((v4_relat_1 @ sk_C_2 @ sk_A)),
% 3.93/4.14      inference('sup-', [status(thm)], ['138', '139'])).
% 3.93/4.14  thf('141', plain,
% 3.93/4.14      (![X18 : $i, X19 : $i]:
% 3.93/4.14         (~ (v4_relat_1 @ X18 @ X19)
% 3.93/4.14          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 3.93/4.14          | ~ (v1_relat_1 @ X18))),
% 3.93/4.14      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.93/4.14  thf('142', plain,
% 3.93/4.14      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['140', '141'])).
% 3.93/4.14  thf('143', plain, ((v1_relat_1 @ sk_C_2)),
% 3.93/4.14      inference('sup-', [status(thm)], ['125', '126'])).
% 3.93/4.14  thf('144', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 3.93/4.14      inference('demod', [status(thm)], ['142', '143'])).
% 3.93/4.14  thf('145', plain,
% 3.93/4.14      (![X12 : $i, X14 : $i]:
% 3.93/4.14         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 3.93/4.14      inference('cnf', [status(esa)], [t3_subset])).
% 3.93/4.14  thf('146', plain,
% 3.93/4.14      ((m1_subset_1 @ (k1_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['144', '145'])).
% 3.93/4.14  thf(t4_subset, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 3.93/4.14       ( m1_subset_1 @ A @ C ) ))).
% 3.93/4.14  thf('147', plain,
% 3.93/4.14      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.93/4.14         (~ (r2_hidden @ X15 @ X16)
% 3.93/4.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 3.93/4.14          | (m1_subset_1 @ X15 @ X17))),
% 3.93/4.14      inference('cnf', [status(esa)], [t4_subset])).
% 3.93/4.14  thf('148', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         ((m1_subset_1 @ X0 @ sk_A)
% 3.93/4.14          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['146', '147'])).
% 3.93/4.14  thf('149', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.93/4.14      inference('clc', [status(thm)], ['116', '121'])).
% 3.93/4.14  thf('150', plain,
% 3.93/4.14      (![X0 : $i]: ((m1_subset_1 @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_A))),
% 3.93/4.14      inference('demod', [status(thm)], ['148', '149'])).
% 3.93/4.14  thf('151', plain,
% 3.93/4.14      ((((sk_C_2) = (sk_D)) | (m1_subset_1 @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['137', '150'])).
% 3.93/4.14  thf('152', plain,
% 3.93/4.14      (![X43 : $i]:
% 3.93/4.14         (((k1_funct_1 @ sk_C_2 @ X43) = (k1_funct_1 @ sk_D @ X43))
% 3.93/4.14          | ~ (m1_subset_1 @ X43 @ sk_A))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('153', plain,
% 3.93/4.14      ((((sk_C_2) = (sk_D))
% 3.93/4.14        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.93/4.14            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 3.93/4.14      inference('sup-', [status(thm)], ['151', '152'])).
% 3.93/4.14  thf('154', plain,
% 3.93/4.14      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.93/4.14         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 3.93/4.14      inference('condensation', [status(thm)], ['153'])).
% 3.93/4.14  thf('155', plain,
% 3.93/4.14      (![X20 : $i, X21 : $i]:
% 3.93/4.14         (~ (v1_relat_1 @ X20)
% 3.93/4.14          | ~ (v1_funct_1 @ X20)
% 3.93/4.14          | ((X21) = (X20))
% 3.93/4.14          | ((k1_funct_1 @ X21 @ (sk_C_1 @ X20 @ X21))
% 3.93/4.14              != (k1_funct_1 @ X20 @ (sk_C_1 @ X20 @ X21)))
% 3.93/4.14          | ((k1_relat_1 @ X21) != (k1_relat_1 @ X20))
% 3.93/4.14          | ~ (v1_funct_1 @ X21)
% 3.93/4.14          | ~ (v1_relat_1 @ X21))),
% 3.93/4.14      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.93/4.14  thf('156', plain,
% 3.93/4.14      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.93/4.14          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.93/4.14        | ~ (v1_relat_1 @ sk_C_2)
% 3.93/4.14        | ~ (v1_funct_1 @ sk_C_2)
% 3.93/4.14        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 3.93/4.14        | ((sk_C_2) = (sk_D))
% 3.93/4.14        | ~ (v1_funct_1 @ sk_D)
% 3.93/4.14        | ~ (v1_relat_1 @ sk_D))),
% 3.93/4.14      inference('sup-', [status(thm)], ['154', '155'])).
% 3.93/4.14  thf('157', plain, ((v1_relat_1 @ sk_C_2)),
% 3.93/4.14      inference('sup-', [status(thm)], ['125', '126'])).
% 3.93/4.14  thf('158', plain, ((v1_funct_1 @ sk_C_2)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('159', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.93/4.14      inference('clc', [status(thm)], ['116', '121'])).
% 3.93/4.14  thf('160', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.93/4.14      inference('clc', [status(thm)], ['105', '112'])).
% 3.93/4.14  thf('161', plain, ((v1_funct_1 @ sk_D)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('162', plain, ((v1_relat_1 @ sk_D)),
% 3.93/4.14      inference('sup-', [status(thm)], ['132', '133'])).
% 3.93/4.14  thf('163', plain,
% 3.93/4.14      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.93/4.14          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.93/4.14        | ((sk_A) != (sk_A))
% 3.93/4.14        | ((sk_C_2) = (sk_D)))),
% 3.93/4.14      inference('demod', [status(thm)],
% 3.93/4.14                ['156', '157', '158', '159', '160', '161', '162'])).
% 3.93/4.14  thf('164', plain, (((sk_C_2) = (sk_D))),
% 3.93/4.14      inference('simplify', [status(thm)], ['163'])).
% 3.93/4.14  thf('165', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('166', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.93/4.14         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.93/4.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.93/4.14      inference('condensation', [status(thm)], ['88'])).
% 3.93/4.14  thf('167', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 3.93/4.14      inference('sup-', [status(thm)], ['165', '166'])).
% 3.93/4.14  thf('168', plain, ($false),
% 3.93/4.14      inference('demod', [status(thm)], ['0', '164', '167'])).
% 3.93/4.14  
% 3.93/4.14  % SZS output end Refutation
% 3.93/4.14  
% 3.93/4.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
