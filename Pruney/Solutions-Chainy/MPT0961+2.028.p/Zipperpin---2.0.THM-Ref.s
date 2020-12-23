%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BAjPS1nvdP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:42 EST 2020

% Result     : Theorem 5.51s
% Output     : Refutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 193 expanded)
%              Number of leaves         :   33 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  681 (1555 expanded)
%              Number of equality atoms :   31 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X23 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('42',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('45',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('52',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['45','50','51'])).

thf('53',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['42','52'])).

thf('54',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BAjPS1nvdP
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:19:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.51/5.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.51/5.72  % Solved by: fo/fo7.sh
% 5.51/5.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.51/5.72  % done 4330 iterations in 5.269s
% 5.51/5.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.51/5.72  % SZS output start Refutation
% 5.51/5.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.51/5.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.51/5.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.51/5.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.51/5.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.51/5.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.51/5.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.51/5.72  thf(sk_A_type, type, sk_A: $i).
% 5.51/5.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.51/5.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.51/5.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.51/5.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.51/5.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.51/5.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.51/5.72  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.51/5.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.51/5.72  thf(d1_funct_2, axiom,
% 5.51/5.72    (![A:$i,B:$i,C:$i]:
% 5.51/5.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.51/5.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.51/5.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.51/5.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.51/5.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.51/5.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.51/5.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.51/5.72  thf(zf_stmt_0, axiom,
% 5.51/5.72    (![B:$i,A:$i]:
% 5.51/5.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.51/5.72       ( zip_tseitin_0 @ B @ A ) ))).
% 5.51/5.72  thf('0', plain,
% 5.51/5.72      (![X24 : $i, X25 : $i]:
% 5.51/5.72         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 5.51/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.51/5.72  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.51/5.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.51/5.72  thf('2', plain,
% 5.51/5.72      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.51/5.72      inference('sup+', [status(thm)], ['0', '1'])).
% 5.51/5.72  thf(dt_k2_subset_1, axiom,
% 5.51/5.72    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.51/5.72  thf('3', plain,
% 5.51/5.72      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 5.51/5.72      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 5.51/5.72  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.51/5.72  thf('4', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 5.51/5.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.51/5.72  thf('5', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 5.51/5.72      inference('demod', [status(thm)], ['3', '4'])).
% 5.51/5.72  thf(t3_subset, axiom,
% 5.51/5.72    (![A:$i,B:$i]:
% 5.51/5.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.51/5.72  thf('6', plain,
% 5.51/5.72      (![X7 : $i, X8 : $i]:
% 5.51/5.72         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 5.51/5.72      inference('cnf', [status(esa)], [t3_subset])).
% 5.51/5.72  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.51/5.72      inference('sup-', [status(thm)], ['5', '6'])).
% 5.51/5.72  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.51/5.72      inference('sup-', [status(thm)], ['5', '6'])).
% 5.51/5.72  thf(t11_relset_1, axiom,
% 5.51/5.72    (![A:$i,B:$i,C:$i]:
% 5.51/5.72     ( ( v1_relat_1 @ C ) =>
% 5.51/5.72       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 5.51/5.72           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 5.51/5.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 5.51/5.72  thf('9', plain,
% 5.51/5.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.51/5.72         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 5.51/5.72          | ~ (r1_tarski @ (k2_relat_1 @ X21) @ X23)
% 5.51/5.72          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 5.51/5.72          | ~ (v1_relat_1 @ X21))),
% 5.51/5.72      inference('cnf', [status(esa)], [t11_relset_1])).
% 5.51/5.72  thf('10', plain,
% 5.51/5.72      (![X0 : $i, X1 : $i]:
% 5.51/5.72         (~ (v1_relat_1 @ X0)
% 5.51/5.72          | (m1_subset_1 @ X0 @ 
% 5.51/5.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 5.51/5.72          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 5.51/5.72      inference('sup-', [status(thm)], ['8', '9'])).
% 5.51/5.72  thf('11', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         ((m1_subset_1 @ X0 @ 
% 5.51/5.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('sup-', [status(thm)], ['7', '10'])).
% 5.51/5.72  thf(cc4_relset_1, axiom,
% 5.51/5.72    (![A:$i,B:$i]:
% 5.51/5.72     ( ( v1_xboole_0 @ A ) =>
% 5.51/5.72       ( ![C:$i]:
% 5.51/5.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 5.51/5.72           ( v1_xboole_0 @ C ) ) ) ))).
% 5.51/5.72  thf('12', plain,
% 5.51/5.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.51/5.72         (~ (v1_xboole_0 @ X15)
% 5.51/5.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 5.51/5.72          | (v1_xboole_0 @ X16))),
% 5.51/5.72      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.51/5.72  thf('13', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (~ (v1_relat_1 @ X0)
% 5.51/5.72          | (v1_xboole_0 @ X0)
% 5.51/5.72          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 5.51/5.72      inference('sup-', [status(thm)], ['11', '12'])).
% 5.51/5.72  thf('14', plain,
% 5.51/5.72      (![X0 : $i, X1 : $i]:
% 5.51/5.72         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 5.51/5.72          | (v1_xboole_0 @ X0)
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('sup-', [status(thm)], ['2', '13'])).
% 5.51/5.72  thf('15', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         ((m1_subset_1 @ X0 @ 
% 5.51/5.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('sup-', [status(thm)], ['7', '10'])).
% 5.51/5.72  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.51/5.72  thf(zf_stmt_2, axiom,
% 5.51/5.72    (![C:$i,B:$i,A:$i]:
% 5.51/5.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.51/5.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.51/5.72  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 5.51/5.72  thf(zf_stmt_4, axiom,
% 5.51/5.72    (![A:$i,B:$i,C:$i]:
% 5.51/5.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.51/5.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.51/5.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.51/5.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.51/5.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.51/5.72  thf('16', plain,
% 5.51/5.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.51/5.72         (~ (zip_tseitin_0 @ X29 @ X30)
% 5.51/5.72          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 5.51/5.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 5.51/5.72      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.51/5.72  thf('17', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (~ (v1_relat_1 @ X0)
% 5.51/5.72          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 5.51/5.72          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 5.51/5.72      inference('sup-', [status(thm)], ['15', '16'])).
% 5.51/5.72  thf('18', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (~ (v1_relat_1 @ X0)
% 5.51/5.72          | (v1_xboole_0 @ X0)
% 5.51/5.72          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('sup-', [status(thm)], ['14', '17'])).
% 5.51/5.72  thf('19', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 5.51/5.72          | (v1_xboole_0 @ X0)
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('simplify', [status(thm)], ['18'])).
% 5.51/5.72  thf(fc11_relat_1, axiom,
% 5.51/5.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 5.51/5.72  thf('20', plain,
% 5.51/5.72      (![X13 : $i]:
% 5.51/5.72         ((v1_xboole_0 @ (k2_relat_1 @ X13)) | ~ (v1_xboole_0 @ X13))),
% 5.51/5.72      inference('cnf', [status(esa)], [fc11_relat_1])).
% 5.51/5.72  thf(l13_xboole_0, axiom,
% 5.51/5.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 5.51/5.72  thf('21', plain,
% 5.51/5.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.51/5.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.51/5.72  thf('22', plain,
% 5.51/5.72      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 5.51/5.72      inference('sup-', [status(thm)], ['20', '21'])).
% 5.51/5.72  thf(t65_relat_1, axiom,
% 5.51/5.72    (![A:$i]:
% 5.51/5.72     ( ( v1_relat_1 @ A ) =>
% 5.51/5.72       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 5.51/5.72         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 5.51/5.72  thf('23', plain,
% 5.51/5.72      (![X14 : $i]:
% 5.51/5.72         (((k2_relat_1 @ X14) != (k1_xboole_0))
% 5.51/5.72          | ((k1_relat_1 @ X14) = (k1_xboole_0))
% 5.51/5.72          | ~ (v1_relat_1 @ X14))),
% 5.51/5.72      inference('cnf', [status(esa)], [t65_relat_1])).
% 5.51/5.72  thf('24', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (((k1_xboole_0) != (k1_xboole_0))
% 5.51/5.72          | ~ (v1_xboole_0 @ X0)
% 5.51/5.72          | ~ (v1_relat_1 @ X0)
% 5.51/5.72          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 5.51/5.72      inference('sup-', [status(thm)], ['22', '23'])).
% 5.51/5.72  thf('25', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 5.51/5.72          | ~ (v1_relat_1 @ X0)
% 5.51/5.72          | ~ (v1_xboole_0 @ X0))),
% 5.51/5.72      inference('simplify', [status(thm)], ['24'])).
% 5.51/5.72  thf('26', plain,
% 5.51/5.72      (![X24 : $i, X25 : $i]:
% 5.51/5.72         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 5.51/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.72  thf('27', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 5.51/5.72      inference('simplify', [status(thm)], ['26'])).
% 5.51/5.72  thf('28', plain,
% 5.51/5.72      (![X0 : $i, X1 : $i]:
% 5.51/5.72         ((zip_tseitin_0 @ X1 @ (k1_relat_1 @ X0))
% 5.51/5.72          | ~ (v1_xboole_0 @ X0)
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('sup+', [status(thm)], ['25', '27'])).
% 5.51/5.72  thf('29', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (~ (v1_relat_1 @ X0)
% 5.51/5.72          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 5.51/5.72          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 5.51/5.72      inference('sup-', [status(thm)], ['15', '16'])).
% 5.51/5.72  thf('30', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (~ (v1_relat_1 @ X0)
% 5.51/5.72          | ~ (v1_xboole_0 @ X0)
% 5.51/5.72          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('sup-', [status(thm)], ['28', '29'])).
% 5.51/5.72  thf('31', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 5.51/5.72          | ~ (v1_xboole_0 @ X0)
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('simplify', [status(thm)], ['30'])).
% 5.51/5.72  thf('32', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (~ (v1_relat_1 @ X0)
% 5.51/5.72          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 5.51/5.72      inference('clc', [status(thm)], ['19', '31'])).
% 5.51/5.72  thf('33', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         ((m1_subset_1 @ X0 @ 
% 5.51/5.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('sup-', [status(thm)], ['7', '10'])).
% 5.51/5.72  thf(redefinition_k1_relset_1, axiom,
% 5.51/5.72    (![A:$i,B:$i,C:$i]:
% 5.51/5.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.51/5.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.51/5.72  thf('34', plain,
% 5.51/5.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.51/5.72         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 5.51/5.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.51/5.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.51/5.72  thf('35', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (~ (v1_relat_1 @ X0)
% 5.51/5.72          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 5.51/5.72              = (k1_relat_1 @ X0)))),
% 5.51/5.72      inference('sup-', [status(thm)], ['33', '34'])).
% 5.51/5.72  thf('36', plain,
% 5.51/5.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.51/5.72         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 5.51/5.72          | (v1_funct_2 @ X28 @ X26 @ X27)
% 5.51/5.72          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 5.51/5.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.51/5.72  thf('37', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 5.51/5.72          | ~ (v1_relat_1 @ X0)
% 5.51/5.72          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 5.51/5.72          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 5.51/5.72      inference('sup-', [status(thm)], ['35', '36'])).
% 5.51/5.72  thf('38', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 5.51/5.72          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('simplify', [status(thm)], ['37'])).
% 5.51/5.72  thf('39', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         (~ (v1_relat_1 @ X0)
% 5.51/5.72          | ~ (v1_relat_1 @ X0)
% 5.51/5.72          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 5.51/5.72      inference('sup-', [status(thm)], ['32', '38'])).
% 5.51/5.72  thf('40', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('simplify', [status(thm)], ['39'])).
% 5.51/5.72  thf(t3_funct_2, conjecture,
% 5.51/5.72    (![A:$i]:
% 5.51/5.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.51/5.72       ( ( v1_funct_1 @ A ) & 
% 5.51/5.72         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 5.51/5.72         ( m1_subset_1 @
% 5.51/5.72           A @ 
% 5.51/5.72           ( k1_zfmisc_1 @
% 5.51/5.72             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 5.51/5.72  thf(zf_stmt_5, negated_conjecture,
% 5.51/5.72    (~( ![A:$i]:
% 5.51/5.72        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.51/5.72          ( ( v1_funct_1 @ A ) & 
% 5.51/5.72            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 5.51/5.72            ( m1_subset_1 @
% 5.51/5.72              A @ 
% 5.51/5.72              ( k1_zfmisc_1 @
% 5.51/5.72                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 5.51/5.72    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 5.51/5.72  thf('41', plain,
% 5.51/5.72      ((~ (v1_funct_1 @ sk_A)
% 5.51/5.72        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 5.51/5.72        | ~ (m1_subset_1 @ sk_A @ 
% 5.51/5.72             (k1_zfmisc_1 @ 
% 5.51/5.72              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 5.51/5.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.51/5.72  thf('42', plain,
% 5.51/5.72      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 5.51/5.72         <= (~
% 5.51/5.72             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 5.51/5.72      inference('split', [status(esa)], ['41'])).
% 5.51/5.72  thf('43', plain, ((v1_funct_1 @ sk_A)),
% 5.51/5.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.51/5.72  thf('44', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 5.51/5.72      inference('split', [status(esa)], ['41'])).
% 5.51/5.72  thf('45', plain, (((v1_funct_1 @ sk_A))),
% 5.51/5.72      inference('sup-', [status(thm)], ['43', '44'])).
% 5.51/5.72  thf('46', plain,
% 5.51/5.72      (![X0 : $i]:
% 5.51/5.72         ((m1_subset_1 @ X0 @ 
% 5.51/5.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 5.51/5.72          | ~ (v1_relat_1 @ X0))),
% 5.51/5.72      inference('sup-', [status(thm)], ['7', '10'])).
% 5.51/5.72  thf('47', plain,
% 5.51/5.72      ((~ (m1_subset_1 @ sk_A @ 
% 5.51/5.72           (k1_zfmisc_1 @ 
% 5.51/5.72            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 5.51/5.72         <= (~
% 5.51/5.72             ((m1_subset_1 @ sk_A @ 
% 5.51/5.72               (k1_zfmisc_1 @ 
% 5.51/5.72                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 5.51/5.72      inference('split', [status(esa)], ['41'])).
% 5.51/5.72  thf('48', plain,
% 5.51/5.72      ((~ (v1_relat_1 @ sk_A))
% 5.51/5.72         <= (~
% 5.51/5.72             ((m1_subset_1 @ sk_A @ 
% 5.51/5.72               (k1_zfmisc_1 @ 
% 5.51/5.72                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 5.51/5.72      inference('sup-', [status(thm)], ['46', '47'])).
% 5.51/5.72  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 5.51/5.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.51/5.72  thf('50', plain,
% 5.51/5.72      (((m1_subset_1 @ sk_A @ 
% 5.51/5.72         (k1_zfmisc_1 @ 
% 5.51/5.72          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 5.51/5.72      inference('demod', [status(thm)], ['48', '49'])).
% 5.51/5.72  thf('51', plain,
% 5.51/5.72      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 5.51/5.72       ~
% 5.51/5.72       ((m1_subset_1 @ sk_A @ 
% 5.51/5.72         (k1_zfmisc_1 @ 
% 5.51/5.72          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 5.51/5.72       ~ ((v1_funct_1 @ sk_A))),
% 5.51/5.72      inference('split', [status(esa)], ['41'])).
% 5.51/5.72  thf('52', plain,
% 5.51/5.72      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 5.51/5.72      inference('sat_resolution*', [status(thm)], ['45', '50', '51'])).
% 5.51/5.72  thf('53', plain,
% 5.51/5.72      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 5.51/5.72      inference('simpl_trail', [status(thm)], ['42', '52'])).
% 5.51/5.72  thf('54', plain, (~ (v1_relat_1 @ sk_A)),
% 5.51/5.72      inference('sup-', [status(thm)], ['40', '53'])).
% 5.51/5.72  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 5.51/5.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.51/5.72  thf('56', plain, ($false), inference('demod', [status(thm)], ['54', '55'])).
% 5.51/5.72  
% 5.51/5.72  % SZS output end Refutation
% 5.51/5.72  
% 5.51/5.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
