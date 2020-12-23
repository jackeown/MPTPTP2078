%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HBhlmBhB1H

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:49 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 414 expanded)
%              Number of leaves         :   44 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  856 (4330 expanded)
%              Number of equality atoms :   58 ( 205 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X28 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_partfun1 @ X29 @ X30 )
      | ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('9',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_partfun1 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_partfun1 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['12'])).

thf('16',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['12'])).

thf('21',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['16','19','20'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['13','21'])).

thf('23',plain,(
    ~ ( v1_partfun1 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['11','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_B_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

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

thf('27',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('29',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['13','21'])).

thf('38',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['30','38'])).

thf('40',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','39'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) @ X16 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['26','40','48'])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('51',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf(s3_funct_1__e7_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = np__1 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('53',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('54',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( sk_B @ X21 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('60',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf('62',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('65',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X34 ) ) )
      | ( v1_partfun1 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_partfun1 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('69',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k9_relat_1 @ X13 @ X14 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','72'])).

thf('74',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['57'])).

thf('75',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( sk_B @ X21 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('78',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('79',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf('83',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['74','75'])).

thf('84',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['67','81','82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['23','51','52','60','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HBhlmBhB1H
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 253 iterations in 0.140s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.43/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.62  thf(np__1_type, type, np__1: $i).
% 0.43/0.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.62  thf(t4_funct_2, conjecture,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.62       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.43/0.62         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.43/0.62           ( m1_subset_1 @
% 0.43/0.62             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i]:
% 0.43/0.62        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.62          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.43/0.62            ( ( v1_funct_1 @ B ) & 
% 0.43/0.62              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.43/0.62              ( m1_subset_1 @
% 0.43/0.62                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.43/0.62  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d10_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.62  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.43/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.43/0.62  thf(t11_relset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ C ) =>
% 0.43/0.62       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.43/0.62           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.43/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.43/0.62         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.43/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X26) @ X28)
% 0.43/0.62          | (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.43/0.62          | ~ (v1_relat_1 @ X26))),
% 0.43/0.62      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | (m1_subset_1 @ X0 @ 
% 0.43/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.43/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (((m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.43/0.62        | ~ (v1_relat_1 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '4'])).
% 0.43/0.62  thf('6', plain, ((v1_relat_1 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf(cc1_funct_2, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.43/0.62         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.43/0.62         (~ (v1_funct_1 @ X29)
% 0.43/0.62          | ~ (v1_partfun1 @ X29 @ X30)
% 0.43/0.62          | (v1_funct_2 @ X29 @ X30 @ X31)
% 0.43/0.62          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.43/0.62        | ~ (v1_partfun1 @ sk_B_1 @ (k1_relat_1 @ sk_B_1))
% 0.43/0.62        | ~ (v1_funct_1 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.62  thf('10', plain, ((v1_funct_1 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.43/0.62        | ~ (v1_partfun1 @ sk_B_1 @ (k1_relat_1 @ sk_B_1)))),
% 0.43/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      ((~ (v1_funct_1 @ sk_B_1)
% 0.43/0.62        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.43/0.62        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.43/0.62         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('split', [status(esa)], ['12'])).
% 0.43/0.62  thf('14', plain, ((v1_funct_1 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('15', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.43/0.62      inference('split', [status(esa)], ['12'])).
% 0.43/0.62  thf('16', plain, (((v1_funct_1 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.43/0.62         <= (~
% 0.43/0.62             ((m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.43/0.62      inference('split', [status(esa)], ['12'])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (((m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.43/0.62       ~
% 0.43/0.62       ((m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.43/0.62       ~ ((v1_funct_1 @ sk_B_1))),
% 0.43/0.62      inference('split', [status(esa)], ['12'])).
% 0.43/0.62  thf('21', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['16', '19', '20'])).
% 0.43/0.62  thf('22', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['13', '21'])).
% 0.43/0.62  thf('23', plain, (~ (v1_partfun1 @ sk_B_1 @ (k1_relat_1 @ sk_B_1))),
% 0.43/0.62      inference('clc', [status(thm)], ['11', '22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf(t3_subset, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X7 : $i, X8 : $i]:
% 0.43/0.62         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      ((r1_tarski @ sk_B_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf(d1_funct_2, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.43/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.43/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.43/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_1, axiom,
% 0.43/0.62    (![B:$i,A:$i]:
% 0.43/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X35 : $i, X36 : $i]:
% 0.43/0.62         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.43/0.62  thf(zf_stmt_3, axiom,
% 0.43/0.62    (![C:$i,B:$i,A:$i]:
% 0.43/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.43/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.43/0.62  thf(zf_stmt_5, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.43/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.43/0.62         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.43/0.62          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.43/0.62          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.43/0.62        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ 
% 0.43/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.43/0.62         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.43/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.43/0.62         = (k1_relat_1 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.43/0.62         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.43/0.62          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.43/0.62          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.43/0.62        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.43/0.62        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.43/0.62        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['35'])).
% 0.43/0.62  thf('37', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['13', '21'])).
% 0.43/0.62  thf('38', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.43/0.62      inference('clc', [status(thm)], ['36', '37'])).
% 0.43/0.62  thf('39', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.43/0.62      inference('clc', [status(thm)], ['30', '38'])).
% 0.43/0.62  thf('40', plain, (((sk_A) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['27', '39'])).
% 0.43/0.62  thf(t194_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (![X15 : $i, X16 : $i]:
% 0.43/0.62         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X15 @ X16)) @ X16)),
% 0.43/0.62      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.43/0.62  thf(t3_xboole_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf(t64_relat_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ A ) =>
% 0.43/0.62       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.62           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.62         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X19 : $i]:
% 0.43/0.62         (((k2_relat_1 @ X19) != (k1_xboole_0))
% 0.43/0.62          | ((X19) = (k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X19))),
% 0.43/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.43/0.62          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.43/0.62  thf(fc6_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.62          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.43/0.62  thf('49', plain, ((r1_tarski @ sk_B_1 @ k1_xboole_0)),
% 0.43/0.62      inference('demod', [status(thm)], ['26', '40', '48'])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.43/0.62  thf('51', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.43/0.62  thf('52', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.43/0.62  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ?[B:$i]:
% 0.43/0.62       ( ( ![C:$i]:
% 0.43/0.62           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.43/0.62         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.43/0.62         ( v1_relat_1 @ B ) ) ))).
% 0.43/0.62  thf('53', plain, (![X21 : $i]: ((k1_relat_1 @ (sk_B @ X21)) = (X21))),
% 0.43/0.62      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (![X19 : $i]:
% 0.43/0.62         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.43/0.62          | ((X19) = (k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X19))),
% 0.43/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) != (k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.43/0.62          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf('56', plain, (![X21 : $i]: (v1_relat_1 @ (sk_B @ X21))),
% 0.43/0.62      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.43/0.62  thf('57', plain,
% 0.43/0.62      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['55', '56'])).
% 0.43/0.62  thf('58', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['57'])).
% 0.43/0.62  thf('59', plain, (![X21 : $i]: ((k1_relat_1 @ (sk_B @ X21)) = (X21))),
% 0.43/0.62      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.43/0.62  thf('60', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['58', '59'])).
% 0.43/0.62  thf('61', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['58', '59'])).
% 0.43/0.62  thf('62', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.43/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.43/0.62  thf('63', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | (m1_subset_1 @ X0 @ 
% 0.43/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.43/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('64', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((m1_subset_1 @ X0 @ 
% 0.43/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.43/0.62  thf(cc1_partfun1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( v1_xboole_0 @ A ) =>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.43/0.62  thf('65', plain,
% 0.43/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.43/0.62         (~ (v1_xboole_0 @ X32)
% 0.43/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X34)))
% 0.43/0.62          | (v1_partfun1 @ X33 @ X32))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.43/0.62  thf('66', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.43/0.62          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['64', '65'])).
% 0.43/0.62  thf('67', plain,
% 0.43/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.43/0.62        | (v1_partfun1 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.43/0.62        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['61', '66'])).
% 0.43/0.62  thf('68', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['58', '59'])).
% 0.43/0.62  thf(t149_relat_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ A ) =>
% 0.43/0.62       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.62  thf('69', plain,
% 0.43/0.62      (![X12 : $i]:
% 0.43/0.62         (((k9_relat_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X12))),
% 0.43/0.62      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.43/0.62  thf(t151_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ B ) =>
% 0.43/0.62       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.43/0.62         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.43/0.62  thf('70', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i]:
% 0.43/0.62         (((k9_relat_1 @ X13 @ X14) != (k1_xboole_0))
% 0.43/0.62          | (r1_xboole_0 @ (k1_relat_1 @ X13) @ X14)
% 0.43/0.62          | ~ (v1_relat_1 @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.43/0.62  thf('71', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0)
% 0.43/0.62          | ~ (v1_relat_1 @ X0)
% 0.43/0.62          | (r1_xboole_0 @ (k1_relat_1 @ X0) @ k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['69', '70'])).
% 0.43/0.62  thf('72', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['71'])).
% 0.43/0.62  thf('73', plain,
% 0.43/0.62      (((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.43/0.62        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['68', '72'])).
% 0.43/0.62  thf('74', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['57'])).
% 0.43/0.62  thf('75', plain, (![X21 : $i]: (v1_relat_1 @ (sk_B @ X21))),
% 0.43/0.62      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.43/0.62  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.62      inference('sup+', [status(thm)], ['74', '75'])).
% 0.43/0.62  thf('77', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('demod', [status(thm)], ['73', '76'])).
% 0.43/0.62  thf(t69_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.43/0.62       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.43/0.62  thf('78', plain,
% 0.43/0.62      (![X4 : $i, X5 : $i]:
% 0.43/0.62         (~ (r1_xboole_0 @ X4 @ X5)
% 0.43/0.62          | ~ (r1_tarski @ X4 @ X5)
% 0.43/0.62          | (v1_xboole_0 @ X4))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.43/0.62  thf('79', plain,
% 0.43/0.62      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.43/0.62  thf('80', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.43/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.43/0.62  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('demod', [status(thm)], ['79', '80'])).
% 0.43/0.62  thf('82', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['58', '59'])).
% 0.43/0.62  thf('83', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.62      inference('sup+', [status(thm)], ['74', '75'])).
% 0.43/0.62  thf('84', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('demod', [status(thm)], ['67', '81', '82', '83'])).
% 0.43/0.62  thf('85', plain, ($false),
% 0.43/0.62      inference('demod', [status(thm)], ['23', '51', '52', '60', '84'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
