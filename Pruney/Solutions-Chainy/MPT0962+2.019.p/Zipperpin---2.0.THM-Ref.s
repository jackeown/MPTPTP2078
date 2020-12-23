%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MVOsVDhyPq

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:51 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 320 expanded)
%              Number of leaves         :   34 ( 107 expanded)
%              Depth                    :   18
%              Number of atoms          :  873 (2861 expanded)
%              Number of equality atoms :   48 ( 105 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('17',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','20','21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('24',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['12','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X24: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X11: $i] :
      ( ( r1_xboole_0 @ X11 @ X11 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('38',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('48',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('50',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','42'])).

thf('57',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('64',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('69',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('72',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X24: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('75',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('76',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k1_relat_1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ( ( k1_relat_1 @ X0 )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('81',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_funct_2 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
        | ~ ( v1_xboole_0 @ X0 )
        | ( zip_tseitin_0 @ sk_A @ X1 ) )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
        | ( zip_tseitin_0 @ sk_A @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
        | ( zip_tseitin_0 @ sk_A @ X0 ) )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
        | ~ ( v1_xboole_0 @ sk_B_1 )
        | ( zip_tseitin_0 @ sk_A @ X0 ) )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['54','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_A @ X0 )
        | ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_A @ X0 )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','87'])).

thf('89',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','20','21'])).

thf('90',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(simpl_trail,[status(thm)],['88','89'])).

thf('91',plain,(
    zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['24','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MVOsVDhyPq
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 517 iterations in 0.282s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.54/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.74  thf(t4_funct_2, conjecture,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.54/0.74         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.54/0.74           ( m1_subset_1 @
% 0.54/0.74             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i,B:$i]:
% 0.54/0.74        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.54/0.74            ( ( v1_funct_1 @ B ) & 
% 0.54/0.74              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.54/0.74              ( m1_subset_1 @
% 0.54/0.74                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.54/0.74  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(d10_xboole_0, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.74  thf('1', plain,
% 0.54/0.74      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.54/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.74  thf('2', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.54/0.74      inference('simplify', [status(thm)], ['1'])).
% 0.54/0.74  thf(t11_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ C ) =>
% 0.54/0.74       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.54/0.74           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.54/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.54/0.74         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.54/0.74          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 0.54/0.74          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.54/0.74          | ~ (v1_relat_1 @ X29))),
% 0.54/0.74      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.54/0.74  thf('4', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | (m1_subset_1 @ X0 @ 
% 0.54/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.54/0.74          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf('5', plain,
% 0.54/0.74      (((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['0', '4'])).
% 0.54/0.74  thf('6', plain, ((v1_relat_1 @ sk_B_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('7', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.74  thf('8', plain,
% 0.54/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.74         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.54/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.74  thf('9', plain,
% 0.54/0.74      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.54/0.74         = (k1_relat_1 @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.74  thf(d1_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.54/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.54/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.54/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_1, axiom,
% 0.54/0.74    (![C:$i,B:$i,A:$i]:
% 0.54/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.54/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.54/0.74  thf('10', plain,
% 0.54/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.74         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 0.54/0.74          | (v1_funct_2 @ X36 @ X34 @ X35)
% 0.54/0.74          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.74  thf('11', plain,
% 0.54/0.74      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.54/0.74        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.54/0.74        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.74  thf('12', plain,
% 0.54/0.74      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.54/0.74        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.54/0.74      inference('simplify', [status(thm)], ['11'])).
% 0.54/0.74  thf('13', plain,
% 0.54/0.74      ((~ (v1_funct_1 @ sk_B_1)
% 0.54/0.74        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.54/0.74        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.54/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('14', plain,
% 0.54/0.74      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.54/0.74         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('split', [status(esa)], ['13'])).
% 0.54/0.74  thf('15', plain, ((v1_funct_1 @ sk_B_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('16', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.54/0.74      inference('split', [status(esa)], ['13'])).
% 0.54/0.74  thf('17', plain, (((v1_funct_1 @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.74  thf('18', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.74  thf('19', plain,
% 0.54/0.74      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.54/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.54/0.74         <= (~
% 0.54/0.74             ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.74               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.54/0.74      inference('split', [status(esa)], ['13'])).
% 0.54/0.74  thf('20', plain,
% 0.54/0.74      (((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.74  thf('21', plain,
% 0.54/0.74      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.54/0.74       ~
% 0.54/0.74       ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.54/0.74       ~ ((v1_funct_1 @ sk_B_1))),
% 0.54/0.74      inference('split', [status(esa)], ['13'])).
% 0.54/0.74  thf('22', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.54/0.74      inference('sat_resolution*', [status(thm)], ['17', '20', '21'])).
% 0.54/0.74  thf('23', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.54/0.74      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.54/0.74  thf('24', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.54/0.74      inference('clc', [status(thm)], ['12', '23'])).
% 0.54/0.74  thf('25', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_4, axiom,
% 0.54/0.74    (![B:$i,A:$i]:
% 0.54/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.54/0.74  thf(zf_stmt_5, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.54/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.54/0.74  thf('26', plain,
% 0.54/0.74      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.54/0.74         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.54/0.74          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.54/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.74  thf('27', plain,
% 0.54/0.74      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.54/0.74        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['25', '26'])).
% 0.54/0.74  thf(fc10_relat_1, axiom,
% 0.54/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.54/0.74  thf('28', plain,
% 0.54/0.74      (![X24 : $i]:
% 0.54/0.74         ((v1_xboole_0 @ (k1_relat_1 @ X24)) | ~ (v1_xboole_0 @ X24))),
% 0.54/0.74      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.54/0.74  thf(l13_xboole_0, axiom,
% 0.54/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.74  thf('29', plain,
% 0.54/0.74      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('30', plain,
% 0.54/0.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.74  thf('31', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.54/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.74  thf(t3_subset, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.74  thf('32', plain,
% 0.54/0.74      (![X17 : $i, X19 : $i]:
% 0.54/0.74         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.54/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.74  thf('33', plain,
% 0.54/0.74      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.74  thf('34', plain,
% 0.54/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.74         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.54/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.74  thf('35', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('36', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.54/0.74          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['30', '35'])).
% 0.54/0.74  thf(t66_xboole_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.54/0.74       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.54/0.74  thf('37', plain,
% 0.54/0.74      (![X11 : $i]: ((r1_xboole_0 @ X11 @ X11) | ((X11) != (k1_xboole_0)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.54/0.74  thf('38', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('simplify', [status(thm)], ['37'])).
% 0.54/0.74  thf(t69_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.74       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.54/0.74  thf('39', plain,
% 0.54/0.74      (![X13 : $i, X14 : $i]:
% 0.54/0.74         (~ (r1_xboole_0 @ X13 @ X14)
% 0.54/0.74          | ~ (r1_tarski @ X13 @ X14)
% 0.54/0.74          | (v1_xboole_0 @ X13))),
% 0.54/0.74      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.54/0.74  thf('40', plain,
% 0.54/0.74      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.54/0.74  thf('41', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.54/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.74  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('demod', [status(thm)], ['40', '41'])).
% 0.54/0.74  thf('43', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('demod', [status(thm)], ['36', '42'])).
% 0.54/0.74  thf('44', plain,
% 0.54/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.74         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 0.54/0.74          | (v1_funct_2 @ X36 @ X34 @ X35)
% 0.54/0.74          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.74  thf('45', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((X1) != (k1_xboole_0))
% 0.54/0.74          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.54/0.74          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['43', '44'])).
% 0.54/0.74  thf('46', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.74          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['45'])).
% 0.54/0.74  thf('47', plain,
% 0.54/0.74      (![X32 : $i, X33 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.54/0.74  thf('48', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 0.54/0.74      inference('simplify', [status(thm)], ['47'])).
% 0.54/0.74  thf('49', plain,
% 0.54/0.74      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.74  thf('50', plain,
% 0.54/0.74      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.54/0.74         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.54/0.74          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.54/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.74  thf('51', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.54/0.74  thf('52', plain,
% 0.54/0.74      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.54/0.74      inference('sup-', [status(thm)], ['48', '51'])).
% 0.54/0.74  thf('53', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.54/0.74      inference('demod', [status(thm)], ['46', '52'])).
% 0.54/0.74  thf('54', plain,
% 0.54/0.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.74  thf('55', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('56', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('demod', [status(thm)], ['36', '42'])).
% 0.54/0.74  thf('57', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.74      inference('demod', [status(thm)], ['55', '56'])).
% 0.54/0.74  thf('58', plain,
% 0.54/0.74      (![X32 : $i, X33 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.54/0.74  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('demod', [status(thm)], ['40', '41'])).
% 0.54/0.74  thf('60', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.54/0.74      inference('sup+', [status(thm)], ['58', '59'])).
% 0.54/0.74  thf('61', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('62', plain,
% 0.54/0.74      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('63', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.54/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.74  thf('64', plain,
% 0.54/0.74      (![X6 : $i, X8 : $i]:
% 0.54/0.74         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.54/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.74  thf('65', plain,
% 0.54/0.74      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['63', '64'])).
% 0.54/0.74  thf('66', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X1 @ X0)
% 0.54/0.74          | ~ (v1_xboole_0 @ X0)
% 0.54/0.74          | ((X1) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['62', '65'])).
% 0.54/0.74  thf('67', plain,
% 0.54/0.74      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['61', '66'])).
% 0.54/0.74  thf('68', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ sk_A @ X0) | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['60', '67'])).
% 0.54/0.74  thf(fc9_relat_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.54/0.74       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.54/0.74  thf('69', plain,
% 0.54/0.74      (![X25 : $i]:
% 0.54/0.74         (~ (v1_xboole_0 @ (k2_relat_1 @ X25))
% 0.54/0.74          | ~ (v1_relat_1 @ X25)
% 0.54/0.74          | (v1_xboole_0 @ X25))),
% 0.54/0.74      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.54/0.74  thf('70', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.74          | (zip_tseitin_0 @ sk_A @ X0)
% 0.54/0.74          | (v1_xboole_0 @ sk_B_1)
% 0.54/0.74          | ~ (v1_relat_1 @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['68', '69'])).
% 0.54/0.74  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('demod', [status(thm)], ['40', '41'])).
% 0.54/0.74  thf('72', plain, ((v1_relat_1 @ sk_B_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('73', plain,
% 0.54/0.74      (![X0 : $i]: ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.54/0.74  thf('74', plain,
% 0.54/0.74      (![X24 : $i]:
% 0.54/0.74         ((v1_xboole_0 @ (k1_relat_1 @ X24)) | ~ (v1_xboole_0 @ X24))),
% 0.54/0.74      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.54/0.74  thf('75', plain,
% 0.54/0.74      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('76', plain,
% 0.54/0.74      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('77', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.74      inference('sup+', [status(thm)], ['75', '76'])).
% 0.54/0.74  thf('78', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (v1_xboole_0 @ X0)
% 0.54/0.74          | ~ (v1_xboole_0 @ X1)
% 0.54/0.74          | ((k1_relat_1 @ X0) = (X1)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['74', '77'])).
% 0.54/0.74  thf('79', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ sk_A @ X1)
% 0.54/0.74          | ((k1_relat_1 @ X0) = (sk_B_1))
% 0.54/0.74          | ~ (v1_xboole_0 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['73', '78'])).
% 0.54/0.74  thf('80', plain,
% 0.54/0.74      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.54/0.74         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('split', [status(esa)], ['13'])).
% 0.54/0.74  thf('81', plain,
% 0.54/0.74      ((![X0 : $i, X1 : $i]:
% 0.54/0.74          (~ (v1_funct_2 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.54/0.74           | ~ (v1_xboole_0 @ X0)
% 0.54/0.74           | (zip_tseitin_0 @ sk_A @ X1)))
% 0.54/0.74         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['79', '80'])).
% 0.54/0.74  thf('82', plain,
% 0.54/0.74      ((![X0 : $i]:
% 0.54/0.74          (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.54/0.74           | (zip_tseitin_0 @ sk_A @ X0)
% 0.54/0.74           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.54/0.74         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['57', '81'])).
% 0.54/0.74  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('demod', [status(thm)], ['40', '41'])).
% 0.54/0.74  thf('84', plain,
% 0.54/0.74      ((![X0 : $i]:
% 0.54/0.74          (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.54/0.74           | (zip_tseitin_0 @ sk_A @ X0)))
% 0.54/0.74         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['82', '83'])).
% 0.54/0.74  thf('85', plain,
% 0.54/0.74      ((![X0 : $i]:
% 0.54/0.74          (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)
% 0.54/0.74           | ~ (v1_xboole_0 @ sk_B_1)
% 0.54/0.74           | (zip_tseitin_0 @ sk_A @ X0)))
% 0.54/0.74         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['54', '84'])).
% 0.54/0.74  thf('86', plain,
% 0.54/0.74      (![X0 : $i]: ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.54/0.74  thf('87', plain,
% 0.54/0.74      ((![X0 : $i]:
% 0.54/0.74          ((zip_tseitin_0 @ sk_A @ X0)
% 0.54/0.74           | ~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)))
% 0.54/0.74         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('clc', [status(thm)], ['85', '86'])).
% 0.54/0.74  thf('88', plain,
% 0.54/0.74      ((![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0))
% 0.54/0.74         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['53', '87'])).
% 0.54/0.74  thf('89', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.54/0.74      inference('sat_resolution*', [status(thm)], ['17', '20', '21'])).
% 0.54/0.74  thf('90', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.54/0.74      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 0.54/0.74  thf('91', plain, ((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['27', '90'])).
% 0.54/0.74  thf('92', plain, ($false), inference('demod', [status(thm)], ['24', '91'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
