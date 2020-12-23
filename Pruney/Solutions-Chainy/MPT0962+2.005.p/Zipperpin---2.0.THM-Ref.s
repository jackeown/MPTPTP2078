%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xpgkp2YdWp

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:49 EST 2020

% Result     : Theorem 4.56s
% Output     : Refutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 287 expanded)
%              Number of leaves         :   41 ( 100 expanded)
%              Depth                    :   22
%              Number of atoms          :  969 (2281 expanded)
%              Number of equality atoms :   71 ( 130 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('25',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X21: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('48',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('60',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('72',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('77',plain,(
    ! [X22: $i] :
      ( ( r1_tarski @ X22 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('80',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['78','80','81'])).

thf('83',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = sk_B_1 )
      | ( zip_tseitin_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','88'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('90',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ sk_B_1 )
        = X0 )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ( ( k1_relat_1 @ sk_B_1 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','91'])).

thf('93',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('94',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('97',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ( zip_tseitin_0 @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(eq_fact,[status(thm)],['102'])).

thf('104',plain,(
    zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['23','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['17','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xpgkp2YdWp
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:26:49 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 4.56/4.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.56/4.74  % Solved by: fo/fo7.sh
% 4.56/4.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.56/4.74  % done 4773 iterations in 4.281s
% 4.56/4.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.56/4.74  % SZS output start Refutation
% 4.56/4.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.56/4.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.56/4.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.56/4.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.56/4.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.56/4.74  thf(sk_A_type, type, sk_A: $i).
% 4.56/4.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.56/4.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.56/4.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.56/4.74  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.56/4.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.56/4.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.56/4.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.56/4.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.56/4.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.56/4.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.56/4.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.56/4.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.56/4.74  thf(t4_funct_2, conjecture,
% 4.56/4.74    (![A:$i,B:$i]:
% 4.56/4.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.56/4.74       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 4.56/4.74         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 4.56/4.74           ( m1_subset_1 @
% 4.56/4.74             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 4.56/4.74  thf(zf_stmt_0, negated_conjecture,
% 4.56/4.74    (~( ![A:$i,B:$i]:
% 4.56/4.74        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.56/4.74          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 4.56/4.74            ( ( v1_funct_1 @ B ) & 
% 4.56/4.74              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 4.56/4.74              ( m1_subset_1 @
% 4.56/4.74                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 4.56/4.74    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 4.56/4.74  thf('0', plain,
% 4.56/4.74      ((~ (v1_funct_1 @ sk_B_1)
% 4.56/4.74        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 4.56/4.74        | ~ (m1_subset_1 @ sk_B_1 @ 
% 4.56/4.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.74  thf('1', plain,
% 4.56/4.74      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 4.56/4.74         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.56/4.74      inference('split', [status(esa)], ['0'])).
% 4.56/4.74  thf('2', plain, ((v1_funct_1 @ sk_B_1)),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.74  thf('3', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 4.56/4.74      inference('split', [status(esa)], ['0'])).
% 4.56/4.74  thf('4', plain, (((v1_funct_1 @ sk_B_1))),
% 4.56/4.74      inference('sup-', [status(thm)], ['2', '3'])).
% 4.56/4.74  thf('5', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.74  thf(d10_xboole_0, axiom,
% 4.56/4.74    (![A:$i,B:$i]:
% 4.56/4.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.56/4.74  thf('6', plain,
% 4.56/4.74      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 4.56/4.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.56/4.74  thf('7', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 4.56/4.74      inference('simplify', [status(thm)], ['6'])).
% 4.56/4.74  thf(t11_relset_1, axiom,
% 4.56/4.74    (![A:$i,B:$i,C:$i]:
% 4.56/4.74     ( ( v1_relat_1 @ C ) =>
% 4.56/4.74       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 4.56/4.74           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 4.56/4.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 4.56/4.74  thf('8', plain,
% 4.56/4.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.56/4.74         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 4.56/4.74          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 4.56/4.74          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 4.56/4.74          | ~ (v1_relat_1 @ X29))),
% 4.56/4.74      inference('cnf', [status(esa)], [t11_relset_1])).
% 4.56/4.74  thf('9', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         (~ (v1_relat_1 @ X0)
% 4.56/4.74          | (m1_subset_1 @ X0 @ 
% 4.56/4.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 4.56/4.74          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 4.56/4.74      inference('sup-', [status(thm)], ['7', '8'])).
% 4.56/4.74  thf('10', plain,
% 4.56/4.74      (((m1_subset_1 @ sk_B_1 @ 
% 4.56/4.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 4.56/4.74        | ~ (v1_relat_1 @ sk_B_1))),
% 4.56/4.74      inference('sup-', [status(thm)], ['5', '9'])).
% 4.56/4.74  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.74  thf('12', plain,
% 4.56/4.74      ((m1_subset_1 @ sk_B_1 @ 
% 4.56/4.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.56/4.74      inference('demod', [status(thm)], ['10', '11'])).
% 4.56/4.74  thf('13', plain,
% 4.56/4.74      ((~ (m1_subset_1 @ sk_B_1 @ 
% 4.56/4.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 4.56/4.74         <= (~
% 4.56/4.74             ((m1_subset_1 @ sk_B_1 @ 
% 4.56/4.74               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 4.56/4.74      inference('split', [status(esa)], ['0'])).
% 4.56/4.74  thf('14', plain,
% 4.56/4.74      (((m1_subset_1 @ sk_B_1 @ 
% 4.56/4.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 4.56/4.74      inference('sup-', [status(thm)], ['12', '13'])).
% 4.56/4.74  thf('15', plain,
% 4.56/4.74      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 4.56/4.74       ~
% 4.56/4.74       ((m1_subset_1 @ sk_B_1 @ 
% 4.56/4.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 4.56/4.74       ~ ((v1_funct_1 @ sk_B_1))),
% 4.56/4.74      inference('split', [status(esa)], ['0'])).
% 4.56/4.74  thf('16', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 4.56/4.74      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 4.56/4.74  thf('17', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 4.56/4.74      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 4.56/4.74  thf('18', plain,
% 4.56/4.74      ((m1_subset_1 @ sk_B_1 @ 
% 4.56/4.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.56/4.74      inference('demod', [status(thm)], ['10', '11'])).
% 4.56/4.74  thf(redefinition_k1_relset_1, axiom,
% 4.56/4.74    (![A:$i,B:$i,C:$i]:
% 4.56/4.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.56/4.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.56/4.74  thf('19', plain,
% 4.56/4.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.56/4.74         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 4.56/4.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.56/4.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.56/4.74  thf('20', plain,
% 4.56/4.74      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 4.56/4.74         = (k1_relat_1 @ sk_B_1))),
% 4.56/4.74      inference('sup-', [status(thm)], ['18', '19'])).
% 4.56/4.74  thf(d1_funct_2, axiom,
% 4.56/4.74    (![A:$i,B:$i,C:$i]:
% 4.56/4.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.56/4.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.56/4.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.56/4.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.56/4.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.56/4.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.56/4.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.56/4.74  thf(zf_stmt_1, axiom,
% 4.56/4.74    (![C:$i,B:$i,A:$i]:
% 4.56/4.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.56/4.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.56/4.74  thf('21', plain,
% 4.56/4.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.56/4.74         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 4.56/4.74          | (v1_funct_2 @ X37 @ X35 @ X36)
% 4.56/4.74          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.56/4.74  thf('22', plain,
% 4.56/4.74      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 4.56/4.74        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 4.56/4.74        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 4.56/4.74      inference('sup-', [status(thm)], ['20', '21'])).
% 4.56/4.74  thf('23', plain,
% 4.56/4.74      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 4.56/4.74        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 4.56/4.74      inference('simplify', [status(thm)], ['22'])).
% 4.56/4.74  thf('24', plain,
% 4.56/4.74      ((m1_subset_1 @ sk_B_1 @ 
% 4.56/4.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.56/4.74      inference('demod', [status(thm)], ['10', '11'])).
% 4.56/4.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.56/4.74  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 4.56/4.74  thf(zf_stmt_4, axiom,
% 4.56/4.74    (![B:$i,A:$i]:
% 4.56/4.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.56/4.74       ( zip_tseitin_0 @ B @ A ) ))).
% 4.56/4.74  thf(zf_stmt_5, axiom,
% 4.56/4.74    (![A:$i,B:$i,C:$i]:
% 4.56/4.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.56/4.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.56/4.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.56/4.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.56/4.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.56/4.74  thf('25', plain,
% 4.56/4.74      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.56/4.74         (~ (zip_tseitin_0 @ X38 @ X39)
% 4.56/4.74          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 4.56/4.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.56/4.74  thf('26', plain,
% 4.56/4.74      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 4.56/4.74        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['24', '25'])).
% 4.56/4.74  thf(l13_xboole_0, axiom,
% 4.56/4.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.56/4.74  thf('27', plain,
% 4.56/4.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.56/4.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.56/4.74  thf(t1_boole, axiom,
% 4.56/4.74    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.56/4.74  thf('28', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 4.56/4.74      inference('cnf', [status(esa)], [t1_boole])).
% 4.56/4.74  thf('29', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 4.56/4.74      inference('simplify', [status(thm)], ['6'])).
% 4.56/4.74  thf(t10_xboole_1, axiom,
% 4.56/4.74    (![A:$i,B:$i,C:$i]:
% 4.56/4.74     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 4.56/4.74  thf('30', plain,
% 4.56/4.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 4.56/4.74         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 4.56/4.74      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.56/4.74  thf('31', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.56/4.74      inference('sup-', [status(thm)], ['29', '30'])).
% 4.56/4.74  thf('32', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.56/4.74      inference('sup+', [status(thm)], ['28', '31'])).
% 4.56/4.74  thf(t3_subset, axiom,
% 4.56/4.74    (![A:$i,B:$i]:
% 4.56/4.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.56/4.74  thf('33', plain,
% 4.56/4.74      (![X14 : $i, X16 : $i]:
% 4.56/4.74         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 4.56/4.74      inference('cnf', [status(esa)], [t3_subset])).
% 4.56/4.74  thf('34', plain,
% 4.56/4.74      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.56/4.74      inference('sup-', [status(thm)], ['32', '33'])).
% 4.56/4.74  thf('35', plain,
% 4.56/4.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.56/4.74         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 4.56/4.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.56/4.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.56/4.74  thf('36', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.56/4.74      inference('sup-', [status(thm)], ['34', '35'])).
% 4.56/4.74  thf(fc10_relat_1, axiom,
% 4.56/4.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 4.56/4.74  thf('37', plain,
% 4.56/4.74      (![X21 : $i]:
% 4.56/4.74         ((v1_xboole_0 @ (k1_relat_1 @ X21)) | ~ (v1_xboole_0 @ X21))),
% 4.56/4.74      inference('cnf', [status(esa)], [fc10_relat_1])).
% 4.56/4.74  thf('38', plain,
% 4.56/4.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.56/4.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.56/4.74  thf('39', plain,
% 4.56/4.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['37', '38'])).
% 4.56/4.74  thf('40', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.56/4.74      inference('sup-', [status(thm)], ['34', '35'])).
% 4.56/4.74  thf('41', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 4.56/4.74          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.56/4.74      inference('sup+', [status(thm)], ['39', '40'])).
% 4.56/4.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.56/4.74  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.56/4.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.56/4.74  thf('43', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.56/4.74      inference('demod', [status(thm)], ['41', '42'])).
% 4.56/4.74  thf('44', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.56/4.74      inference('demod', [status(thm)], ['36', '43'])).
% 4.56/4.74  thf(t65_relat_1, axiom,
% 4.56/4.74    (![A:$i]:
% 4.56/4.74     ( ( v1_relat_1 @ A ) =>
% 4.56/4.74       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 4.56/4.74         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 4.56/4.74  thf('45', plain,
% 4.56/4.74      (![X23 : $i]:
% 4.56/4.74         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 4.56/4.74          | ((k2_relat_1 @ X23) = (k1_xboole_0))
% 4.56/4.74          | ~ (v1_relat_1 @ X23))),
% 4.56/4.74      inference('cnf', [status(esa)], [t65_relat_1])).
% 4.56/4.74  thf('46', plain,
% 4.56/4.74      ((((k1_xboole_0) != (k1_xboole_0))
% 4.56/4.74        | ~ (v1_relat_1 @ k1_xboole_0)
% 4.56/4.74        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['44', '45'])).
% 4.56/4.74  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.56/4.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.56/4.74  thf(cc1_relat_1, axiom,
% 4.56/4.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 4.56/4.74  thf('48', plain, (![X20 : $i]: ((v1_relat_1 @ X20) | ~ (v1_xboole_0 @ X20))),
% 4.56/4.74      inference('cnf', [status(esa)], [cc1_relat_1])).
% 4.56/4.74  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.56/4.74      inference('sup-', [status(thm)], ['47', '48'])).
% 4.56/4.74  thf('50', plain,
% 4.56/4.74      ((((k1_xboole_0) != (k1_xboole_0))
% 4.56/4.74        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.56/4.74      inference('demod', [status(thm)], ['46', '49'])).
% 4.56/4.74  thf('51', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.56/4.74      inference('simplify', [status(thm)], ['50'])).
% 4.56/4.74  thf('52', plain,
% 4.56/4.74      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.56/4.74      inference('sup+', [status(thm)], ['27', '51'])).
% 4.56/4.74  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.56/4.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.56/4.74  thf('54', plain,
% 4.56/4.74      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 4.56/4.74      inference('sup+', [status(thm)], ['52', '53'])).
% 4.56/4.74  thf(fc3_zfmisc_1, axiom,
% 4.56/4.74    (![A:$i,B:$i]:
% 4.56/4.74     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.56/4.74  thf('55', plain,
% 4.56/4.74      (![X9 : $i, X10 : $i]:
% 4.56/4.74         ((v1_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10)) | ~ (v1_xboole_0 @ X10))),
% 4.56/4.74      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 4.56/4.74  thf('56', plain,
% 4.56/4.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.56/4.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.56/4.74  thf('57', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 4.56/4.74      inference('cnf', [status(esa)], [t1_boole])).
% 4.56/4.74  thf('58', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         (((k2_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 4.56/4.74      inference('sup+', [status(thm)], ['56', '57'])).
% 4.56/4.74  thf('59', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.74         (~ (v1_xboole_0 @ X0)
% 4.56/4.74          | ((k2_xboole_0 @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) = (X2)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['55', '58'])).
% 4.56/4.74  thf(t29_relset_1, axiom,
% 4.56/4.74    (![A:$i]:
% 4.56/4.74     ( m1_subset_1 @
% 4.56/4.74       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.56/4.74  thf('60', plain,
% 4.56/4.74      (![X32 : $i]:
% 4.56/4.74         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 4.56/4.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 4.56/4.74      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.56/4.74  thf('61', plain,
% 4.56/4.74      (![X14 : $i, X15 : $i]:
% 4.56/4.74         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 4.56/4.74      inference('cnf', [status(esa)], [t3_subset])).
% 4.56/4.74  thf('62', plain,
% 4.56/4.74      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 4.56/4.74      inference('sup-', [status(thm)], ['60', '61'])).
% 4.56/4.74  thf('63', plain,
% 4.56/4.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 4.56/4.74         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 4.56/4.74      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.56/4.74  thf('64', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         (r1_tarski @ (k6_relat_1 @ X0) @ 
% 4.56/4.74          (k2_xboole_0 @ X1 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['62', '63'])).
% 4.56/4.74  thf('65', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         ((r1_tarski @ (k6_relat_1 @ X1) @ X0) | ~ (v1_xboole_0 @ X1))),
% 4.56/4.74      inference('sup+', [status(thm)], ['59', '64'])).
% 4.56/4.74  thf('66', plain,
% 4.56/4.74      (![X33 : $i, X34 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.56/4.74  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.56/4.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.56/4.74  thf('68', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.56/4.74      inference('sup+', [status(thm)], ['66', '67'])).
% 4.56/4.74  thf('69', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.74  thf('70', plain,
% 4.56/4.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.56/4.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.56/4.74  thf('71', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.56/4.74      inference('sup+', [status(thm)], ['28', '31'])).
% 4.56/4.74  thf('72', plain,
% 4.56/4.74      (![X2 : $i, X4 : $i]:
% 4.56/4.74         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 4.56/4.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.56/4.74  thf('73', plain,
% 4.56/4.74      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['71', '72'])).
% 4.56/4.74  thf('74', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         (~ (r1_tarski @ X1 @ X0)
% 4.56/4.74          | ~ (v1_xboole_0 @ X0)
% 4.56/4.74          | ((X1) = (k1_xboole_0)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['70', '73'])).
% 4.56/4.74  thf('75', plain,
% 4.56/4.74      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_A))),
% 4.56/4.74      inference('sup-', [status(thm)], ['69', '74'])).
% 4.56/4.74  thf('76', plain,
% 4.56/4.74      (![X0 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ sk_A @ X0) | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['68', '75'])).
% 4.56/4.74  thf(t21_relat_1, axiom,
% 4.56/4.74    (![A:$i]:
% 4.56/4.74     ( ( v1_relat_1 @ A ) =>
% 4.56/4.74       ( r1_tarski @
% 4.56/4.74         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 4.56/4.74  thf('77', plain,
% 4.56/4.74      (![X22 : $i]:
% 4.56/4.74         ((r1_tarski @ X22 @ 
% 4.56/4.74           (k2_zfmisc_1 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 4.56/4.74          | ~ (v1_relat_1 @ X22))),
% 4.56/4.74      inference('cnf', [status(esa)], [t21_relat_1])).
% 4.56/4.74  thf('78', plain,
% 4.56/4.74      (![X0 : $i]:
% 4.56/4.74         ((r1_tarski @ sk_B_1 @ 
% 4.56/4.74           (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0))
% 4.56/4.74          | (zip_tseitin_0 @ sk_A @ X0)
% 4.56/4.74          | ~ (v1_relat_1 @ sk_B_1))),
% 4.56/4.74      inference('sup+', [status(thm)], ['76', '77'])).
% 4.56/4.74  thf(t113_zfmisc_1, axiom,
% 4.56/4.74    (![A:$i,B:$i]:
% 4.56/4.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.56/4.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.56/4.74  thf('79', plain,
% 4.56/4.74      (![X12 : $i, X13 : $i]:
% 4.56/4.74         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 4.56/4.74          | ((X13) != (k1_xboole_0)))),
% 4.56/4.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.56/4.74  thf('80', plain,
% 4.56/4.74      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 4.56/4.74      inference('simplify', [status(thm)], ['79'])).
% 4.56/4.74  thf('81', plain, ((v1_relat_1 @ sk_B_1)),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.74  thf('82', plain,
% 4.56/4.74      (![X0 : $i]:
% 4.56/4.74         ((r1_tarski @ sk_B_1 @ k1_xboole_0) | (zip_tseitin_0 @ sk_A @ X0))),
% 4.56/4.74      inference('demod', [status(thm)], ['78', '80', '81'])).
% 4.56/4.74  thf('83', plain,
% 4.56/4.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 4.56/4.74         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 4.56/4.74      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.56/4.74  thf('84', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ sk_A @ X1)
% 4.56/4.74          | (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['82', '83'])).
% 4.56/4.74  thf('85', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 4.56/4.74      inference('cnf', [status(esa)], [t1_boole])).
% 4.56/4.74  thf('86', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ sk_A @ X1) | (r1_tarski @ sk_B_1 @ X0))),
% 4.56/4.74      inference('demod', [status(thm)], ['84', '85'])).
% 4.56/4.74  thf('87', plain,
% 4.56/4.74      (![X2 : $i, X4 : $i]:
% 4.56/4.74         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 4.56/4.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.56/4.74  thf('88', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ sk_A @ X1)
% 4.56/4.74          | ~ (r1_tarski @ X0 @ sk_B_1)
% 4.56/4.74          | ((X0) = (sk_B_1)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['86', '87'])).
% 4.56/4.74  thf('89', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         (~ (v1_xboole_0 @ X0)
% 4.56/4.74          | ((k6_relat_1 @ X0) = (sk_B_1))
% 4.56/4.74          | (zip_tseitin_0 @ sk_A @ X1))),
% 4.56/4.74      inference('sup-', [status(thm)], ['65', '88'])).
% 4.56/4.74  thf(t71_relat_1, axiom,
% 4.56/4.74    (![A:$i]:
% 4.56/4.74     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.56/4.74       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.56/4.74  thf('90', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 4.56/4.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.56/4.74  thf('91', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         (((k1_relat_1 @ sk_B_1) = (X0))
% 4.56/4.74          | (zip_tseitin_0 @ sk_A @ X1)
% 4.56/4.74          | ~ (v1_xboole_0 @ X0))),
% 4.56/4.74      inference('sup+', [status(thm)], ['89', '90'])).
% 4.56/4.74  thf('92', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         (~ (v1_xboole_0 @ X0)
% 4.56/4.74          | (zip_tseitin_0 @ sk_A @ X1)
% 4.56/4.74          | ((k1_relat_1 @ sk_B_1) = (k2_relat_1 @ X0)))),
% 4.56/4.74      inference('sup-', [status(thm)], ['54', '91'])).
% 4.56/4.74  thf('93', plain,
% 4.56/4.74      (![X33 : $i, X34 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.56/4.74  thf('94', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.56/4.74      inference('simplify', [status(thm)], ['50'])).
% 4.56/4.74  thf('95', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         (((k2_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 4.56/4.74      inference('sup+', [status(thm)], ['93', '94'])).
% 4.56/4.74  thf('96', plain,
% 4.56/4.74      (![X33 : $i, X34 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 4.56/4.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.56/4.74  thf('97', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 4.56/4.74      inference('simplify', [status(thm)], ['96'])).
% 4.56/4.74  thf('98', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ X1 @ (k2_relat_1 @ X0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.56/4.74      inference('sup+', [status(thm)], ['95', '97'])).
% 4.56/4.74  thf('99', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ (k2_relat_1 @ X0))),
% 4.56/4.74      inference('eq_fact', [status(thm)], ['98'])).
% 4.56/4.74  thf('100', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ X0 @ (k1_relat_1 @ sk_B_1))
% 4.56/4.74          | (zip_tseitin_0 @ sk_A @ X1)
% 4.56/4.74          | ~ (v1_xboole_0 @ X0))),
% 4.56/4.74      inference('sup+', [status(thm)], ['92', '99'])).
% 4.56/4.74  thf('101', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.56/4.74      inference('sup+', [status(thm)], ['66', '67'])).
% 4.56/4.74  thf('102', plain,
% 4.56/4.74      (![X0 : $i, X1 : $i]:
% 4.56/4.74         ((zip_tseitin_0 @ sk_A @ X1)
% 4.56/4.74          | (zip_tseitin_0 @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 4.56/4.74      inference('clc', [status(thm)], ['100', '101'])).
% 4.56/4.74  thf('103', plain, ((zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 4.56/4.74      inference('eq_fact', [status(thm)], ['102'])).
% 4.56/4.74  thf('104', plain, ((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 4.56/4.74      inference('demod', [status(thm)], ['26', '103'])).
% 4.56/4.74  thf('105', plain, ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 4.56/4.74      inference('demod', [status(thm)], ['23', '104'])).
% 4.56/4.74  thf('106', plain, ($false), inference('demod', [status(thm)], ['17', '105'])).
% 4.56/4.74  
% 4.56/4.74  % SZS output end Refutation
% 4.56/4.74  
% 4.56/4.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
