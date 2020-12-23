%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SDO8SDPZer

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:50 EST 2020

% Result     : Theorem 6.04s
% Output     : Refutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 619 expanded)
%              Number of leaves         :   39 ( 197 expanded)
%              Depth                    :   24
%              Number of atoms          : 1138 (5712 expanded)
%              Number of equality atoms :   84 ( 271 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X32 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
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

thf('8',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('25',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','23','24'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','25'])).

thf('27',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['15','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) @ X20 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['45','46'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) @ X23 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['33','49'])).

thf('51',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('52',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('56',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X26: $i] :
      ( ( ( k2_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k1_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['45','46'])).

thf('65',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) @ X23 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ( X40 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,(
    ! [X39: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('80',plain,(
    ! [X39: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( X1
        = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('85',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) @ X23 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('94',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['45','46'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('96',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['89','100'])).

thf('102',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('103',plain,(
    r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('105',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X26: $i] :
      ( ( ( k2_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('107',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','98'])).

thf('109',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','113'])).

thf('115',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(condensation,[status(thm)],['114'])).

thf('116',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('117',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('120',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('121',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['119','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['32','118','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SDO8SDPZer
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.04/6.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.04/6.23  % Solved by: fo/fo7.sh
% 6.04/6.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.04/6.23  % done 5530 iterations in 5.778s
% 6.04/6.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.04/6.23  % SZS output start Refutation
% 6.04/6.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.04/6.23  thf(sk_A_type, type, sk_A: $i).
% 6.04/6.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.04/6.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.04/6.23  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.04/6.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.04/6.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.04/6.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.04/6.23  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.04/6.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.04/6.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.04/6.23  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.04/6.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.04/6.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.04/6.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.04/6.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.04/6.23  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.04/6.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.04/6.23  thf(t4_funct_2, conjecture,
% 6.04/6.23    (![A:$i,B:$i]:
% 6.04/6.23     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.04/6.23       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 6.04/6.23         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 6.04/6.23           ( m1_subset_1 @
% 6.04/6.23             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 6.04/6.23  thf(zf_stmt_0, negated_conjecture,
% 6.04/6.23    (~( ![A:$i,B:$i]:
% 6.04/6.23        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.04/6.23          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 6.04/6.23            ( ( v1_funct_1 @ B ) & 
% 6.04/6.23              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 6.04/6.23              ( m1_subset_1 @
% 6.04/6.23                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 6.04/6.23    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 6.04/6.23  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.04/6.23  thf(d10_xboole_0, axiom,
% 6.04/6.23    (![A:$i,B:$i]:
% 6.04/6.23     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.04/6.23  thf('1', plain,
% 6.04/6.23      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 6.04/6.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.04/6.23  thf('2', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 6.04/6.23      inference('simplify', [status(thm)], ['1'])).
% 6.04/6.23  thf(t11_relset_1, axiom,
% 6.04/6.23    (![A:$i,B:$i,C:$i]:
% 6.04/6.23     ( ( v1_relat_1 @ C ) =>
% 6.04/6.23       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 6.04/6.23           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 6.04/6.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 6.04/6.23  thf('3', plain,
% 6.04/6.23      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.04/6.23         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 6.04/6.23          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ X32)
% 6.04/6.23          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 6.04/6.23          | ~ (v1_relat_1 @ X30))),
% 6.04/6.23      inference('cnf', [status(esa)], [t11_relset_1])).
% 6.04/6.23  thf('4', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         (~ (v1_relat_1 @ X0)
% 6.04/6.23          | (m1_subset_1 @ X0 @ 
% 6.04/6.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 6.04/6.23          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 6.04/6.23      inference('sup-', [status(thm)], ['2', '3'])).
% 6.04/6.23  thf('5', plain,
% 6.04/6.23      (((m1_subset_1 @ sk_B_1 @ 
% 6.04/6.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 6.04/6.23        | ~ (v1_relat_1 @ sk_B_1))),
% 6.04/6.23      inference('sup-', [status(thm)], ['0', '4'])).
% 6.04/6.23  thf('6', plain, ((v1_relat_1 @ sk_B_1)),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.04/6.23  thf('7', plain,
% 6.04/6.23      ((m1_subset_1 @ sk_B_1 @ 
% 6.04/6.23        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 6.04/6.23      inference('demod', [status(thm)], ['5', '6'])).
% 6.04/6.23  thf(d1_funct_2, axiom,
% 6.04/6.23    (![A:$i,B:$i,C:$i]:
% 6.04/6.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.04/6.23       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.04/6.23           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.04/6.23             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.04/6.23         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.04/6.23           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.04/6.23             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.04/6.23  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.04/6.23  thf(zf_stmt_2, axiom,
% 6.04/6.23    (![C:$i,B:$i,A:$i]:
% 6.04/6.23     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.04/6.23       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.04/6.23  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 6.04/6.23  thf(zf_stmt_4, axiom,
% 6.04/6.23    (![B:$i,A:$i]:
% 6.04/6.23     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.04/6.23       ( zip_tseitin_0 @ B @ A ) ))).
% 6.04/6.23  thf(zf_stmt_5, axiom,
% 6.04/6.23    (![A:$i,B:$i,C:$i]:
% 6.04/6.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.04/6.23       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.04/6.23         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.04/6.23           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.04/6.23             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.04/6.23  thf('8', plain,
% 6.04/6.23      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.04/6.23         (~ (zip_tseitin_0 @ X38 @ X39)
% 6.04/6.23          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 6.04/6.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.04/6.23  thf('9', plain,
% 6.04/6.23      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 6.04/6.23        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 6.04/6.23      inference('sup-', [status(thm)], ['7', '8'])).
% 6.04/6.23  thf('10', plain,
% 6.04/6.23      ((m1_subset_1 @ sk_B_1 @ 
% 6.04/6.23        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 6.04/6.23      inference('demod', [status(thm)], ['5', '6'])).
% 6.04/6.23  thf(redefinition_k1_relset_1, axiom,
% 6.04/6.23    (![A:$i,B:$i,C:$i]:
% 6.04/6.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.04/6.23       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.04/6.23  thf('11', plain,
% 6.04/6.23      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.04/6.23         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 6.04/6.23          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 6.04/6.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.04/6.23  thf('12', plain,
% 6.04/6.23      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 6.04/6.23         = (k1_relat_1 @ sk_B_1))),
% 6.04/6.23      inference('sup-', [status(thm)], ['10', '11'])).
% 6.04/6.23  thf('13', plain,
% 6.04/6.23      (![X35 : $i, X36 : $i, X37 : $i]:
% 6.04/6.23         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 6.04/6.23          | (v1_funct_2 @ X37 @ X35 @ X36)
% 6.04/6.23          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.04/6.23  thf('14', plain,
% 6.04/6.23      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 6.04/6.23        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 6.04/6.23        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 6.04/6.23      inference('sup-', [status(thm)], ['12', '13'])).
% 6.04/6.23  thf('15', plain,
% 6.04/6.23      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 6.04/6.23        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 6.04/6.23      inference('simplify', [status(thm)], ['14'])).
% 6.04/6.23  thf('16', plain,
% 6.04/6.23      ((~ (v1_funct_1 @ sk_B_1)
% 6.04/6.23        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 6.04/6.23        | ~ (m1_subset_1 @ sk_B_1 @ 
% 6.04/6.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.04/6.23  thf('17', plain,
% 6.04/6.23      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 6.04/6.23         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 6.04/6.23      inference('split', [status(esa)], ['16'])).
% 6.04/6.23  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.04/6.23  thf('19', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 6.04/6.23      inference('split', [status(esa)], ['16'])).
% 6.04/6.23  thf('20', plain, (((v1_funct_1 @ sk_B_1))),
% 6.04/6.23      inference('sup-', [status(thm)], ['18', '19'])).
% 6.04/6.23  thf('21', plain,
% 6.04/6.23      ((m1_subset_1 @ sk_B_1 @ 
% 6.04/6.23        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 6.04/6.23      inference('demod', [status(thm)], ['5', '6'])).
% 6.04/6.23  thf('22', plain,
% 6.04/6.23      ((~ (m1_subset_1 @ sk_B_1 @ 
% 6.04/6.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 6.04/6.23         <= (~
% 6.04/6.23             ((m1_subset_1 @ sk_B_1 @ 
% 6.04/6.23               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 6.04/6.23      inference('split', [status(esa)], ['16'])).
% 6.04/6.23  thf('23', plain,
% 6.04/6.23      (((m1_subset_1 @ sk_B_1 @ 
% 6.04/6.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 6.04/6.23      inference('sup-', [status(thm)], ['21', '22'])).
% 6.04/6.23  thf('24', plain,
% 6.04/6.23      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 6.04/6.23       ~
% 6.04/6.23       ((m1_subset_1 @ sk_B_1 @ 
% 6.04/6.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 6.04/6.23       ~ ((v1_funct_1 @ sk_B_1))),
% 6.04/6.23      inference('split', [status(esa)], ['16'])).
% 6.04/6.23  thf('25', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 6.04/6.23      inference('sat_resolution*', [status(thm)], ['20', '23', '24'])).
% 6.04/6.23  thf('26', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 6.04/6.23      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 6.04/6.23  thf('27', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 6.04/6.23      inference('clc', [status(thm)], ['15', '26'])).
% 6.04/6.23  thf('28', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 6.04/6.23      inference('clc', [status(thm)], ['9', '27'])).
% 6.04/6.23  thf('29', plain,
% 6.04/6.23      (![X33 : $i, X34 : $i]:
% 6.04/6.23         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.04/6.23  thf('30', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 6.04/6.23      inference('clc', [status(thm)], ['9', '27'])).
% 6.04/6.23  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['29', '30'])).
% 6.04/6.23  thf('32', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B_1))),
% 6.04/6.23      inference('demod', [status(thm)], ['28', '31'])).
% 6.04/6.23  thf('33', plain,
% 6.04/6.23      (![X33 : $i, X34 : $i]:
% 6.04/6.23         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.04/6.23  thf(t193_relat_1, axiom,
% 6.04/6.23    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 6.04/6.23  thf('34', plain,
% 6.04/6.23      (![X20 : $i, X21 : $i]:
% 6.04/6.23         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21)) @ X20)),
% 6.04/6.23      inference('cnf', [status(esa)], [t193_relat_1])).
% 6.04/6.23  thf(d3_tarski, axiom,
% 6.04/6.23    (![A:$i,B:$i]:
% 6.04/6.23     ( ( r1_tarski @ A @ B ) <=>
% 6.04/6.23       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.04/6.23  thf('35', plain,
% 6.04/6.23      (![X4 : $i, X6 : $i]:
% 6.04/6.23         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 6.04/6.23      inference('cnf', [status(esa)], [d3_tarski])).
% 6.04/6.23  thf(d1_xboole_0, axiom,
% 6.04/6.23    (![A:$i]:
% 6.04/6.23     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.04/6.23  thf('36', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.04/6.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.04/6.23  thf('37', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['35', '36'])).
% 6.04/6.23  thf('38', plain,
% 6.04/6.23      (![X7 : $i, X9 : $i]:
% 6.04/6.23         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 6.04/6.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.04/6.23  thf('39', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 6.04/6.23      inference('sup-', [status(thm)], ['37', '38'])).
% 6.04/6.23  thf('40', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         (((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X0))
% 6.04/6.23          | ~ (v1_xboole_0 @ X0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['34', '39'])).
% 6.04/6.23  thf(t65_relat_1, axiom,
% 6.04/6.23    (![A:$i]:
% 6.04/6.23     ( ( v1_relat_1 @ A ) =>
% 6.04/6.23       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 6.04/6.23         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 6.04/6.23  thf('41', plain,
% 6.04/6.23      (![X26 : $i]:
% 6.04/6.23         (((k1_relat_1 @ X26) != (k1_xboole_0))
% 6.04/6.23          | ((k2_relat_1 @ X26) = (k1_xboole_0))
% 6.04/6.23          | ~ (v1_relat_1 @ X26))),
% 6.04/6.23      inference('cnf', [status(esa)], [t65_relat_1])).
% 6.04/6.23  thf('42', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         (((X0) != (k1_xboole_0))
% 6.04/6.23          | ~ (v1_xboole_0 @ X0)
% 6.04/6.23          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 6.04/6.23          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (k1_xboole_0)))),
% 6.04/6.23      inference('sup-', [status(thm)], ['40', '41'])).
% 6.04/6.23  thf(fc6_relat_1, axiom,
% 6.04/6.23    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.04/6.23  thf('43', plain,
% 6.04/6.23      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 6.04/6.23      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.04/6.23  thf('44', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         (((X0) != (k1_xboole_0))
% 6.04/6.23          | ~ (v1_xboole_0 @ X0)
% 6.04/6.23          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (k1_xboole_0)))),
% 6.04/6.23      inference('demod', [status(thm)], ['42', '43'])).
% 6.04/6.23  thf('45', plain,
% 6.04/6.23      (![X1 : $i]:
% 6.04/6.23         (((k2_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1)) = (k1_xboole_0))
% 6.04/6.23          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.04/6.23      inference('simplify', [status(thm)], ['44'])).
% 6.04/6.23  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.04/6.23  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.04/6.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.04/6.23  thf('47', plain,
% 6.04/6.23      (![X1 : $i]:
% 6.04/6.23         ((k2_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1)) = (k1_xboole_0))),
% 6.04/6.23      inference('simplify_reflect+', [status(thm)], ['45', '46'])).
% 6.04/6.23  thf(t194_relat_1, axiom,
% 6.04/6.23    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 6.04/6.23  thf('48', plain,
% 6.04/6.23      (![X22 : $i, X23 : $i]:
% 6.04/6.23         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X22 @ X23)) @ X23)),
% 6.04/6.23      inference('cnf', [status(esa)], [t194_relat_1])).
% 6.04/6.23  thf('49', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.04/6.23      inference('sup+', [status(thm)], ['47', '48'])).
% 6.04/6.23  thf('50', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.23         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 6.04/6.23      inference('sup+', [status(thm)], ['33', '49'])).
% 6.04/6.23  thf('51', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.04/6.23  thf(t1_xboole_1, axiom,
% 6.04/6.23    (![A:$i,B:$i,C:$i]:
% 6.04/6.23     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 6.04/6.23       ( r1_tarski @ A @ C ) ))).
% 6.04/6.23  thf('52', plain,
% 6.04/6.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.04/6.23         (~ (r1_tarski @ X10 @ X11)
% 6.04/6.23          | ~ (r1_tarski @ X11 @ X12)
% 6.04/6.23          | (r1_tarski @ X10 @ X12))),
% 6.04/6.23      inference('cnf', [status(esa)], [t1_xboole_1])).
% 6.04/6.23  thf('53', plain,
% 6.04/6.23      (![X0 : $i]:
% 6.04/6.23         ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['51', '52'])).
% 6.04/6.23  thf('54', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         ((zip_tseitin_0 @ sk_A @ X1)
% 6.04/6.23          | (r1_tarski @ (k2_relat_1 @ sk_B_1) @ X0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['50', '53'])).
% 6.04/6.23  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.04/6.23      inference('sup+', [status(thm)], ['47', '48'])).
% 6.04/6.23  thf('56', plain,
% 6.04/6.23      (![X7 : $i, X9 : $i]:
% 6.04/6.23         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 6.04/6.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.04/6.23  thf('57', plain,
% 6.04/6.23      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.04/6.23      inference('sup-', [status(thm)], ['55', '56'])).
% 6.04/6.23  thf('58', plain,
% 6.04/6.23      (![X0 : $i]:
% 6.04/6.23         ((zip_tseitin_0 @ sk_A @ X0) | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 6.04/6.23      inference('sup-', [status(thm)], ['54', '57'])).
% 6.04/6.23  thf('59', plain,
% 6.04/6.23      (![X26 : $i]:
% 6.04/6.23         (((k2_relat_1 @ X26) != (k1_xboole_0))
% 6.04/6.23          | ((k1_relat_1 @ X26) = (k1_xboole_0))
% 6.04/6.23          | ~ (v1_relat_1 @ X26))),
% 6.04/6.23      inference('cnf', [status(esa)], [t65_relat_1])).
% 6.04/6.23  thf('60', plain,
% 6.04/6.23      (![X0 : $i]:
% 6.04/6.23         (((k1_xboole_0) != (k1_xboole_0))
% 6.04/6.23          | (zip_tseitin_0 @ sk_A @ X0)
% 6.04/6.23          | ~ (v1_relat_1 @ sk_B_1)
% 6.04/6.23          | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 6.04/6.23      inference('sup-', [status(thm)], ['58', '59'])).
% 6.04/6.23  thf('61', plain, ((v1_relat_1 @ sk_B_1)),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.04/6.23  thf('62', plain,
% 6.04/6.23      (![X0 : $i]:
% 6.04/6.23         (((k1_xboole_0) != (k1_xboole_0))
% 6.04/6.23          | (zip_tseitin_0 @ sk_A @ X0)
% 6.04/6.23          | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 6.04/6.23      inference('demod', [status(thm)], ['60', '61'])).
% 6.04/6.23  thf('63', plain,
% 6.04/6.23      (![X0 : $i]:
% 6.04/6.23         (((k1_relat_1 @ sk_B_1) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_A @ X0))),
% 6.04/6.23      inference('simplify', [status(thm)], ['62'])).
% 6.04/6.23  thf('64', plain,
% 6.04/6.23      (![X1 : $i]:
% 6.04/6.23         ((k2_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1)) = (k1_xboole_0))),
% 6.04/6.23      inference('simplify_reflect+', [status(thm)], ['45', '46'])).
% 6.04/6.23  thf('65', plain,
% 6.04/6.23      (![X22 : $i, X23 : $i]:
% 6.04/6.23         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X22 @ X23)) @ X23)),
% 6.04/6.23      inference('cnf', [status(esa)], [t194_relat_1])).
% 6.04/6.23  thf(t3_subset, axiom,
% 6.04/6.23    (![A:$i,B:$i]:
% 6.04/6.23     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.04/6.23  thf('66', plain,
% 6.04/6.23      (![X13 : $i, X15 : $i]:
% 6.04/6.23         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 6.04/6.23      inference('cnf', [status(esa)], [t3_subset])).
% 6.04/6.23  thf('67', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         (m1_subset_1 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 6.04/6.23          (k1_zfmisc_1 @ X0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['65', '66'])).
% 6.04/6.23  thf('68', plain,
% 6.04/6.23      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.04/6.23      inference('sup+', [status(thm)], ['64', '67'])).
% 6.04/6.23  thf('69', plain,
% 6.04/6.23      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.04/6.23         (~ (zip_tseitin_0 @ X38 @ X39)
% 6.04/6.23          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 6.04/6.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.04/6.23  thf('70', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 6.04/6.23      inference('sup-', [status(thm)], ['68', '69'])).
% 6.04/6.23  thf('71', plain,
% 6.04/6.23      (![X0 : $i]:
% 6.04/6.23         (((k1_relat_1 @ sk_B_1) = (k1_xboole_0))
% 6.04/6.23          | (zip_tseitin_1 @ k1_xboole_0 @ sk_A @ X0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['63', '70'])).
% 6.04/6.23  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.04/6.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.04/6.23  thf('73', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['35', '36'])).
% 6.04/6.23  thf('74', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 6.04/6.23      inference('sup-', [status(thm)], ['37', '38'])).
% 6.04/6.23  thf('75', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['73', '74'])).
% 6.04/6.23  thf('76', plain,
% 6.04/6.23      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 6.04/6.23      inference('sup-', [status(thm)], ['72', '75'])).
% 6.04/6.23  thf('77', plain,
% 6.04/6.23      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.04/6.23         (((X38) != (k1_xboole_0))
% 6.04/6.23          | ((X39) = (k1_xboole_0))
% 6.04/6.23          | (v1_funct_2 @ X40 @ X39 @ X38)
% 6.04/6.23          | ((X40) != (k1_xboole_0))
% 6.04/6.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.04/6.23  thf('78', plain,
% 6.04/6.23      (![X39 : $i]:
% 6.04/6.23         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 6.04/6.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ k1_xboole_0)))
% 6.04/6.23          | (v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0)
% 6.04/6.23          | ((X39) = (k1_xboole_0)))),
% 6.04/6.23      inference('simplify', [status(thm)], ['77'])).
% 6.04/6.23  thf('79', plain,
% 6.04/6.23      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.04/6.23      inference('sup+', [status(thm)], ['64', '67'])).
% 6.04/6.23  thf('80', plain,
% 6.04/6.23      (![X39 : $i]:
% 6.04/6.23         ((v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0)
% 6.04/6.23          | ((X39) = (k1_xboole_0)))),
% 6.04/6.23      inference('demod', [status(thm)], ['78', '79'])).
% 6.04/6.23  thf('81', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 6.04/6.23          | ~ (v1_xboole_0 @ X0)
% 6.04/6.23          | ((X1) = (k1_xboole_0)))),
% 6.04/6.23      inference('sup+', [status(thm)], ['76', '80'])).
% 6.04/6.23  thf('82', plain,
% 6.04/6.23      (![X35 : $i, X36 : $i, X37 : $i]:
% 6.04/6.23         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 6.04/6.23          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 6.04/6.23          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 6.04/6.23      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.04/6.23  thf('83', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         (((X1) = (k1_xboole_0))
% 6.04/6.23          | ~ (v1_xboole_0 @ X0)
% 6.04/6.23          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 6.04/6.23          | ((X1) = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0)))),
% 6.04/6.23      inference('sup-', [status(thm)], ['81', '82'])).
% 6.04/6.23  thf('84', plain,
% 6.04/6.23      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.04/6.23      inference('sup+', [status(thm)], ['64', '67'])).
% 6.04/6.23  thf('85', plain,
% 6.04/6.23      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.04/6.23         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 6.04/6.23          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 6.04/6.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.04/6.23  thf('86', plain,
% 6.04/6.23      (![X0 : $i, X1 : $i]:
% 6.04/6.23         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 6.04/6.23      inference('sup-', [status(thm)], ['84', '85'])).
% 6.04/6.24  thf('87', plain,
% 6.04/6.24      (![X22 : $i, X23 : $i]:
% 6.04/6.24         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X22 @ X23)) @ X23)),
% 6.04/6.24      inference('cnf', [status(esa)], [t194_relat_1])).
% 6.04/6.24  thf('88', plain,
% 6.04/6.24      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.04/6.24      inference('sup-', [status(thm)], ['55', '56'])).
% 6.04/6.24  thf('89', plain,
% 6.04/6.24      (![X0 : $i]:
% 6.04/6.24         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 6.04/6.24      inference('sup-', [status(thm)], ['87', '88'])).
% 6.04/6.24  thf('90', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.04/6.24      inference('sup+', [status(thm)], ['47', '48'])).
% 6.04/6.24  thf(t25_relat_1, axiom,
% 6.04/6.24    (![A:$i]:
% 6.04/6.24     ( ( v1_relat_1 @ A ) =>
% 6.04/6.24       ( ![B:$i]:
% 6.04/6.24         ( ( v1_relat_1 @ B ) =>
% 6.04/6.24           ( ( r1_tarski @ A @ B ) =>
% 6.04/6.24             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 6.04/6.24               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 6.04/6.24  thf('91', plain,
% 6.04/6.24      (![X24 : $i, X25 : $i]:
% 6.04/6.24         (~ (v1_relat_1 @ X24)
% 6.04/6.24          | (r1_tarski @ (k2_relat_1 @ X25) @ (k2_relat_1 @ X24))
% 6.04/6.24          | ~ (r1_tarski @ X25 @ X24)
% 6.04/6.24          | ~ (v1_relat_1 @ X25))),
% 6.04/6.24      inference('cnf', [status(esa)], [t25_relat_1])).
% 6.04/6.24  thf('92', plain,
% 6.04/6.24      (![X0 : $i]:
% 6.04/6.24         (~ (v1_relat_1 @ k1_xboole_0)
% 6.04/6.24          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ (k2_relat_1 @ X0))
% 6.04/6.24          | ~ (v1_relat_1 @ X0))),
% 6.04/6.24      inference('sup-', [status(thm)], ['90', '91'])).
% 6.04/6.24  thf('93', plain,
% 6.04/6.24      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 6.04/6.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.04/6.24  thf('94', plain,
% 6.04/6.24      (![X1 : $i]:
% 6.04/6.24         ((k2_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1)) = (k1_xboole_0))),
% 6.04/6.24      inference('simplify_reflect+', [status(thm)], ['45', '46'])).
% 6.04/6.24  thf('95', plain,
% 6.04/6.24      (![X0 : $i, X1 : $i]:
% 6.04/6.24         (m1_subset_1 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 6.04/6.24          (k1_zfmisc_1 @ X0))),
% 6.04/6.24      inference('sup-', [status(thm)], ['65', '66'])).
% 6.04/6.24  thf(cc2_relat_1, axiom,
% 6.04/6.24    (![A:$i]:
% 6.04/6.24     ( ( v1_relat_1 @ A ) =>
% 6.04/6.24       ( ![B:$i]:
% 6.04/6.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.04/6.24  thf('96', plain,
% 6.04/6.24      (![X16 : $i, X17 : $i]:
% 6.04/6.24         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 6.04/6.24          | (v1_relat_1 @ X16)
% 6.04/6.24          | ~ (v1_relat_1 @ X17))),
% 6.04/6.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.04/6.24  thf('97', plain,
% 6.04/6.24      (![X0 : $i, X1 : $i]:
% 6.04/6.24         (~ (v1_relat_1 @ X0)
% 6.04/6.24          | (v1_relat_1 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 6.04/6.24      inference('sup-', [status(thm)], ['95', '96'])).
% 6.04/6.24  thf('98', plain,
% 6.04/6.24      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 6.04/6.24      inference('sup+', [status(thm)], ['94', '97'])).
% 6.04/6.24  thf('99', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.04/6.24      inference('sup-', [status(thm)], ['93', '98'])).
% 6.04/6.24  thf('100', plain,
% 6.04/6.24      (![X0 : $i]:
% 6.04/6.24         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ (k2_relat_1 @ X0))
% 6.04/6.24          | ~ (v1_relat_1 @ X0))),
% 6.04/6.24      inference('demod', [status(thm)], ['92', '99'])).
% 6.04/6.24  thf('101', plain,
% 6.04/6.24      (![X0 : $i]:
% 6.04/6.24         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 6.04/6.24          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 6.04/6.24      inference('sup+', [status(thm)], ['89', '100'])).
% 6.04/6.24  thf('102', plain,
% 6.04/6.24      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 6.04/6.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.04/6.24  thf('103', plain, ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 6.04/6.24      inference('demod', [status(thm)], ['101', '102'])).
% 6.04/6.24  thf('104', plain,
% 6.04/6.24      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.04/6.24      inference('sup-', [status(thm)], ['55', '56'])).
% 6.04/6.24  thf('105', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.04/6.24      inference('sup-', [status(thm)], ['103', '104'])).
% 6.04/6.24  thf('106', plain,
% 6.04/6.24      (![X26 : $i]:
% 6.04/6.24         (((k2_relat_1 @ X26) != (k1_xboole_0))
% 6.04/6.24          | ((k1_relat_1 @ X26) = (k1_xboole_0))
% 6.04/6.24          | ~ (v1_relat_1 @ X26))),
% 6.04/6.24      inference('cnf', [status(esa)], [t65_relat_1])).
% 6.04/6.24  thf('107', plain,
% 6.04/6.24      ((((k1_xboole_0) != (k1_xboole_0))
% 6.04/6.24        | ~ (v1_relat_1 @ k1_xboole_0)
% 6.04/6.24        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 6.04/6.24      inference('sup-', [status(thm)], ['105', '106'])).
% 6.04/6.24  thf('108', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.04/6.24      inference('sup-', [status(thm)], ['93', '98'])).
% 6.04/6.24  thf('109', plain,
% 6.04/6.24      ((((k1_xboole_0) != (k1_xboole_0))
% 6.04/6.24        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 6.04/6.24      inference('demod', [status(thm)], ['107', '108'])).
% 6.04/6.24  thf('110', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.04/6.24      inference('simplify', [status(thm)], ['109'])).
% 6.04/6.24  thf('111', plain,
% 6.04/6.24      (![X0 : $i, X1 : $i]:
% 6.04/6.24         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.04/6.24      inference('demod', [status(thm)], ['86', '110'])).
% 6.04/6.24  thf('112', plain,
% 6.04/6.24      (![X0 : $i, X1 : $i]:
% 6.04/6.24         (((X1) = (k1_xboole_0))
% 6.04/6.24          | ~ (v1_xboole_0 @ X0)
% 6.04/6.24          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 6.04/6.24          | ((X1) = (k1_xboole_0)))),
% 6.04/6.24      inference('demod', [status(thm)], ['83', '111'])).
% 6.04/6.24  thf('113', plain,
% 6.04/6.24      (![X0 : $i, X1 : $i]:
% 6.04/6.24         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 6.04/6.24          | ~ (v1_xboole_0 @ X0)
% 6.04/6.24          | ((X1) = (k1_xboole_0)))),
% 6.04/6.24      inference('simplify', [status(thm)], ['112'])).
% 6.04/6.24  thf('114', plain,
% 6.04/6.24      (![X0 : $i]:
% 6.04/6.24         (((k1_relat_1 @ sk_B_1) = (k1_xboole_0))
% 6.04/6.24          | ((X0) = (k1_xboole_0))
% 6.04/6.24          | ~ (v1_xboole_0 @ sk_A))),
% 6.04/6.24      inference('sup-', [status(thm)], ['71', '113'])).
% 6.04/6.24  thf('115', plain,
% 6.04/6.24      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_A))),
% 6.04/6.24      inference('condensation', [status(thm)], ['114'])).
% 6.04/6.24  thf('116', plain, (((sk_A) = (k1_xboole_0))),
% 6.04/6.24      inference('sup-', [status(thm)], ['29', '30'])).
% 6.04/6.24  thf('117', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.04/6.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.04/6.24  thf('118', plain, (((k1_relat_1 @ sk_B_1) = (k1_xboole_0))),
% 6.04/6.24      inference('demod', [status(thm)], ['115', '116', '117'])).
% 6.04/6.24  thf('119', plain,
% 6.04/6.24      (![X33 : $i, X34 : $i]:
% 6.04/6.24         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 6.04/6.24      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.04/6.24  thf('120', plain,
% 6.04/6.24      (![X33 : $i, X34 : $i]:
% 6.04/6.24         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 6.04/6.24      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.04/6.24  thf('121', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 6.04/6.24      inference('simplify', [status(thm)], ['120'])).
% 6.04/6.24  thf('122', plain,
% 6.04/6.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.24         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 6.04/6.24      inference('sup+', [status(thm)], ['119', '121'])).
% 6.04/6.24  thf('123', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 6.04/6.24      inference('eq_fact', [status(thm)], ['122'])).
% 6.04/6.24  thf('124', plain, ($false),
% 6.04/6.24      inference('demod', [status(thm)], ['32', '118', '123'])).
% 6.04/6.24  
% 6.04/6.24  % SZS output end Refutation
% 6.04/6.24  
% 6.04/6.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
