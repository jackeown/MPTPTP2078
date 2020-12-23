%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m6bODgi5B0

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:53 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 543 expanded)
%              Number of leaves         :   36 ( 179 expanded)
%              Depth                    :   26
%              Number of atoms          : 1173 (4529 expanded)
%              Number of equality atoms :   60 ( 172 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( r1_tarski @ X20 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30
       != ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['14'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','21','22'])).

thf('24',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['15','23'])).

thf('25',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['13','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('27',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('32',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30
       != ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X29 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('38',plain,(
    ! [X28: $i] :
      ( zip_tseitin_0 @ X28 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('40',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['36','42'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('62',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relset_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('76',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('85',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','85'])).

thf('87',plain,(
    ! [X20: $i] :
      ( ( r1_tarski @ X20 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('104',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B
        = ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','106'])).

thf('108',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['14'])).

thf('109',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_funct_2 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_B ) @ sk_A )
        | ( zip_tseitin_0 @ sk_A @ X1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
        | ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ sk_A @ X0 ) )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','109'])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
        | ( zip_tseitin_0 @ sk_A @ X0 ) )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
        | ~ ( v1_xboole_0 @ sk_B )
        | ( zip_tseitin_0 @ sk_A @ X0 ) )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','112'])).

thf('114',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relset_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k1_relset_1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B
        = ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','106'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ X4 )
      | ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_A @ X3 ) ) ),
    inference('sup-',[status(thm)],['118','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(condensation,[status(thm)],['123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_A @ X0 )
        | ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['113','124'])).

thf('126',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_A @ X0 )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','125'])).

thf('127',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','21','22'])).

thf('128',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(simpl_trail,[status(thm)],['126','127'])).

thf('129',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['28','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['25','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m6bODgi5B0
% 0.17/0.38  % Computer   : n025.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 18:52:51 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 1.36/1.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.36/1.62  % Solved by: fo/fo7.sh
% 1.36/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.62  % done 1732 iterations in 1.121s
% 1.36/1.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.36/1.62  % SZS output start Refutation
% 1.36/1.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.36/1.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.36/1.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.36/1.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.62  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.36/1.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.36/1.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.36/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.36/1.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.36/1.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.36/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.36/1.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.36/1.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.36/1.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.36/1.62  thf(t4_funct_2, conjecture,
% 1.36/1.62    (![A:$i,B:$i]:
% 1.36/1.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.36/1.62       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.36/1.62         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.36/1.62           ( m1_subset_1 @
% 1.36/1.62             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.36/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.62    (~( ![A:$i,B:$i]:
% 1.36/1.62        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.36/1.62          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.36/1.62            ( ( v1_funct_1 @ B ) & 
% 1.36/1.62              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.36/1.62              ( m1_subset_1 @
% 1.36/1.62                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 1.36/1.62    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 1.36/1.62  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.62  thf(t21_relat_1, axiom,
% 1.36/1.62    (![A:$i]:
% 1.36/1.62     ( ( v1_relat_1 @ A ) =>
% 1.36/1.62       ( r1_tarski @
% 1.36/1.62         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.36/1.62  thf('1', plain,
% 1.36/1.62      (![X20 : $i]:
% 1.36/1.62         ((r1_tarski @ X20 @ 
% 1.36/1.62           (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20)))
% 1.36/1.62          | ~ (v1_relat_1 @ X20))),
% 1.36/1.62      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.36/1.62  thf(t3_subset, axiom,
% 1.36/1.62    (![A:$i,B:$i]:
% 1.36/1.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.36/1.62  thf('2', plain,
% 1.36/1.62      (![X11 : $i, X13 : $i]:
% 1.36/1.62         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.36/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.62  thf('3', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         (~ (v1_relat_1 @ X0)
% 1.36/1.62          | (m1_subset_1 @ X0 @ 
% 1.36/1.62             (k1_zfmisc_1 @ 
% 1.36/1.62              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.36/1.62      inference('sup-', [status(thm)], ['1', '2'])).
% 1.36/1.62  thf(t14_relset_1, axiom,
% 1.36/1.62    (![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.62     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.36/1.62       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 1.36/1.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 1.36/1.62  thf('4', plain,
% 1.36/1.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.36/1.62         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 1.36/1.62          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.36/1.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.36/1.62      inference('cnf', [status(esa)], [t14_relset_1])).
% 1.36/1.62  thf('5', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         (~ (v1_relat_1 @ X0)
% 1.36/1.62          | (m1_subset_1 @ X0 @ 
% 1.36/1.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.36/1.62          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.36/1.62      inference('sup-', [status(thm)], ['3', '4'])).
% 1.36/1.62  thf('6', plain,
% 1.36/1.62      (((m1_subset_1 @ sk_B @ 
% 1.36/1.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 1.36/1.62        | ~ (v1_relat_1 @ sk_B))),
% 1.36/1.62      inference('sup-', [status(thm)], ['0', '5'])).
% 1.36/1.62  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.62  thf('8', plain,
% 1.36/1.62      ((m1_subset_1 @ sk_B @ 
% 1.36/1.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('demod', [status(thm)], ['6', '7'])).
% 1.36/1.62  thf(redefinition_k1_relset_1, axiom,
% 1.36/1.62    (![A:$i,B:$i,C:$i]:
% 1.36/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.36/1.62  thf('9', plain,
% 1.36/1.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.36/1.62         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 1.36/1.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.36/1.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.36/1.62  thf('10', plain,
% 1.36/1.62      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 1.36/1.62      inference('sup-', [status(thm)], ['8', '9'])).
% 1.36/1.62  thf(d1_funct_2, axiom,
% 1.36/1.62    (![A:$i,B:$i,C:$i]:
% 1.36/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.36/1.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.36/1.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.36/1.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.36/1.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.36/1.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.36/1.62  thf(zf_stmt_1, axiom,
% 1.36/1.62    (![C:$i,B:$i,A:$i]:
% 1.36/1.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.36/1.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.36/1.62  thf('11', plain,
% 1.36/1.62      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.36/1.62         (((X30) != (k1_relset_1 @ X30 @ X31 @ X32))
% 1.36/1.62          | (v1_funct_2 @ X32 @ X30 @ X31)
% 1.36/1.62          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.36/1.62  thf('12', plain,
% 1.36/1.62      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 1.36/1.62        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 1.36/1.62        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.36/1.62      inference('sup-', [status(thm)], ['10', '11'])).
% 1.36/1.62  thf('13', plain,
% 1.36/1.62      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.36/1.62        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.36/1.62      inference('simplify', [status(thm)], ['12'])).
% 1.36/1.62  thf('14', plain,
% 1.36/1.62      ((~ (v1_funct_1 @ sk_B)
% 1.36/1.62        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.36/1.62        | ~ (m1_subset_1 @ sk_B @ 
% 1.36/1.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.62  thf('15', plain,
% 1.36/1.62      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.36/1.62         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('split', [status(esa)], ['14'])).
% 1.36/1.62  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.62  thf('17', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 1.36/1.62      inference('split', [status(esa)], ['14'])).
% 1.36/1.62  thf('18', plain, (((v1_funct_1 @ sk_B))),
% 1.36/1.62      inference('sup-', [status(thm)], ['16', '17'])).
% 1.36/1.62  thf('19', plain,
% 1.36/1.62      ((m1_subset_1 @ sk_B @ 
% 1.36/1.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('demod', [status(thm)], ['6', '7'])).
% 1.36/1.62  thf('20', plain,
% 1.36/1.62      ((~ (m1_subset_1 @ sk_B @ 
% 1.36/1.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 1.36/1.62         <= (~
% 1.36/1.62             ((m1_subset_1 @ sk_B @ 
% 1.36/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 1.36/1.62      inference('split', [status(esa)], ['14'])).
% 1.36/1.62  thf('21', plain,
% 1.36/1.62      (((m1_subset_1 @ sk_B @ 
% 1.36/1.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 1.36/1.62      inference('sup-', [status(thm)], ['19', '20'])).
% 1.36/1.62  thf('22', plain,
% 1.36/1.62      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 1.36/1.62       ~
% 1.36/1.62       ((m1_subset_1 @ sk_B @ 
% 1.36/1.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 1.36/1.62       ~ ((v1_funct_1 @ sk_B))),
% 1.36/1.62      inference('split', [status(esa)], ['14'])).
% 1.36/1.62  thf('23', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.36/1.62      inference('sat_resolution*', [status(thm)], ['18', '21', '22'])).
% 1.36/1.62  thf('24', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.36/1.62      inference('simpl_trail', [status(thm)], ['15', '23'])).
% 1.36/1.62  thf('25', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.36/1.62      inference('clc', [status(thm)], ['13', '24'])).
% 1.36/1.62  thf('26', plain,
% 1.36/1.62      ((m1_subset_1 @ sk_B @ 
% 1.36/1.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('demod', [status(thm)], ['6', '7'])).
% 1.36/1.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.36/1.62  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.36/1.62  thf(zf_stmt_4, axiom,
% 1.36/1.62    (![B:$i,A:$i]:
% 1.36/1.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.36/1.62       ( zip_tseitin_0 @ B @ A ) ))).
% 1.36/1.62  thf(zf_stmt_5, axiom,
% 1.36/1.62    (![A:$i,B:$i,C:$i]:
% 1.36/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.36/1.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.36/1.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.36/1.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.36/1.62  thf('27', plain,
% 1.36/1.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.36/1.62         (~ (zip_tseitin_0 @ X33 @ X34)
% 1.36/1.62          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 1.36/1.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.36/1.62  thf('28', plain,
% 1.36/1.62      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 1.36/1.62        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['26', '27'])).
% 1.36/1.62  thf(t4_subset_1, axiom,
% 1.36/1.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.36/1.62  thf('29', plain,
% 1.36/1.62      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 1.36/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.36/1.62  thf('30', plain,
% 1.36/1.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.36/1.62         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 1.36/1.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.36/1.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.36/1.62  thf('31', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['29', '30'])).
% 1.36/1.62  thf(t60_relat_1, axiom,
% 1.36/1.62    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.36/1.62     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.36/1.62  thf('32', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.36/1.62  thf('33', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.62      inference('demod', [status(thm)], ['31', '32'])).
% 1.36/1.62  thf('34', plain,
% 1.36/1.62      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.36/1.62         (((X30) != (k1_relset_1 @ X30 @ X31 @ X32))
% 1.36/1.62          | (v1_funct_2 @ X32 @ X30 @ X31)
% 1.36/1.62          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.36/1.62  thf('35', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         (((X1) != (k1_xboole_0))
% 1.36/1.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.36/1.62          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['33', '34'])).
% 1.36/1.62  thf('36', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.36/1.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.62      inference('simplify', [status(thm)], ['35'])).
% 1.36/1.62  thf('37', plain,
% 1.36/1.62      (![X28 : $i, X29 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ X28 @ X29) | ((X29) != (k1_xboole_0)))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.36/1.62  thf('38', plain, (![X28 : $i]: (zip_tseitin_0 @ X28 @ k1_xboole_0)),
% 1.36/1.62      inference('simplify', [status(thm)], ['37'])).
% 1.36/1.62  thf('39', plain,
% 1.36/1.62      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 1.36/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.36/1.62  thf('40', plain,
% 1.36/1.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.36/1.62         (~ (zip_tseitin_0 @ X33 @ X34)
% 1.36/1.62          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 1.36/1.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.36/1.62  thf('41', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.36/1.62      inference('sup-', [status(thm)], ['39', '40'])).
% 1.36/1.62  thf('42', plain,
% 1.36/1.62      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.36/1.62      inference('sup-', [status(thm)], ['38', '41'])).
% 1.36/1.62  thf('43', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.36/1.62      inference('demod', [status(thm)], ['36', '42'])).
% 1.36/1.62  thf(d3_tarski, axiom,
% 1.36/1.62    (![A:$i,B:$i]:
% 1.36/1.62     ( ( r1_tarski @ A @ B ) <=>
% 1.36/1.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.36/1.62  thf('44', plain,
% 1.36/1.62      (![X1 : $i, X3 : $i]:
% 1.36/1.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.36/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.62  thf(d10_xboole_0, axiom,
% 1.36/1.62    (![A:$i,B:$i]:
% 1.36/1.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.36/1.62  thf('45', plain,
% 1.36/1.62      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.36/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.62  thf('46', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.36/1.62      inference('simplify', [status(thm)], ['45'])).
% 1.36/1.62  thf('47', plain,
% 1.36/1.62      (![X11 : $i, X13 : $i]:
% 1.36/1.62         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.36/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.62  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['46', '47'])).
% 1.36/1.62  thf(t5_subset, axiom,
% 1.36/1.62    (![A:$i,B:$i,C:$i]:
% 1.36/1.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.36/1.62          ( v1_xboole_0 @ C ) ) ))).
% 1.36/1.62  thf('49', plain,
% 1.36/1.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.36/1.62         (~ (r2_hidden @ X17 @ X18)
% 1.36/1.62          | ~ (v1_xboole_0 @ X19)
% 1.36/1.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.36/1.62      inference('cnf', [status(esa)], [t5_subset])).
% 1.36/1.62  thf('50', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['48', '49'])).
% 1.36/1.62  thf('51', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['44', '50'])).
% 1.36/1.62  thf('52', plain,
% 1.36/1.62      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 1.36/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.36/1.62  thf('53', plain,
% 1.36/1.62      (![X11 : $i, X12 : $i]:
% 1.36/1.62         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.36/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.62  thf('54', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.36/1.62      inference('sup-', [status(thm)], ['52', '53'])).
% 1.36/1.62  thf('55', plain,
% 1.36/1.62      (![X4 : $i, X6 : $i]:
% 1.36/1.62         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.36/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.62  thf('56', plain,
% 1.36/1.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['54', '55'])).
% 1.36/1.62  thf('57', plain,
% 1.36/1.62      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['51', '56'])).
% 1.36/1.62  thf('58', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.36/1.62  thf('59', plain,
% 1.36/1.62      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup+', [status(thm)], ['57', '58'])).
% 1.36/1.62  thf('60', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.36/1.62  thf('61', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['44', '50'])).
% 1.36/1.62  thf('62', plain,
% 1.36/1.62      (![X11 : $i, X13 : $i]:
% 1.36/1.62         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.36/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.62  thf('63', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['61', '62'])).
% 1.36/1.62  thf('64', plain,
% 1.36/1.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.36/1.62         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 1.36/1.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.36/1.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.36/1.62  thf('65', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.62         (~ (v1_xboole_0 @ X2)
% 1.36/1.62          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['63', '64'])).
% 1.36/1.62  thf('66', plain,
% 1.36/1.62      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['51', '56'])).
% 1.36/1.62  thf('67', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.62      inference('demod', [status(thm)], ['31', '32'])).
% 1.36/1.62  thf('68', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.62         (((k1_relset_1 @ X2 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup+', [status(thm)], ['66', '67'])).
% 1.36/1.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.36/1.62  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.62  thf('70', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.62         ((v1_xboole_0 @ (k1_relset_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup+', [status(thm)], ['68', '69'])).
% 1.36/1.62  thf('71', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.36/1.62          | ~ (v1_xboole_0 @ X0)
% 1.36/1.62          | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup+', [status(thm)], ['65', '70'])).
% 1.36/1.62  thf('72', plain,
% 1.36/1.62      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.36/1.62      inference('simplify', [status(thm)], ['71'])).
% 1.36/1.62  thf('73', plain,
% 1.36/1.62      (![X1 : $i, X3 : $i]:
% 1.36/1.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.36/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.62  thf('74', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.62  thf('75', plain,
% 1.36/1.62      (![X28 : $i, X29 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.36/1.62  thf('76', plain,
% 1.36/1.62      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 1.36/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.36/1.62  thf('77', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.62         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.36/1.62      inference('sup+', [status(thm)], ['75', '76'])).
% 1.36/1.62  thf('78', plain,
% 1.36/1.62      (![X11 : $i, X12 : $i]:
% 1.36/1.62         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.36/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.62  thf('79', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ X1 @ X2) | (r1_tarski @ X1 @ X0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['77', '78'])).
% 1.36/1.62  thf('80', plain,
% 1.36/1.62      (![X4 : $i, X6 : $i]:
% 1.36/1.62         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.36/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.62  thf('81', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['79', '80'])).
% 1.36/1.62  thf('82', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         (((k2_relat_1 @ sk_B) = (sk_A)) | (zip_tseitin_0 @ sk_A @ X0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['74', '81'])).
% 1.36/1.62  thf('83', plain,
% 1.36/1.62      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['51', '56'])).
% 1.36/1.62  thf(t113_zfmisc_1, axiom,
% 1.36/1.62    (![A:$i,B:$i]:
% 1.36/1.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.36/1.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.36/1.62  thf('84', plain,
% 1.36/1.62      (![X8 : $i, X9 : $i]:
% 1.36/1.62         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 1.36/1.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.36/1.62  thf('85', plain,
% 1.36/1.62      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.62      inference('simplify', [status(thm)], ['84'])).
% 1.36/1.62  thf('86', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup+', [status(thm)], ['83', '85'])).
% 1.36/1.62  thf('87', plain,
% 1.36/1.62      (![X20 : $i]:
% 1.36/1.62         ((r1_tarski @ X20 @ 
% 1.36/1.62           (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20)))
% 1.36/1.62          | ~ (v1_relat_1 @ X20))),
% 1.36/1.62      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.36/1.62  thf('88', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         ((r1_tarski @ X0 @ k1_xboole_0)
% 1.36/1.62          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.36/1.62          | ~ (v1_relat_1 @ X0))),
% 1.36/1.62      inference('sup+', [status(thm)], ['86', '87'])).
% 1.36/1.62  thf('89', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         (~ (v1_xboole_0 @ sk_A)
% 1.36/1.62          | (zip_tseitin_0 @ sk_A @ X0)
% 1.36/1.62          | ~ (v1_relat_1 @ sk_B)
% 1.36/1.62          | (r1_tarski @ sk_B @ k1_xboole_0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['82', '88'])).
% 1.36/1.62  thf('90', plain, ((v1_relat_1 @ sk_B)),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.62  thf('91', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         (~ (v1_xboole_0 @ sk_A)
% 1.36/1.62          | (zip_tseitin_0 @ sk_A @ X0)
% 1.36/1.62          | (r1_tarski @ sk_B @ k1_xboole_0))),
% 1.36/1.62      inference('demod', [status(thm)], ['89', '90'])).
% 1.36/1.62  thf('92', plain,
% 1.36/1.62      (![X28 : $i, X29 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.36/1.62  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.62  thf('94', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.36/1.62      inference('sup+', [status(thm)], ['92', '93'])).
% 1.36/1.62  thf('95', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         ((r1_tarski @ sk_B @ k1_xboole_0) | (zip_tseitin_0 @ sk_A @ X0))),
% 1.36/1.62      inference('clc', [status(thm)], ['91', '94'])).
% 1.36/1.62  thf('96', plain,
% 1.36/1.62      (![X11 : $i, X13 : $i]:
% 1.36/1.62         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.36/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.62  thf('97', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ sk_A @ X0)
% 1.36/1.62          | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['95', '96'])).
% 1.36/1.62  thf('98', plain,
% 1.36/1.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.36/1.62         (~ (r2_hidden @ X17 @ X18)
% 1.36/1.62          | ~ (v1_xboole_0 @ X19)
% 1.36/1.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.36/1.62      inference('cnf', [status(esa)], [t5_subset])).
% 1.36/1.62  thf('99', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ sk_A @ X1)
% 1.36/1.62          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.36/1.62          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.36/1.62      inference('sup-', [status(thm)], ['97', '98'])).
% 1.36/1.62  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.62  thf('101', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ sk_A @ X1) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.36/1.62      inference('demod', [status(thm)], ['99', '100'])).
% 1.36/1.62  thf('102', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_0 @ sk_A @ X1))),
% 1.36/1.62      inference('sup-', [status(thm)], ['73', '101'])).
% 1.36/1.62  thf('103', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['44', '50'])).
% 1.36/1.62  thf('104', plain,
% 1.36/1.62      (![X4 : $i, X6 : $i]:
% 1.36/1.62         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.36/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.62  thf('105', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['103', '104'])).
% 1.36/1.62  thf('106', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ sk_A @ X1) | ((sk_B) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup-', [status(thm)], ['102', '105'])).
% 1.36/1.62  thf('107', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         (~ (v1_xboole_0 @ X0)
% 1.36/1.62          | ((sk_B) = (k1_relat_1 @ X0))
% 1.36/1.62          | (zip_tseitin_0 @ sk_A @ X1))),
% 1.36/1.62      inference('sup-', [status(thm)], ['72', '106'])).
% 1.36/1.62  thf('108', plain,
% 1.36/1.62      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.36/1.62         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('split', [status(esa)], ['14'])).
% 1.36/1.62  thf('109', plain,
% 1.36/1.62      ((![X0 : $i, X1 : $i]:
% 1.36/1.62          (~ (v1_funct_2 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.36/1.62           | (zip_tseitin_0 @ sk_A @ X1)
% 1.36/1.62           | ~ (v1_xboole_0 @ X0)))
% 1.36/1.62         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['107', '108'])).
% 1.36/1.62  thf('110', plain,
% 1.36/1.62      ((![X0 : $i]:
% 1.36/1.62          (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.36/1.62           | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.36/1.62           | (zip_tseitin_0 @ sk_A @ X0)))
% 1.36/1.62         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['60', '109'])).
% 1.36/1.62  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.62  thf('112', plain,
% 1.36/1.62      ((![X0 : $i]:
% 1.36/1.62          (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.36/1.62           | (zip_tseitin_0 @ sk_A @ X0)))
% 1.36/1.62         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('demod', [status(thm)], ['110', '111'])).
% 1.36/1.62  thf('113', plain,
% 1.36/1.62      ((![X0 : $i]:
% 1.36/1.62          (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)
% 1.36/1.62           | ~ (v1_xboole_0 @ sk_B)
% 1.36/1.62           | (zip_tseitin_0 @ sk_A @ X0)))
% 1.36/1.62         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['59', '112'])).
% 1.36/1.62  thf('114', plain,
% 1.36/1.62      (![X28 : $i, X29 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.36/1.62  thf('115', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.62      inference('demod', [status(thm)], ['31', '32'])).
% 1.36/1.62  thf('116', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.36/1.62         (((k1_relset_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 1.36/1.62          | (zip_tseitin_0 @ X0 @ X3))),
% 1.36/1.62      inference('sup+', [status(thm)], ['114', '115'])).
% 1.36/1.62  thf('117', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.62  thf('118', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.36/1.62         ((v1_xboole_0 @ (k1_relset_1 @ X2 @ X1 @ X0))
% 1.36/1.62          | (zip_tseitin_0 @ X0 @ X3))),
% 1.36/1.62      inference('sup+', [status(thm)], ['116', '117'])).
% 1.36/1.62  thf('119', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         (~ (v1_xboole_0 @ X0)
% 1.36/1.62          | ((sk_B) = (k1_relat_1 @ X0))
% 1.36/1.62          | (zip_tseitin_0 @ sk_A @ X1))),
% 1.36/1.62      inference('sup-', [status(thm)], ['72', '106'])).
% 1.36/1.62  thf('120', plain,
% 1.36/1.62      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.36/1.62      inference('simplify', [status(thm)], ['71'])).
% 1.36/1.62  thf('121', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         ((v1_xboole_0 @ sk_B)
% 1.36/1.62          | (zip_tseitin_0 @ sk_A @ X1)
% 1.36/1.62          | ~ (v1_xboole_0 @ X0)
% 1.36/1.62          | ~ (v1_xboole_0 @ X0))),
% 1.36/1.62      inference('sup+', [status(thm)], ['119', '120'])).
% 1.36/1.62  thf('122', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]:
% 1.36/1.62         (~ (v1_xboole_0 @ X0)
% 1.36/1.62          | (zip_tseitin_0 @ sk_A @ X1)
% 1.36/1.62          | (v1_xboole_0 @ sk_B))),
% 1.36/1.62      inference('simplify', [status(thm)], ['121'])).
% 1.36/1.62  thf('123', plain,
% 1.36/1.62      (![X0 : $i, X3 : $i, X4 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ X0 @ X4)
% 1.36/1.62          | (v1_xboole_0 @ sk_B)
% 1.36/1.62          | (zip_tseitin_0 @ sk_A @ X3))),
% 1.36/1.62      inference('sup-', [status(thm)], ['118', '122'])).
% 1.36/1.62  thf('124', plain,
% 1.36/1.62      (![X0 : $i]: ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ sk_B))),
% 1.36/1.62      inference('condensation', [status(thm)], ['123'])).
% 1.36/1.62  thf('125', plain,
% 1.36/1.62      ((![X0 : $i]:
% 1.36/1.62          ((zip_tseitin_0 @ sk_A @ X0)
% 1.36/1.62           | ~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)))
% 1.36/1.62         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('clc', [status(thm)], ['113', '124'])).
% 1.36/1.62  thf('126', plain,
% 1.36/1.62      ((![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0))
% 1.36/1.62         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['43', '125'])).
% 1.36/1.62  thf('127', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.36/1.62      inference('sat_resolution*', [status(thm)], ['18', '21', '22'])).
% 1.36/1.62  thf('128', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 1.36/1.62      inference('simpl_trail', [status(thm)], ['126', '127'])).
% 1.36/1.62  thf('129', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.36/1.62      inference('demod', [status(thm)], ['28', '128'])).
% 1.36/1.62  thf('130', plain, ($false), inference('demod', [status(thm)], ['25', '129'])).
% 1.36/1.62  
% 1.36/1.62  % SZS output end Refutation
% 1.36/1.62  
% 1.36/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
