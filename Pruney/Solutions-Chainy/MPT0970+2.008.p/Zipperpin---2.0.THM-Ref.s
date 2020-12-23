%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dTMtO9gW7B

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:17 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 187 expanded)
%              Number of leaves         :   42 (  74 expanded)
%              Depth                    :   22
%              Number of atoms          :  778 (2098 expanded)
%              Number of equality atoms :   48 ( 135 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( X37
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X37 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('21',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf('37',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('56',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X15 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','69'])).

thf('71',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['37','40'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dTMtO9gW7B
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:46:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 313 iterations in 0.331s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.80  thf(sk_E_type, type, sk_E: $i > $i).
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.80  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.59/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.59/0.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.59/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.80  thf(t16_funct_2, conjecture,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.80       ( ( ![D:$i]:
% 0.59/0.80           ( ~( ( r2_hidden @ D @ B ) & 
% 0.59/0.80                ( ![E:$i]:
% 0.59/0.80                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.59/0.80                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.59/0.80         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.80        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.80            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.80          ( ( ![D:$i]:
% 0.59/0.80              ( ~( ( r2_hidden @ D @ B ) & 
% 0.59/0.80                   ( ![E:$i]:
% 0.59/0.80                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.59/0.80                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.59/0.80            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.59/0.80  thf('0', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(cc2_relset_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.80  thf('1', plain,
% 0.59/0.80      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.59/0.80         ((v5_relat_1 @ X20 @ X22)
% 0.59/0.80          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.59/0.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.80  thf('2', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.59/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.80  thf(d19_relat_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( v1_relat_1 @ B ) =>
% 0.59/0.80       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i]:
% 0.59/0.80         (~ (v5_relat_1 @ X13 @ X14)
% 0.59/0.80          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.59/0.80          | ~ (v1_relat_1 @ X13))),
% 0.59/0.80      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.80  thf('5', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(cc1_relset_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.80       ( v1_relat_1 @ C ) ))).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.80         ((v1_relat_1 @ X17)
% 0.59/0.80          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.59/0.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.80  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.80      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.80  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.59/0.80      inference('demod', [status(thm)], ['4', '7'])).
% 0.59/0.80  thf(d10_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      (![X4 : $i, X6 : $i]:
% 0.59/0.80         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.59/0.80        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.80  thf(d3_tarski, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.80  thf('11', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      (![X37 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X37 @ sk_B)
% 0.59/0.80          | ((X37) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X37))))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B @ X0)
% 0.59/0.80          | ((sk_C @ X0 @ sk_B)
% 0.59/0.80              = (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (![X37 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X37 @ sk_B) | (r2_hidden @ (sk_E @ X37) @ sk_A))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B @ X0)
% 0.59/0.80          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf(d1_funct_2, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.59/0.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.59/0.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.59/0.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_1, axiom,
% 0.59/0.80    (![B:$i,A:$i]:
% 0.59/0.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.80       ( zip_tseitin_0 @ B @ A ) ))).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X29 : $i, X30 : $i]:
% 0.59/0.80         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X29 : $i, X30 : $i]:
% 0.59/0.80         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.80         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.59/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.59/0.80  thf(zf_stmt_3, axiom,
% 0.59/0.80    (![C:$i,B:$i,A:$i]:
% 0.59/0.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.59/0.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.80  thf(zf_stmt_5, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.59/0.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.59/0.80         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.59/0.80          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.59/0.80          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.59/0.80        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((zip_tseitin_0 @ X1 @ X0)
% 0.59/0.80          | ((sk_B) = (X1))
% 0.59/0.80          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['19', '22'])).
% 0.59/0.80  thf('24', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.59/0.80      inference('demod', [status(thm)], ['4', '7'])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.80  thf('27', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.59/0.80      inference('simplify', [status(thm)], ['26'])).
% 0.59/0.80  thf(t3_subset, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      (![X7 : $i, X9 : $i]:
% 0.59/0.80         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.80  thf('29', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.59/0.80  thf(t5_subset, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.59/0.80          ( v1_xboole_0 @ C ) ) ))).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X10 @ X11)
% 0.59/0.80          | ~ (v1_xboole_0 @ X12)
% 0.59/0.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t5_subset])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['25', '31'])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (![X4 : $i, X6 : $i]:
% 0.59/0.80         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.80  thf('35', plain,
% 0.59/0.80      ((((k2_relat_1 @ sk_C_1) = (sk_B)) | ~ (v1_xboole_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['24', '34'])).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_xboole_0 @ X0)
% 0.59/0.80          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.59/0.80          | (zip_tseitin_0 @ X0 @ X1)
% 0.59/0.80          | ((k2_relat_1 @ sk_C_1) = (sk_B)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['23', '35'])).
% 0.59/0.80  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(redefinition_k2_relset_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.80       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.80         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.59/0.80          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.59/0.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.80  thf('41', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['37', '40'])).
% 0.59/0.80  thf('42', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_xboole_0 @ X0)
% 0.59/0.80          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.59/0.80          | (zip_tseitin_0 @ X0 @ X1))),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['36', '41'])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      (![X29 : $i, X30 : $i]:
% 0.59/0.80         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.80  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.80  thf('45', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['43', '44'])).
% 0.59/0.80  thf('46', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((zip_tseitin_0 @ X0 @ X1) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('clc', [status(thm)], ['42', '45'])).
% 0.59/0.80  thf('47', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.80         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.59/0.80          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.59/0.80          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.80  thf('49', plain,
% 0.59/0.80      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.59/0.80        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['47', '48'])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.59/0.80         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.59/0.80          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.59/0.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.80  thf('52', plain,
% 0.59/0.80      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.80  thf('53', plain,
% 0.59/0.80      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.59/0.80        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['49', '52'])).
% 0.59/0.80  thf('54', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((zip_tseitin_0 @ X1 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['46', '53'])).
% 0.59/0.80  thf('55', plain,
% 0.59/0.80      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.59/0.80        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.80  thf('56', plain,
% 0.59/0.80      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 0.59/0.80        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.80  thf('57', plain,
% 0.59/0.80      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.59/0.80        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['49', '52'])).
% 0.59/0.80  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.59/0.80      inference('clc', [status(thm)], ['56', '57'])).
% 0.59/0.80  thf(t12_funct_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.80       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.59/0.80         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.59/0.80  thf('59', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.59/0.80          | (r2_hidden @ (k1_funct_1 @ X16 @ X15) @ (k2_relat_1 @ X16))
% 0.59/0.80          | ~ (v1_funct_1 @ X16)
% 0.59/0.80          | ~ (v1_relat_1 @ X16))),
% 0.59/0.80      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.59/0.80  thf('60', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.80          | ~ (v1_relat_1 @ sk_C_1)
% 0.59/0.80          | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.80          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['58', '59'])).
% 0.59/0.80  thf('61', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.80      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.80  thf('62', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('63', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.80          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.59/0.80  thf('64', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B @ X0)
% 0.59/0.80          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.59/0.80             (k2_relat_1 @ sk_C_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['16', '63'])).
% 0.59/0.80  thf('65', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_1))
% 0.59/0.80          | (r1_tarski @ sk_B @ X0)
% 0.59/0.80          | (r1_tarski @ sk_B @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['13', '64'])).
% 0.59/0.80  thf('66', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B @ X0)
% 0.59/0.80          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_1)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['65'])).
% 0.59/0.80  thf('67', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('68', plain,
% 0.59/0.80      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.59/0.80        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['66', '67'])).
% 0.59/0.80  thf('69', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.59/0.80      inference('simplify', [status(thm)], ['68'])).
% 0.59/0.80  thf('70', plain, (((sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.59/0.80      inference('demod', [status(thm)], ['10', '69'])).
% 0.59/0.80  thf('71', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['37', '40'])).
% 0.59/0.80  thf('72', plain, ($false),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.65/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
