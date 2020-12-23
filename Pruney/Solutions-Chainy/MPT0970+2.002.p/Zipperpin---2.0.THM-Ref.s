%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kl4YIYAmok

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:17 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 169 expanded)
%              Number of leaves         :   42 (  70 expanded)
%              Depth                    :   20
%              Number of atoms          :  729 (1755 expanded)
%              Number of equality atoms :   40 (  99 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B_1 )
      | ( X34
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B_1 )
      | ( r2_hidden @ ( sk_E @ X34 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
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

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('24',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','7'])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['40','47'])).

thf('49',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['26','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','49','52'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ X12 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('57',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( sk_B_1
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','64'])).

thf('66',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('68',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kl4YIYAmok
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.55/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.72  % Solved by: fo/fo7.sh
% 0.55/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.72  % done 235 iterations in 0.270s
% 0.55/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.72  % SZS output start Refutation
% 0.55/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.55/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.55/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.55/0.72  thf(sk_E_type, type, sk_E: $i > $i).
% 0.55/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.55/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.55/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.55/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.55/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.72  thf(t16_funct_2, conjecture,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.72       ( ( ![D:$i]:
% 0.55/0.72           ( ~( ( r2_hidden @ D @ B ) & 
% 0.55/0.72                ( ![E:$i]:
% 0.55/0.72                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.55/0.72                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.55/0.72         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.55/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.72          ( ( ![D:$i]:
% 0.55/0.72              ( ~( ( r2_hidden @ D @ B ) & 
% 0.55/0.72                   ( ![E:$i]:
% 0.55/0.72                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.55/0.72                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.55/0.72            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.55/0.72    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.55/0.72  thf('0', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(cc2_relset_1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.72  thf('1', plain,
% 0.55/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.55/0.72         ((v5_relat_1 @ X17 @ X19)
% 0.55/0.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.55/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.72  thf('2', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.55/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.72  thf(d19_relat_1, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( v1_relat_1 @ B ) =>
% 0.55/0.72       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.55/0.72  thf('3', plain,
% 0.55/0.72      (![X10 : $i, X11 : $i]:
% 0.55/0.72         (~ (v5_relat_1 @ X10 @ X11)
% 0.55/0.72          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.55/0.72          | ~ (v1_relat_1 @ X10))),
% 0.55/0.72      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.55/0.72  thf('4', plain,
% 0.55/0.72      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.55/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.72  thf('5', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(cc1_relset_1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.72       ( v1_relat_1 @ C ) ))).
% 0.55/0.72  thf('6', plain,
% 0.55/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.55/0.72         ((v1_relat_1 @ X14)
% 0.55/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.55/0.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.55/0.72  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.55/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.72  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.55/0.72      inference('demod', [status(thm)], ['4', '7'])).
% 0.55/0.72  thf(d10_xboole_0, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.72  thf('9', plain,
% 0.55/0.72      (![X7 : $i, X9 : $i]:
% 0.55/0.72         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.55/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.72  thf('10', plain,
% 0.55/0.72      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_1))
% 0.55/0.72        | ((sk_B_1) = (k2_relat_1 @ sk_C_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.55/0.72  thf(d3_tarski, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.55/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.55/0.72  thf('11', plain,
% 0.55/0.72      (![X4 : $i, X6 : $i]:
% 0.55/0.72         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.55/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.72  thf('12', plain,
% 0.55/0.72      (![X34 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X34 @ sk_B_1)
% 0.55/0.72          | ((X34) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X34))))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('13', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((r1_tarski @ sk_B_1 @ X0)
% 0.55/0.72          | ((sk_C @ X0 @ sk_B_1)
% 0.55/0.72              = (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ X0 @ sk_B_1)))))),
% 0.55/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.72  thf('14', plain,
% 0.55/0.72      (![X4 : $i, X6 : $i]:
% 0.55/0.72         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.55/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.72  thf('15', plain,
% 0.55/0.72      (![X34 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X34 @ sk_B_1) | (r2_hidden @ (sk_E @ X34) @ sk_A))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('16', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((r1_tarski @ sk_B_1 @ X0)
% 0.55/0.72          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B_1)) @ sk_A))),
% 0.55/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.55/0.72  thf('17', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(d1_funct_2, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.55/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.55/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.55/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.55/0.72  thf(zf_stmt_1, axiom,
% 0.55/0.72    (![C:$i,B:$i,A:$i]:
% 0.55/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.55/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.55/0.72  thf('18', plain,
% 0.55/0.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.72         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.55/0.72          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.55/0.72          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.72  thf('19', plain,
% 0.55/0.72      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.55/0.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.55/0.72  thf(zf_stmt_2, axiom,
% 0.55/0.72    (![B:$i,A:$i]:
% 0.55/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.55/0.72  thf('20', plain,
% 0.55/0.72      (![X26 : $i, X27 : $i]:
% 0.55/0.72         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.55/0.72  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.55/0.72  thf('22', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.55/0.72      inference('sup+', [status(thm)], ['20', '21'])).
% 0.55/0.72  thf('23', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.55/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.55/0.72  thf(zf_stmt_5, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.55/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.55/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.55/0.72  thf('24', plain,
% 0.55/0.72      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.72         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.55/0.72          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.55/0.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.55/0.72  thf('25', plain,
% 0.55/0.72      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.55/0.72        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.55/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.55/0.72  thf('26', plain,
% 0.55/0.72      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 0.55/0.72      inference('sup-', [status(thm)], ['22', '25'])).
% 0.55/0.72  thf('27', plain,
% 0.55/0.72      (![X4 : $i, X6 : $i]:
% 0.55/0.72         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.55/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.72  thf(d1_xboole_0, axiom,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.55/0.72  thf('28', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.72  thf('29', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.55/0.72  thf('30', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.55/0.72  thf('31', plain,
% 0.55/0.72      (![X7 : $i, X9 : $i]:
% 0.55/0.72         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.55/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.72  thf('32', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.55/0.72  thf('33', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['29', '32'])).
% 0.55/0.72  thf('34', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (sk_B_1))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('35', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         (((X0) != (sk_B_1))
% 0.55/0.72          | ~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.55/0.72          | ~ (v1_xboole_0 @ X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.55/0.72  thf('36', plain,
% 0.55/0.72      ((~ (v1_xboole_0 @ sk_B_1)
% 0.55/0.72        | ~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.55/0.72      inference('simplify', [status(thm)], ['35'])).
% 0.55/0.72  thf('37', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(redefinition_k2_relset_1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.55/0.72  thf('38', plain,
% 0.55/0.72      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.55/0.72         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.55/0.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.55/0.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.72  thf('39', plain,
% 0.55/0.72      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.55/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.72  thf('40', plain,
% 0.55/0.72      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.55/0.72      inference('demod', [status(thm)], ['36', '39'])).
% 0.55/0.72  thf('41', plain,
% 0.55/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.55/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.72  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.55/0.72      inference('demod', [status(thm)], ['4', '7'])).
% 0.55/0.72  thf('43', plain,
% 0.55/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X3 @ X4)
% 0.55/0.72          | (r2_hidden @ X3 @ X5)
% 0.55/0.72          | ~ (r1_tarski @ X4 @ X5))),
% 0.55/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.72  thf('44', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((r2_hidden @ X0 @ sk_B_1)
% 0.55/0.72          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['42', '43'])).
% 0.55/0.72  thf('45', plain,
% 0.55/0.72      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.55/0.72        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.55/0.72      inference('sup-', [status(thm)], ['41', '44'])).
% 0.55/0.72  thf('46', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.72  thf('47', plain,
% 0.55/0.72      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.55/0.72      inference('sup-', [status(thm)], ['45', '46'])).
% 0.55/0.72  thf('48', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.55/0.72      inference('clc', [status(thm)], ['40', '47'])).
% 0.55/0.72  thf('49', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.55/0.72      inference('clc', [status(thm)], ['26', '48'])).
% 0.55/0.72  thf('50', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.55/0.72  thf('51', plain,
% 0.55/0.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.55/0.72         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.55/0.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.55/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.72  thf('52', plain,
% 0.55/0.72      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.55/0.72      inference('sup-', [status(thm)], ['50', '51'])).
% 0.55/0.72  thf('53', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.55/0.72      inference('demod', [status(thm)], ['19', '49', '52'])).
% 0.55/0.72  thf(t12_funct_1, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.72       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.55/0.72         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.55/0.72  thf('54', plain,
% 0.55/0.72      (![X12 : $i, X13 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.55/0.72          | (r2_hidden @ (k1_funct_1 @ X13 @ X12) @ (k2_relat_1 @ X13))
% 0.55/0.72          | ~ (v1_funct_1 @ X13)
% 0.55/0.72          | ~ (v1_relat_1 @ X13))),
% 0.55/0.72      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.55/0.72  thf('55', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.55/0.72          | ~ (v1_relat_1 @ sk_C_1)
% 0.55/0.72          | ~ (v1_funct_1 @ sk_C_1)
% 0.55/0.72          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['53', '54'])).
% 0.55/0.72  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 0.55/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.72  thf('57', plain, ((v1_funct_1 @ sk_C_1)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('58', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.55/0.72          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.55/0.72      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.55/0.72  thf('59', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((r1_tarski @ sk_B_1 @ X0)
% 0.55/0.72          | (r2_hidden @ 
% 0.55/0.72             (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ X0 @ sk_B_1))) @ 
% 0.55/0.72             (k2_relat_1 @ sk_C_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['16', '58'])).
% 0.55/0.72  thf('60', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k2_relat_1 @ sk_C_1))
% 0.55/0.72          | (r1_tarski @ sk_B_1 @ X0)
% 0.55/0.72          | (r1_tarski @ sk_B_1 @ X0))),
% 0.55/0.72      inference('sup+', [status(thm)], ['13', '59'])).
% 0.55/0.72  thf('61', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((r1_tarski @ sk_B_1 @ X0)
% 0.55/0.72          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k2_relat_1 @ sk_C_1)))),
% 0.55/0.72      inference('simplify', [status(thm)], ['60'])).
% 0.55/0.72  thf('62', plain,
% 0.55/0.72      (![X4 : $i, X6 : $i]:
% 0.55/0.72         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.55/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.72  thf('63', plain,
% 0.55/0.72      (((r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_1))
% 0.55/0.72        | (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['61', '62'])).
% 0.55/0.72  thf('64', plain, ((r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_1))),
% 0.55/0.72      inference('simplify', [status(thm)], ['63'])).
% 0.55/0.72  thf('65', plain, (((sk_B_1) = (k2_relat_1 @ sk_C_1))),
% 0.55/0.72      inference('demod', [status(thm)], ['10', '64'])).
% 0.55/0.72  thf('66', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (sk_B_1))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('67', plain,
% 0.55/0.72      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.55/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.72  thf('68', plain, (((k2_relat_1 @ sk_C_1) != (sk_B_1))),
% 0.55/0.72      inference('demod', [status(thm)], ['66', '67'])).
% 0.55/0.72  thf('69', plain, ($false),
% 0.55/0.72      inference('simplify_reflect-', [status(thm)], ['65', '68'])).
% 0.55/0.72  
% 0.55/0.72  % SZS output end Refutation
% 0.55/0.72  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
