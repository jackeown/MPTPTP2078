%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jd8TvFhtr3

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:18 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 310 expanded)
%              Number of leaves         :   43 ( 111 expanded)
%              Depth                    :   26
%              Number of atoms          :  818 (3547 expanded)
%              Number of equality atoms :   45 ( 203 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('2',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_B_1 )
      | ( X33
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_B_1 )
      | ( r2_hidden @ ( sk_E @ X33 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
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

thf('8',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['32','47'])).

thf('49',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['20','48'])).

thf('50',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['13','49'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X11 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('54',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['6','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ X0 ) @ X0 )
      | ( X0 = sk_B_1 )
      | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['64'])).

thf('66',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('68',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('71',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('73',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_C_2 ) )
    | ( ( k2_relat_1 @ sk_C_2 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['65','68'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['66','67'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jd8TvFhtr3
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 408 iterations in 0.532s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.75/0.98  thf(sk_E_type, type, sk_E: $i > $i).
% 0.75/0.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.75/0.98  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.75/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.98  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.75/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i > $i).
% 0.75/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.75/0.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.75/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/0.98  thf(t2_tarski, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.75/0.98       ( ( A ) = ( B ) ) ))).
% 0.75/0.98  thf('0', plain,
% 0.75/0.98      (![X7 : $i, X8 : $i]:
% 0.75/0.98         (((X8) = (X7))
% 0.75/0.98          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 0.75/0.98          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X8))),
% 0.75/0.98      inference('cnf', [status(esa)], [t2_tarski])).
% 0.75/0.98  thf(d3_tarski, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( r1_tarski @ A @ B ) <=>
% 0.75/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.75/0.98  thf('1', plain,
% 0.75/0.98      (![X4 : $i, X6 : $i]:
% 0.75/0.98         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf(t16_funct_2, conjecture,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.98       ( ( ![D:$i]:
% 0.75/0.98           ( ~( ( r2_hidden @ D @ B ) & 
% 0.75/0.98                ( ![E:$i]:
% 0.75/0.98                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.75/0.98                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.75/0.98         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.98        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.98            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.98          ( ( ![D:$i]:
% 0.75/0.98              ( ~( ( r2_hidden @ D @ B ) & 
% 0.75/0.98                   ( ![E:$i]:
% 0.75/0.98                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.75/0.98                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.75/0.98            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      (![X33 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X33 @ sk_B_1)
% 0.75/0.98          | ((X33) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X33))))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r1_tarski @ sk_B_1 @ X0)
% 0.75/0.98          | ((sk_C @ X0 @ sk_B_1)
% 0.75/0.98              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B_1)))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.98  thf('4', plain,
% 0.75/0.98      (![X4 : $i, X6 : $i]:
% 0.75/0.98         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf('5', plain,
% 0.75/0.98      (![X33 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X33 @ sk_B_1) | (r2_hidden @ (sk_E @ X33) @ sk_A))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r1_tarski @ sk_B_1 @ X0)
% 0.75/0.98          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B_1)) @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.98  thf('7', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(d1_funct_2, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_1, axiom,
% 0.75/0.98    (![C:$i,B:$i,A:$i]:
% 0.75/0.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/0.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.75/0.98         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.75/0.98          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.75/0.98          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.75/0.98        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.98  thf('10', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.98  thf('11', plain,
% 0.75/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.98         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.75/0.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.75/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.98  thf('12', plain,
% 0.75/0.98      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.75/0.98      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.75/0.98        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('demod', [status(thm)], ['9', '12'])).
% 0.75/0.98  thf(zf_stmt_2, axiom,
% 0.75/0.98    (![B:$i,A:$i]:
% 0.75/0.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.98       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/0.98  thf('14', plain,
% 0.75/0.98      (![X25 : $i, X26 : $i]:
% 0.75/0.98         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.98  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.75/0.98  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.98  thf('16', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['14', '15'])).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/0.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.75/0.98  thf(zf_stmt_5, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.75/0.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.75/0.98         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.75/0.98          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.75/0.98          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.75/0.98        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['17', '18'])).
% 0.75/0.98  thf('20', plain,
% 0.75/0.98      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['16', '19'])).
% 0.75/0.98  thf('21', plain,
% 0.75/0.98      (![X7 : $i, X8 : $i]:
% 0.75/0.98         (((X8) = (X7))
% 0.75/0.98          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 0.75/0.98          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X8))),
% 0.75/0.98      inference('cnf', [status(esa)], [t2_tarski])).
% 0.75/0.98  thf(d1_xboole_0, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.98  thf('23', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 0.75/0.98          | ((X1) = (X0))
% 0.75/0.98          | ~ (v1_xboole_0 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.98  thf('24', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.98  thf('25', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['23', '24'])).
% 0.75/0.98  thf('26', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) != (sk_B_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((X0) != (sk_B_1))
% 0.75/0.98          | ~ (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.98  thf('28', plain,
% 0.75/0.98      ((~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2))
% 0.75/0.98        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.75/0.98      inference('simplify', [status(thm)], ['27'])).
% 0.75/0.98  thf('29', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(redefinition_k2_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.98         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.75/0.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.75/0.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.98  thf('31', plain,
% 0.75/0.98      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.75/0.98      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.98  thf('32', plain,
% 0.75/0.98      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['28', '31'])).
% 0.75/0.98  thf('33', plain,
% 0.75/0.98      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.75/0.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(cc2_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.75/0.98         ((v5_relat_1 @ X16 @ X18)
% 0.75/0.98          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.75/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.98  thf('36', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['34', '35'])).
% 0.75/0.98  thf(d19_relat_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ B ) =>
% 0.75/0.98       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.75/0.98  thf('37', plain,
% 0.75/0.98      (![X9 : $i, X10 : $i]:
% 0.75/0.98         (~ (v5_relat_1 @ X9 @ X10)
% 0.75/0.98          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.75/0.98          | ~ (v1_relat_1 @ X9))),
% 0.75/0.98      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.75/0.98  thf('38', plain,
% 0.75/0.98      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(cc1_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( v1_relat_1 @ C ) ))).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.98         ((v1_relat_1 @ X13)
% 0.75/0.98          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.75/0.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.98  thf('41', plain, ((v1_relat_1 @ sk_C_2)),
% 0.75/0.98      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.98  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.75/0.98      inference('demod', [status(thm)], ['38', '41'])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X3 @ X4)
% 0.75/0.98          | (r2_hidden @ X3 @ X5)
% 0.75/0.98          | ~ (r1_tarski @ X4 @ X5))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf('44', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r2_hidden @ X0 @ sk_B_1)
% 0.75/0.98          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['42', '43'])).
% 0.75/0.98  thf('45', plain,
% 0.75/0.98      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))
% 0.75/0.98        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_2)) @ sk_B_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['33', '44'])).
% 0.75/0.98  thf('46', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.98  thf('47', plain,
% 0.75/0.98      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.98  thf('48', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.75/0.98      inference('clc', [status(thm)], ['32', '47'])).
% 0.75/0.98  thf('49', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 0.75/0.98      inference('clc', [status(thm)], ['20', '48'])).
% 0.75/0.98  thf('50', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.75/0.98      inference('demod', [status(thm)], ['13', '49'])).
% 0.75/0.98  thf(t12_funct_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.75/0.98       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.75/0.98         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.75/0.98  thf('51', plain,
% 0.75/0.98      (![X11 : $i, X12 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.75/0.98          | (r2_hidden @ (k1_funct_1 @ X12 @ X11) @ (k2_relat_1 @ X12))
% 0.75/0.98          | ~ (v1_funct_1 @ X12)
% 0.75/0.98          | ~ (v1_relat_1 @ X12))),
% 0.75/0.98      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X0 @ sk_A)
% 0.75/0.98          | ~ (v1_relat_1 @ sk_C_2)
% 0.75/0.98          | ~ (v1_funct_1 @ sk_C_2)
% 0.75/0.98          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/0.98  thf('53', plain, ((v1_relat_1 @ sk_C_2)),
% 0.75/0.98      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.98  thf('54', plain, ((v1_funct_1 @ sk_C_2)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('55', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X0 @ sk_A)
% 0.75/0.98          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.75/0.98  thf('56', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r1_tarski @ sk_B_1 @ X0)
% 0.75/0.98          | (r2_hidden @ 
% 0.75/0.98             (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B_1))) @ 
% 0.75/0.98             (k2_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['6', '55'])).
% 0.75/0.98  thf('57', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k2_relat_1 @ sk_C_2))
% 0.75/0.98          | (r1_tarski @ sk_B_1 @ X0)
% 0.75/0.98          | (r1_tarski @ sk_B_1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['3', '56'])).
% 0.75/0.98  thf('58', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r1_tarski @ sk_B_1 @ X0)
% 0.75/0.98          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k2_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['57'])).
% 0.75/0.98  thf('59', plain,
% 0.75/0.98      (![X4 : $i, X6 : $i]:
% 0.75/0.98         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf('60', plain,
% 0.75/0.98      (((r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_2))
% 0.75/0.98        | (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['58', '59'])).
% 0.75/0.98  thf('61', plain, ((r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_2))),
% 0.75/0.98      inference('simplify', [status(thm)], ['60'])).
% 0.75/0.98  thf('62', plain,
% 0.75/0.98      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X3 @ X4)
% 0.75/0.98          | (r2_hidden @ X3 @ X5)
% 0.75/0.98          | ~ (r1_tarski @ X4 @ X5))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf('63', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2))
% 0.75/0.98          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['61', '62'])).
% 0.75/0.98  thf('64', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r2_hidden @ (sk_C_1 @ sk_B_1 @ X0) @ X0)
% 0.75/0.98          | ((X0) = (sk_B_1))
% 0.75/0.98          | (r2_hidden @ (sk_C_1 @ sk_B_1 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['0', '63'])).
% 0.75/0.98  thf('65', plain,
% 0.75/0.98      ((((k2_relat_1 @ sk_C_2) = (sk_B_1))
% 0.75/0.98        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ (k2_relat_1 @ sk_C_2)) @ 
% 0.75/0.98           (k2_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('eq_fact', [status(thm)], ['64'])).
% 0.75/0.98  thf('66', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) != (sk_B_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('67', plain,
% 0.75/0.98      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.75/0.98      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.98  thf('68', plain, (((k2_relat_1 @ sk_C_2) != (sk_B_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['66', '67'])).
% 0.75/0.98  thf('69', plain,
% 0.75/0.98      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ (k2_relat_1 @ sk_C_2)) @ 
% 0.75/0.98        (k2_relat_1 @ sk_C_2))),
% 0.75/0.98      inference('simplify_reflect-', [status(thm)], ['65', '68'])).
% 0.75/0.98  thf('70', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r2_hidden @ X0 @ sk_B_1)
% 0.75/0.98          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['42', '43'])).
% 0.75/0.98  thf('71', plain,
% 0.75/0.98      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ (k2_relat_1 @ sk_C_2)) @ sk_B_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['69', '70'])).
% 0.75/0.98  thf('72', plain,
% 0.75/0.98      (![X7 : $i, X8 : $i]:
% 0.75/0.98         (((X8) = (X7))
% 0.75/0.98          | ~ (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 0.75/0.98          | ~ (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X8))),
% 0.75/0.98      inference('cnf', [status(esa)], [t2_tarski])).
% 0.75/0.98  thf('73', plain,
% 0.75/0.98      ((~ (r2_hidden @ (sk_C_1 @ sk_B_1 @ (k2_relat_1 @ sk_C_2)) @ 
% 0.75/0.98           (k2_relat_1 @ sk_C_2))
% 0.75/0.98        | ((k2_relat_1 @ sk_C_2) = (sk_B_1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['71', '72'])).
% 0.75/0.98  thf('74', plain,
% 0.75/0.98      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ (k2_relat_1 @ sk_C_2)) @ 
% 0.75/0.98        (k2_relat_1 @ sk_C_2))),
% 0.75/0.98      inference('simplify_reflect-', [status(thm)], ['65', '68'])).
% 0.75/0.98  thf('75', plain, (((k2_relat_1 @ sk_C_2) = (sk_B_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['73', '74'])).
% 0.75/0.98  thf('76', plain, (((k2_relat_1 @ sk_C_2) != (sk_B_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['66', '67'])).
% 0.75/0.98  thf('77', plain, ($false),
% 0.75/0.98      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.81/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
