%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8qZu9vV16

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 244 expanded)
%              Number of leaves         :   39 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  700 (2867 expanded)
%              Number of equality atoms :   50 ( 176 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(t19_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                    & ( C
                      = ( k1_funct_1 @ B @ D ) ) ) )
       => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ( r1_tarski @ X11 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t19_funct_1])).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k2_relat_1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B )
      | ( X30
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_C @ sk_C_1 @ sk_B )
    = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
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

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('40',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['21','24'])).

thf('44',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','44','47'])).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( sk_C @ X10 @ X11 )
       != ( k1_funct_1 @ X10 @ X12 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X10 ) )
      | ( r1_tarski @ X11 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t19_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( ( sk_C @ sk_C_1 @ X1 )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( ( sk_C @ sk_C_1 @ X1 )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','53'])).

thf('55',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['20','25'])).

thf('56',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X30 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(eq_res,[status(thm)],['58'])).

thf('60',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','59'])).

thf('61',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['21','24'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8qZu9vV16
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 81 iterations in 0.073s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(sk_E_type, type, sk_E: $i > $i).
% 0.19/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.19/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.52  thf(t16_funct_2, conjecture,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.52       ( ( ![D:$i]:
% 0.19/0.52           ( ~( ( r2_hidden @ D @ B ) & 
% 0.19/0.52                ( ![E:$i]:
% 0.19/0.52                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.19/0.52                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.19/0.52         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.52          ( ( ![D:$i]:
% 0.19/0.52              ( ~( ( r2_hidden @ D @ B ) & 
% 0.19/0.52                   ( ![E:$i]:
% 0.19/0.52                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.19/0.52                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.19/0.52            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(cc2_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.52         ((v5_relat_1 @ X13 @ X15)
% 0.19/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.52  thf('2', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.19/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.52  thf(d19_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ B ) =>
% 0.19/0.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X6 : $i, X7 : $i]:
% 0.19/0.52         (~ (v5_relat_1 @ X6 @ X7)
% 0.19/0.52          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.19/0.52          | ~ (v1_relat_1 @ X6))),
% 0.19/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(cc2_relat_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X4 : $i, X5 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.19/0.52          | (v1_relat_1 @ X4)
% 0.19/0.52          | ~ (v1_relat_1 @ X5))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf(fc6_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.19/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.52  thf('9', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.52  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['4', '9'])).
% 0.19/0.52  thf(d10_xboole_0, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      (![X0 : $i, X2 : $i]:
% 0.19/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.19/0.52        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.52  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['4', '9'])).
% 0.19/0.52  thf(t19_funct_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.52       ( ( ![C:$i]:
% 0.19/0.52           ( ~( ( r2_hidden @ C @ A ) & 
% 0.19/0.52                ( ![D:$i]:
% 0.19/0.52                  ( ~( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.52                       ( ( C ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) =>
% 0.19/0.52         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X10 : $i, X11 : $i]:
% 0.19/0.52         ((r2_hidden @ (sk_C @ X10 @ X11) @ X11)
% 0.19/0.52          | (r1_tarski @ X11 @ (k2_relat_1 @ X10))
% 0.19/0.52          | ~ (v1_funct_1 @ X10)
% 0.19/0.52          | ~ (v1_relat_1 @ X10))),
% 0.19/0.52      inference('cnf', [status(esa)], [t19_funct_1])).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X0 : $i, X2 : $i]:
% 0.19/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X0)
% 0.19/0.52          | ~ (v1_funct_1 @ X0)
% 0.19/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.19/0.52          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.19/0.52          | ((k2_relat_1 @ X0) = (X1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.19/0.52        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.19/0.52        | ~ (v1_funct_1 @ sk_C_1)
% 0.19/0.52        | ~ (v1_relat_1 @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.19/0.52  thf('18', plain, ((v1_funct_1 @ sk_C_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.19/0.52        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.19/0.52  thf('21', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.52         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.19/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.52  thf('25', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['21', '24'])).
% 0.19/0.52  thf('26', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['20', '25'])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (![X30 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X30 @ sk_B)
% 0.19/0.52          | ((X30) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X30))))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (((sk_C @ sk_C_1 @ sk_B)
% 0.19/0.52         = (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ sk_C_1 @ sk_B))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.52  thf('29', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d1_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.19/0.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.19/0.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_1, axiom,
% 0.19/0.52    (![C:$i,B:$i,A:$i]:
% 0.19/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.19/0.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.52         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.19/0.52          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.19/0.52          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.19/0.52        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.52  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['4', '9'])).
% 0.19/0.52  thf(zf_stmt_2, axiom,
% 0.19/0.52    (![B:$i,A:$i]:
% 0.19/0.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.52       ( zip_tseitin_0 @ B @ A ) ))).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      (![X22 : $i, X23 : $i]:
% 0.19/0.52         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.52  thf('34', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.19/0.52      inference('sup+', [status(thm)], ['33', '34'])).
% 0.19/0.52  thf('36', plain,
% 0.19/0.52      (![X0 : $i, X2 : $i]:
% 0.19/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((k2_relat_1 @ sk_C_1) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['32', '37'])).
% 0.19/0.52  thf('39', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.19/0.52  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.19/0.52  thf(zf_stmt_5, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.19/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.19/0.52  thf('40', plain,
% 0.19/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.52         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.19/0.52          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.19/0.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.19/0.52        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.19/0.52        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['38', '41'])).
% 0.19/0.52  thf('43', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['21', '24'])).
% 0.19/0.52  thf('44', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.19/0.52  thf('45', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.52  thf('46', plain,
% 0.19/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.52         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.19/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.52  thf('47', plain,
% 0.19/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.52  thf('48', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.52      inference('demod', [status(thm)], ['31', '44', '47'])).
% 0.19/0.52  thf('49', plain,
% 0.19/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.52         (((sk_C @ X10 @ X11) != (k1_funct_1 @ X10 @ X12))
% 0.19/0.52          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X10))
% 0.19/0.52          | (r1_tarski @ X11 @ (k2_relat_1 @ X10))
% 0.19/0.52          | ~ (v1_funct_1 @ X10)
% 0.19/0.52          | ~ (v1_relat_1 @ X10))),
% 0.19/0.52      inference('cnf', [status(esa)], [t19_funct_1])).
% 0.19/0.52  thf('50', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.52          | ~ (v1_relat_1 @ sk_C_1)
% 0.19/0.52          | ~ (v1_funct_1 @ sk_C_1)
% 0.19/0.52          | (r1_tarski @ X1 @ (k2_relat_1 @ sk_C_1))
% 0.19/0.52          | ((sk_C @ sk_C_1 @ X1) != (k1_funct_1 @ sk_C_1 @ X0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.52  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.52  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('53', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.52          | (r1_tarski @ X1 @ (k2_relat_1 @ sk_C_1))
% 0.19/0.52          | ((sk_C @ sk_C_1 @ X1) != (k1_funct_1 @ sk_C_1 @ X0)))),
% 0.19/0.52      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.19/0.52  thf('54', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((sk_C @ sk_C_1 @ X0) != (sk_C @ sk_C_1 @ sk_B))
% 0.19/0.52          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.19/0.52          | ~ (r2_hidden @ (sk_E @ (sk_C @ sk_C_1 @ sk_B)) @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['28', '53'])).
% 0.19/0.52  thf('55', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['20', '25'])).
% 0.19/0.52  thf('56', plain,
% 0.19/0.52      (![X30 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X30 @ sk_B) | (r2_hidden @ (sk_E @ X30) @ sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('57', plain, ((r2_hidden @ (sk_E @ (sk_C @ sk_C_1 @ sk_B)) @ sk_A)),
% 0.19/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.52  thf('58', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((sk_C @ sk_C_1 @ X0) != (sk_C @ sk_C_1 @ sk_B))
% 0.19/0.52          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.19/0.52      inference('demod', [status(thm)], ['54', '57'])).
% 0.19/0.52  thf('59', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.19/0.52      inference('eq_res', [status(thm)], ['58'])).
% 0.19/0.52  thf('60', plain, (((sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.52      inference('demod', [status(thm)], ['12', '59'])).
% 0.19/0.52  thf('61', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['21', '24'])).
% 0.19/0.52  thf('62', plain, ($false),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
