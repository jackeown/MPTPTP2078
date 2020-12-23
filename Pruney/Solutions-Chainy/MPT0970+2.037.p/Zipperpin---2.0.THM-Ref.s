%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ran1vxywOs

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:21 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  143 (3455 expanded)
%              Number of leaves         :   34 ( 985 expanded)
%              Depth                    :   31
%              Number of atoms          : 1035 (54386 expanded)
%              Number of equality atoms :  100 (4064 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_D @ X14 @ X12 ) @ X12 )
      | ( ( k2_relset_1 @ X13 @ X12 @ X14 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('7',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('9',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('12',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X25 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X2
       != ( k1_funct_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ) @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['9','12'])).

thf('39',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ sk_B )
      | ( X25
        = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( sk_D @ sk_C @ sk_B ) ) @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D @ X14 @ X12 ) ) @ X14 )
      | ( ( k2_relset_1 @ X13 @ X12 @ X14 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','43'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','44'])).

thf('46',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('47',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('60',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('61',plain,(
    ( k2_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('63',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('71',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('72',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_C @ k1_xboole_0 ) ) @ sk_A ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('74',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_C @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('76',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('77',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('79',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('80',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('83',plain,
    ( ( zip_tseitin_1 @ sk_C @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['87'])).

thf('89',plain,(
    zip_tseitin_1 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['83','88'])).

thf('90',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ k1_xboole_0 ) ) @ ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ k1_xboole_0 ) ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['74','95'])).

thf('97',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('98',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('99',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('100',plain,
    ( ( sk_D @ sk_C @ k1_xboole_0 )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ k1_xboole_0 ) ) @ ( sk_D @ sk_C @ k1_xboole_0 ) ) @ sk_C ),
    inference(demod,[status(thm)],['96','100'])).

thf('102',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D @ X14 @ X12 ) ) @ X14 )
      | ( ( k2_relset_1 @ X13 @ X12 @ X14 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) )
      | ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','103'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['66','104'])).

thf('106',plain,(
    ( k2_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ran1vxywOs
% 0.13/0.36  % Computer   : n011.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 16:29:57 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.05/1.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.26  % Solved by: fo/fo7.sh
% 1.05/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.26  % done 857 iterations in 0.786s
% 1.05/1.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.26  % SZS output start Refutation
% 1.05/1.26  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.05/1.26  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.05/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.26  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.26  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 1.05/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.26  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.05/1.26  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.05/1.26  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.26  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.05/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.26  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.05/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.26  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.05/1.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.26  thf(t16_funct_2, conjecture,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.26         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.26       ( ( ![D:$i]:
% 1.05/1.26           ( ~( ( r2_hidden @ D @ B ) & 
% 1.05/1.26                ( ![E:$i]:
% 1.05/1.26                  ( ~( ( r2_hidden @ E @ A ) & 
% 1.05/1.26                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.05/1.26         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 1.05/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.26    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.26        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.26            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.26          ( ( ![D:$i]:
% 1.05/1.26              ( ~( ( r2_hidden @ D @ B ) & 
% 1.05/1.26                   ( ![E:$i]:
% 1.05/1.26                     ( ~( ( r2_hidden @ E @ A ) & 
% 1.05/1.26                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.05/1.26            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 1.05/1.26    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 1.05/1.26  thf('0', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(redefinition_k2_relset_1, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.26       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.05/1.26  thf('1', plain,
% 1.05/1.26      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.05/1.26         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.05/1.26          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.05/1.26      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.05/1.26  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.05/1.26      inference('sup-', [status(thm)], ['0', '1'])).
% 1.05/1.26  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.05/1.26      inference('sup-', [status(thm)], ['0', '1'])).
% 1.05/1.26  thf('4', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('5', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(t23_relset_1, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.26       ( ( ![D:$i]:
% 1.05/1.26           ( ~( ( r2_hidden @ D @ B ) & 
% 1.05/1.26                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 1.05/1.26         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 1.05/1.26  thf('6', plain,
% 1.05/1.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.26         ((r2_hidden @ (sk_D @ X14 @ X12) @ X12)
% 1.05/1.26          | ((k2_relset_1 @ X13 @ X12 @ X14) = (X12))
% 1.05/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12))))),
% 1.05/1.26      inference('cnf', [status(esa)], [t23_relset_1])).
% 1.05/1.26  thf('7', plain,
% 1.05/1.26      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 1.05/1.26        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 1.05/1.26      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.26  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.05/1.26      inference('sup-', [status(thm)], ['0', '1'])).
% 1.05/1.26  thf('9', plain,
% 1.05/1.26      ((((k2_relat_1 @ sk_C) = (sk_B))
% 1.05/1.26        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 1.05/1.26      inference('demod', [status(thm)], ['7', '8'])).
% 1.05/1.26  thf('10', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('11', plain,
% 1.05/1.26      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.05/1.26      inference('sup-', [status(thm)], ['0', '1'])).
% 1.05/1.26  thf('12', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 1.05/1.26      inference('demod', [status(thm)], ['10', '11'])).
% 1.05/1.26  thf('13', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['9', '12'])).
% 1.05/1.26  thf('14', plain,
% 1.05/1.26      (![X25 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X25 @ sk_B) | (r2_hidden @ (sk_E_1 @ X25) @ sk_A))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('15', plain, ((r2_hidden @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ sk_A)),
% 1.05/1.26      inference('sup-', [status(thm)], ['13', '14'])).
% 1.05/1.26  thf(d1_funct_2, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.26       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.26           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.05/1.26             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.05/1.26         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.26           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.05/1.26             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.05/1.26  thf(zf_stmt_1, axiom,
% 1.05/1.26    (![B:$i,A:$i]:
% 1.05/1.26     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.26       ( zip_tseitin_0 @ B @ A ) ))).
% 1.05/1.26  thf('16', plain,
% 1.05/1.26      (![X17 : $i, X18 : $i]:
% 1.05/1.26         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.26  thf('17', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.05/1.26  thf(zf_stmt_3, axiom,
% 1.05/1.26    (![C:$i,B:$i,A:$i]:
% 1.05/1.26     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.05/1.26       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.05/1.26  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.05/1.26  thf(zf_stmt_5, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.26       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.05/1.26         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.26           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.05/1.26             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.05/1.26  thf('18', plain,
% 1.05/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.26         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.05/1.26          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.05/1.26          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.26  thf('19', plain,
% 1.05/1.26      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.05/1.26      inference('sup-', [status(thm)], ['17', '18'])).
% 1.05/1.26  thf('20', plain,
% 1.05/1.26      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.05/1.26      inference('sup-', [status(thm)], ['16', '19'])).
% 1.05/1.26  thf('21', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('22', plain,
% 1.05/1.26      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.05/1.26         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.05/1.26          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.05/1.26          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.05/1.26  thf('23', plain,
% 1.05/1.26      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.05/1.26        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['21', '22'])).
% 1.05/1.26  thf('24', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(redefinition_k1_relset_1, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.26       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.05/1.26  thf('25', plain,
% 1.05/1.26      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.05/1.26         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 1.05/1.26          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.05/1.26      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.05/1.26  thf('26', plain,
% 1.05/1.26      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.05/1.26      inference('sup-', [status(thm)], ['24', '25'])).
% 1.05/1.26  thf('27', plain,
% 1.05/1.26      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.05/1.26      inference('demod', [status(thm)], ['23', '26'])).
% 1.05/1.26  thf('28', plain,
% 1.05/1.26      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['20', '27'])).
% 1.05/1.26  thf(t8_funct_1, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.05/1.26       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.05/1.26         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.05/1.26           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.05/1.26  thf('29', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 1.05/1.26          | ((X2) != (k1_funct_1 @ X1 @ X0))
% 1.05/1.26          | (r2_hidden @ (k4_tarski @ X0 @ X2) @ X1)
% 1.05/1.26          | ~ (v1_funct_1 @ X1)
% 1.05/1.26          | ~ (v1_relat_1 @ X1))),
% 1.05/1.26      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.05/1.26  thf('30', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (v1_funct_1 @ X1)
% 1.05/1.26          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ X1 @ X0)) @ X1)
% 1.05/1.26          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ X1)))),
% 1.05/1.26      inference('simplify', [status(thm)], ['29'])).
% 1.05/1.26  thf('31', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X0 @ sk_A)
% 1.05/1.26          | ((sk_B) = (k1_xboole_0))
% 1.05/1.26          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C)
% 1.05/1.26          | ~ (v1_funct_1 @ sk_C)
% 1.05/1.26          | ~ (v1_relat_1 @ sk_C))),
% 1.05/1.26      inference('sup-', [status(thm)], ['28', '30'])).
% 1.05/1.26  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('33', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(cc1_relset_1, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.26       ( v1_relat_1 @ C ) ))).
% 1.05/1.26  thf('34', plain,
% 1.05/1.26      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.05/1.26         ((v1_relat_1 @ X3)
% 1.05/1.26          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.05/1.26      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.26  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.26      inference('sup-', [status(thm)], ['33', '34'])).
% 1.05/1.26  thf('36', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X0 @ sk_A)
% 1.05/1.26          | ((sk_B) = (k1_xboole_0))
% 1.05/1.26          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C))),
% 1.05/1.26      inference('demod', [status(thm)], ['31', '32', '35'])).
% 1.05/1.26  thf('37', plain,
% 1.05/1.26      (((r2_hidden @ 
% 1.05/1.26         (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ 
% 1.05/1.26          (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)))) @ 
% 1.05/1.26         sk_C)
% 1.05/1.26        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['15', '36'])).
% 1.05/1.26  thf('38', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['9', '12'])).
% 1.05/1.26  thf('39', plain,
% 1.05/1.26      (![X25 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X25 @ sk_B)
% 1.05/1.26          | ((X25) = (k1_funct_1 @ sk_C @ (sk_E_1 @ X25))))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('40', plain,
% 1.05/1.26      (((sk_D @ sk_C @ sk_B)
% 1.05/1.26         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['38', '39'])).
% 1.05/1.26  thf('41', plain,
% 1.05/1.26      (((r2_hidden @ 
% 1.05/1.26         (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ (sk_D @ sk_C @ sk_B)) @ 
% 1.05/1.26         sk_C)
% 1.05/1.26        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['37', '40'])).
% 1.05/1.26  thf('42', plain,
% 1.05/1.26      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 1.05/1.26         (~ (r2_hidden @ (k4_tarski @ X16 @ (sk_D @ X14 @ X12)) @ X14)
% 1.05/1.26          | ((k2_relset_1 @ X13 @ X12 @ X14) = (X12))
% 1.05/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12))))),
% 1.05/1.26      inference('cnf', [status(esa)], [t23_relset_1])).
% 1.05/1.26  thf('43', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (((sk_B) = (k1_xboole_0))
% 1.05/1.26          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.05/1.26          | ((k2_relset_1 @ X0 @ sk_B @ sk_C) = (sk_B)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['41', '42'])).
% 1.05/1.26  thf('44', plain,
% 1.05/1.26      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 1.05/1.26        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['4', '43'])).
% 1.05/1.26  thf('45', plain,
% 1.05/1.26      ((((k2_relat_1 @ sk_C) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.26      inference('sup+', [status(thm)], ['3', '44'])).
% 1.05/1.26  thf('46', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 1.05/1.26      inference('demod', [status(thm)], ['10', '11'])).
% 1.05/1.26  thf('47', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf('48', plain,
% 1.05/1.26      (((k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.05/1.26      inference('demod', [status(thm)], ['2', '47'])).
% 1.05/1.26  thf('49', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('50', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf('51', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.26  thf('52', plain,
% 1.05/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.26         (((X22) != (k1_xboole_0))
% 1.05/1.26          | ((X23) = (k1_xboole_0))
% 1.05/1.26          | ((X24) = (k1_xboole_0))
% 1.05/1.26          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 1.05/1.26          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.26  thf('53', plain,
% 1.05/1.26      (![X23 : $i, X24 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X24 @ 
% 1.05/1.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ k1_xboole_0)))
% 1.05/1.26          | ~ (v1_funct_2 @ X24 @ X23 @ k1_xboole_0)
% 1.05/1.26          | ((X24) = (k1_xboole_0))
% 1.05/1.26          | ((X23) = (k1_xboole_0)))),
% 1.05/1.26      inference('simplify', [status(thm)], ['52'])).
% 1.05/1.26  thf('54', plain,
% 1.05/1.26      ((((sk_A) = (k1_xboole_0))
% 1.05/1.26        | ((sk_C) = (k1_xboole_0))
% 1.05/1.26        | ~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['51', '53'])).
% 1.05/1.26  thf('55', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf('57', plain, ((v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 1.05/1.26      inference('demod', [status(thm)], ['55', '56'])).
% 1.05/1.26  thf('58', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['54', '57'])).
% 1.05/1.26  thf('59', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 1.05/1.26      inference('demod', [status(thm)], ['10', '11'])).
% 1.05/1.26  thf('60', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf('61', plain, (((k2_relat_1 @ sk_C) != (k1_xboole_0))),
% 1.05/1.26      inference('demod', [status(thm)], ['59', '60'])).
% 1.05/1.26  thf('62', plain,
% 1.05/1.26      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 1.05/1.26        | ((sk_A) = (k1_xboole_0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['58', '61'])).
% 1.05/1.26  thf(t60_relat_1, axiom,
% 1.05/1.26    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.05/1.26     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.05/1.26  thf('63', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.26      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.05/1.26  thf('64', plain,
% 1.05/1.26      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['62', '63'])).
% 1.05/1.26  thf('65', plain, (((sk_A) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['64'])).
% 1.05/1.26  thf('66', plain,
% 1.05/1.26      (((k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.05/1.26      inference('demod', [status(thm)], ['48', '65'])).
% 1.05/1.26  thf('67', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.26  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['64'])).
% 1.05/1.26  thf('69', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ 
% 1.05/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['67', '68'])).
% 1.05/1.26  thf('70', plain, ((r2_hidden @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ sk_A)),
% 1.05/1.26      inference('sup-', [status(thm)], ['13', '14'])).
% 1.05/1.26  thf('71', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf('72', plain,
% 1.05/1.26      ((r2_hidden @ (sk_E_1 @ (sk_D @ sk_C @ k1_xboole_0)) @ sk_A)),
% 1.05/1.26      inference('demod', [status(thm)], ['70', '71'])).
% 1.05/1.26  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['64'])).
% 1.05/1.26  thf('74', plain,
% 1.05/1.26      ((r2_hidden @ (sk_E_1 @ (sk_D @ sk_C @ k1_xboole_0)) @ k1_xboole_0)),
% 1.05/1.26      inference('demod', [status(thm)], ['72', '73'])).
% 1.05/1.26  thf('75', plain,
% 1.05/1.26      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.05/1.26      inference('demod', [status(thm)], ['23', '26'])).
% 1.05/1.26  thf('76', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf('77', plain,
% 1.05/1.26      ((~ (zip_tseitin_1 @ sk_C @ k1_xboole_0 @ sk_A)
% 1.05/1.26        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.05/1.26      inference('demod', [status(thm)], ['75', '76'])).
% 1.05/1.26  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['64'])).
% 1.05/1.26  thf('79', plain, (((sk_A) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['64'])).
% 1.05/1.26  thf('80', plain,
% 1.05/1.26      ((~ (zip_tseitin_1 @ sk_C @ k1_xboole_0 @ k1_xboole_0)
% 1.05/1.26        | ((k1_xboole_0) = (k1_relat_1 @ sk_C)))),
% 1.05/1.26      inference('demod', [status(thm)], ['77', '78', '79'])).
% 1.05/1.26  thf('81', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_C @ 
% 1.05/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['67', '68'])).
% 1.05/1.26  thf('82', plain,
% 1.05/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.26         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.05/1.26          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.05/1.26          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.26  thf('83', plain,
% 1.05/1.26      (((zip_tseitin_1 @ sk_C @ k1_xboole_0 @ k1_xboole_0)
% 1.05/1.26        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['81', '82'])).
% 1.05/1.26  thf('84', plain,
% 1.05/1.26      (![X17 : $i, X18 : $i]:
% 1.05/1.26         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.26  thf('85', plain,
% 1.05/1.26      (![X17 : $i, X18 : $i]:
% 1.05/1.26         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.26  thf('86', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 1.05/1.26      inference('simplify', [status(thm)], ['85'])).
% 1.05/1.26  thf('87', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.26         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 1.05/1.26      inference('sup+', [status(thm)], ['84', '86'])).
% 1.05/1.26  thf('88', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 1.05/1.26      inference('eq_fact', [status(thm)], ['87'])).
% 1.05/1.26  thf('89', plain, ((zip_tseitin_1 @ sk_C @ k1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('demod', [status(thm)], ['83', '88'])).
% 1.05/1.26  thf('90', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C))),
% 1.05/1.26      inference('demod', [status(thm)], ['80', '89'])).
% 1.05/1.26  thf('91', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (v1_funct_1 @ X1)
% 1.05/1.26          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ X1 @ X0)) @ X1)
% 1.05/1.26          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ X1)))),
% 1.05/1.26      inference('simplify', [status(thm)], ['29'])).
% 1.05/1.26  thf('92', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.05/1.26          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C)
% 1.05/1.26          | ~ (v1_funct_1 @ sk_C)
% 1.05/1.26          | ~ (v1_relat_1 @ sk_C))),
% 1.05/1.26      inference('sup-', [status(thm)], ['90', '91'])).
% 1.05/1.26  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.26      inference('sup-', [status(thm)], ['33', '34'])).
% 1.05/1.26  thf('95', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.05/1.26          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C))),
% 1.05/1.26      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.05/1.26  thf('96', plain,
% 1.05/1.26      ((r2_hidden @ 
% 1.05/1.26        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ k1_xboole_0)) @ 
% 1.05/1.26         (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ k1_xboole_0)))) @ 
% 1.05/1.26        sk_C)),
% 1.05/1.26      inference('sup-', [status(thm)], ['74', '95'])).
% 1.05/1.26  thf('97', plain,
% 1.05/1.26      (((sk_D @ sk_C @ sk_B)
% 1.05/1.26         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['38', '39'])).
% 1.05/1.26  thf('98', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf('99', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf('100', plain,
% 1.05/1.26      (((sk_D @ sk_C @ k1_xboole_0)
% 1.05/1.26         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ k1_xboole_0))))),
% 1.05/1.26      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.05/1.26  thf('101', plain,
% 1.05/1.26      ((r2_hidden @ 
% 1.05/1.26        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ k1_xboole_0)) @ 
% 1.05/1.26         (sk_D @ sk_C @ k1_xboole_0)) @ 
% 1.05/1.26        sk_C)),
% 1.05/1.26      inference('demod', [status(thm)], ['96', '100'])).
% 1.05/1.26  thf('102', plain,
% 1.05/1.26      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 1.05/1.26         (~ (r2_hidden @ (k4_tarski @ X16 @ (sk_D @ X14 @ X12)) @ X14)
% 1.05/1.26          | ((k2_relset_1 @ X13 @ X12 @ X14) = (X12))
% 1.05/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12))))),
% 1.05/1.26      inference('cnf', [status(esa)], [t23_relset_1])).
% 1.05/1.26  thf('103', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ sk_C @ 
% 1.05/1.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))
% 1.05/1.26          | ((k2_relset_1 @ X0 @ k1_xboole_0 @ sk_C) = (k1_xboole_0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['101', '102'])).
% 1.05/1.26  thf('104', plain,
% 1.05/1.26      (((k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C) = (k1_xboole_0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['69', '103'])).
% 1.05/1.26  thf('105', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.05/1.26      inference('sup+', [status(thm)], ['66', '104'])).
% 1.05/1.26  thf('106', plain, (((k2_relat_1 @ sk_C) != (k1_xboole_0))),
% 1.05/1.26      inference('demod', [status(thm)], ['59', '60'])).
% 1.05/1.26  thf('107', plain, ($false),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 1.05/1.26  
% 1.05/1.26  % SZS output end Refutation
% 1.05/1.26  
% 1.05/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
