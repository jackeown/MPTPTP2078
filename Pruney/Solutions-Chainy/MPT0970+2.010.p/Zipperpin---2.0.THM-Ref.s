%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y53GN3dawl

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:18 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 224 expanded)
%              Number of leaves         :   38 (  84 expanded)
%              Depth                    :   19
%              Number of atoms          :  734 (2804 expanded)
%              Number of equality atoms :   58 ( 182 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

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

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ X7 )
      | ( r1_tarski @ X7 @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t19_funct_1])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k2_relat_1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X29 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('22',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_B )
      | ( X29
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( ( sk_C @ sk_C_1 @ sk_B )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ( sk_B != sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['29','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','44','47'])).

thf('49',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( sk_C @ X6 @ X7 )
       != ( k1_funct_1 @ X6 @ X8 ) )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) )
      | ( r1_tarski @ X7 @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    inference('sup-',[status(thm)],['5','6'])).

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
      | ( ( k2_relat_1 @ sk_C_1 )
        = sk_B )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['37','40'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = sk_B )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','56'])).

thf('58',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['37','40'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(eq_res,[status(thm)],['59'])).

thf('61',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','60'])).

thf('62',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['37','40'])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y53GN3dawl
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 115 iterations in 0.129s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.58  thf(sk_E_type, type, sk_E: $i > $i).
% 0.36/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(t16_funct_2, conjecture,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.58       ( ( ![D:$i]:
% 0.36/0.58           ( ~( ( r2_hidden @ D @ B ) & 
% 0.36/0.58                ( ![E:$i]:
% 0.36/0.58                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.36/0.58                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.36/0.58         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.58          ( ( ![D:$i]:
% 0.36/0.58              ( ~( ( r2_hidden @ D @ B ) & 
% 0.36/0.58                   ( ![E:$i]:
% 0.36/0.58                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.36/0.58                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.36/0.58            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(cc2_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.58         ((v5_relat_1 @ X12 @ X14)
% 0.36/0.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.36/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.58  thf('2', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf(d19_relat_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ B ) =>
% 0.36/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i]:
% 0.36/0.58         (~ (v5_relat_1 @ X4 @ X5)
% 0.36/0.58          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.36/0.58          | ~ (v1_relat_1 @ X4))),
% 0.36/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(cc1_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( v1_relat_1 @ C ) ))).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.58         ((v1_relat_1 @ X9)
% 0.36/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.36/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.58  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.58  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.36/0.58      inference('demod', [status(thm)], ['4', '7'])).
% 0.36/0.58  thf(d10_xboole_0, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (![X0 : $i, X2 : $i]:
% 0.36/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.36/0.58        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.58  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.36/0.58      inference('demod', [status(thm)], ['4', '7'])).
% 0.36/0.58  thf(t19_funct_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.58       ( ( ![C:$i]:
% 0.36/0.58           ( ~( ( r2_hidden @ C @ A ) & 
% 0.36/0.58                ( ![D:$i]:
% 0.36/0.58                  ( ~( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) & 
% 0.36/0.58                       ( ( C ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) =>
% 0.36/0.58         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (![X6 : $i, X7 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_C @ X6 @ X7) @ X7)
% 0.36/0.58          | (r1_tarski @ X7 @ (k2_relat_1 @ X6))
% 0.36/0.58          | ~ (v1_funct_1 @ X6)
% 0.36/0.58          | ~ (v1_relat_1 @ X6))),
% 0.36/0.58      inference('cnf', [status(esa)], [t19_funct_1])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      (![X0 : $i, X2 : $i]:
% 0.36/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.36/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.36/0.58          | ((k2_relat_1 @ X0) = (X1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.36/0.58        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.36/0.58        | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.58        | ~ (v1_relat_1 @ sk_C_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['11', '14'])).
% 0.36/0.59  thf('16', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.36/0.59        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (![X29 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X29 @ sk_B) | (r2_hidden @ (sk_E @ X29) @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.36/0.59        | (r2_hidden @ (sk_E @ (sk_C @ sk_C_1 @ sk_B)) @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.36/0.59        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      (![X29 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X29 @ sk_B)
% 0.36/0.59          | ((X29) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X29))))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.36/0.59        | ((sk_C @ sk_C_1 @ sk_B)
% 0.36/0.59            = (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ sk_C_1 @ sk_B)))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.59  thf('24', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(d1_funct_2, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_1, axiom,
% 0.36/0.59    (![C:$i,B:$i,A:$i]:
% 0.36/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.59         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.36/0.59          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.36/0.59          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.36/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_4, axiom,
% 0.36/0.59    (![B:$i,A:$i]:
% 0.36/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.59  thf(zf_stmt_5, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.36/0.59         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.36/0.59          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.36/0.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.36/0.59        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.59  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.36/0.59      inference('demod', [status(thm)], ['4', '7'])).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (![X21 : $i, X22 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.59  thf('32', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.59  thf('33', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.36/0.59      inference('sup+', [status(thm)], ['31', '32'])).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      (![X0 : $i, X2 : $i]:
% 0.36/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.59  thf('35', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k2_relat_1 @ sk_C_1) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['30', '35'])).
% 0.36/0.59  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('38', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.59         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.36/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.59  thf('41', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['37', '40'])).
% 0.36/0.59  thf('42', plain,
% 0.36/0.59      (![X0 : $i]: (((sk_B) != (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['36', '41'])).
% 0.36/0.59  thf('43', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.36/0.59      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.59  thf('44', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.36/0.59      inference('demod', [status(thm)], ['29', '43'])).
% 0.36/0.59  thf('45', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.59  thf('46', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.59         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.36/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.59  thf('47', plain,
% 0.36/0.59      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.59  thf('48', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['26', '44', '47'])).
% 0.36/0.59  thf('49', plain,
% 0.36/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.59         (((sk_C @ X6 @ X7) != (k1_funct_1 @ X6 @ X8))
% 0.36/0.59          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6))
% 0.36/0.59          | (r1_tarski @ X7 @ (k2_relat_1 @ X6))
% 0.36/0.59          | ~ (v1_funct_1 @ X6)
% 0.36/0.59          | ~ (v1_relat_1 @ X6))),
% 0.36/0.59      inference('cnf', [status(esa)], [t19_funct_1])).
% 0.36/0.59  thf('50', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.59          | ~ (v1_relat_1 @ sk_C_1)
% 0.36/0.59          | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.59          | (r1_tarski @ X1 @ (k2_relat_1 @ sk_C_1))
% 0.36/0.59          | ((sk_C @ sk_C_1 @ X1) != (k1_funct_1 @ sk_C_1 @ X0)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.59  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('53', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.59          | (r1_tarski @ X1 @ (k2_relat_1 @ sk_C_1))
% 0.36/0.59          | ((sk_C @ sk_C_1 @ X1) != (k1_funct_1 @ sk_C_1 @ X0)))),
% 0.36/0.59      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.36/0.59  thf('54', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((sk_C @ sk_C_1 @ X0) != (sk_C @ sk_C_1 @ sk_B))
% 0.36/0.59          | ((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.36/0.59          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.36/0.59          | ~ (r2_hidden @ (sk_E @ (sk_C @ sk_C_1 @ sk_B)) @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['23', '53'])).
% 0.36/0.59  thf('55', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['37', '40'])).
% 0.36/0.59  thf('56', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((sk_C @ sk_C_1 @ X0) != (sk_C @ sk_C_1 @ sk_B))
% 0.36/0.59          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.36/0.59          | ~ (r2_hidden @ (sk_E @ (sk_C @ sk_C_1 @ sk_B)) @ sk_A))),
% 0.36/0.59      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.36/0.59  thf('57', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.36/0.59          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.36/0.59          | ((sk_C @ sk_C_1 @ X0) != (sk_C @ sk_C_1 @ sk_B)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['20', '56'])).
% 0.36/0.59  thf('58', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['37', '40'])).
% 0.36/0.59  thf('59', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.36/0.59          | ((sk_C @ sk_C_1 @ X0) != (sk_C @ sk_C_1 @ sk_B)))),
% 0.36/0.59      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.36/0.59  thf('60', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('eq_res', [status(thm)], ['59'])).
% 0.36/0.59  thf('61', plain, (((sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['10', '60'])).
% 0.36/0.59  thf('62', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['37', '40'])).
% 0.36/0.59  thf('63', plain, ($false),
% 0.36/0.59      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
