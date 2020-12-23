%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1bemAFKaOH

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:20 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 178 expanded)
%              Number of leaves         :   38 (  69 expanded)
%              Depth                    :   17
%              Number of atoms          :  715 (2348 expanded)
%              Number of equality atoms :   49 ( 164 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( sk_D @ X24 @ X22 ) @ X22 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X24 )
        = X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('6',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('11',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X35 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('23',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('35',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['20','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','36','39'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( X9
       != ( k1_funct_1 @ X8 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( k1_funct_1 @ X8 @ X7 ) ) @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['14','48'])).

thf('50',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('51',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B )
      | ( X35
        = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( sk_D @ sk_C @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_D @ X24 @ X22 ) ) @ X24 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X24 )
        = X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['3','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['2','56'])).

thf('58',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1bemAFKaOH
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 176 iterations in 0.141s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.40/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 0.40/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(t16_funct_2, conjecture,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59       ( ( ![D:$i]:
% 0.40/0.59           ( ~( ( r2_hidden @ D @ B ) & 
% 0.40/0.59                ( ![E:$i]:
% 0.40/0.59                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.40/0.59                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.40/0.59         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.59            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59          ( ( ![D:$i]:
% 0.40/0.59              ( ~( ( r2_hidden @ D @ B ) & 
% 0.40/0.59                   ( ![E:$i]:
% 0.40/0.59                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.40/0.59                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.40/0.59            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.59         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.40/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.59  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t23_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( ![D:$i]:
% 0.40/0.59           ( ~( ( r2_hidden @ D @ B ) & 
% 0.40/0.59                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.40/0.59         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_D @ X24 @ X22) @ X22)
% 0.40/0.59          | ((k2_relset_1 @ X23 @ X22 @ X24) = (X22))
% 0.40/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.40/0.59      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.40/0.59        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) = (sk_B))
% 0.40/0.59        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('11', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf('12', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X35 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X35 @ sk_B) | (r2_hidden @ (sk_E_1 @ X35) @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('14', plain, ((r2_hidden @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.59  thf('15', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d1_funct_2, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_1, axiom,
% 0.40/0.59    (![C:$i,B:$i,A:$i]:
% 0.40/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.40/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.59         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.40/0.59          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.40/0.59          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.40/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_4, axiom,
% 0.40/0.59    (![B:$i,A:$i]:
% 0.40/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.40/0.59  thf(zf_stmt_5, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.40/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.40/0.59         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.40/0.59          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.40/0.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_k2_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.59         ((m1_subset_1 @ (k2_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.40/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.59  thf(t3_subset, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X4 : $i, X5 : $i]:
% 0.40/0.59         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.40/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X27 : $i, X28 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.59  thf('29', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.40/0.59      inference('sup+', [status(thm)], ['28', '29'])).
% 0.40/0.59  thf(d10_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X0 : $i, X2 : $i]:
% 0.40/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k2_relat_1 @ sk_C) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['27', '32'])).
% 0.40/0.59  thf('34', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf('35', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('36', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['20', '35'])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.59         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.40/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.59  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['17', '36', '39'])).
% 0.40/0.59  thf(t8_funct_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.59       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.40/0.59         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.40/0.59           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X7 @ (k1_relat_1 @ X8))
% 0.40/0.59          | ((X9) != (k1_funct_1 @ X8 @ X7))
% 0.40/0.59          | (r2_hidden @ (k4_tarski @ X7 @ X9) @ X8)
% 0.40/0.59          | ~ (v1_funct_1 @ X8)
% 0.40/0.59          | ~ (v1_relat_1 @ X8))),
% 0.40/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X8)
% 0.40/0.59          | ~ (v1_funct_1 @ X8)
% 0.40/0.59          | (r2_hidden @ (k4_tarski @ X7 @ (k1_funct_1 @ X8 @ X7)) @ X8)
% 0.40/0.59          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X8)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['41'])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.59          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C)
% 0.40/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59          | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['40', '42'])).
% 0.40/0.59  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc1_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( v1_relat_1 @ C ) ))).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.59         ((v1_relat_1 @ X10)
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.59  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.59          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      ((r2_hidden @ 
% 0.40/0.59        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ 
% 0.40/0.59         (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)))) @ 
% 0.40/0.59        sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['14', '48'])).
% 0.40/0.59  thf('50', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X35 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X35 @ sk_B)
% 0.40/0.59          | ((X35) = (k1_funct_1 @ sk_C @ (sk_E_1 @ X35))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (((sk_D @ sk_C @ sk_B)
% 0.40/0.59         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      ((r2_hidden @ 
% 0.40/0.59        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ (sk_D @ sk_C @ sk_B)) @ 
% 0.40/0.59        sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['49', '52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 0.40/0.59         (~ (r2_hidden @ (k4_tarski @ X26 @ (sk_D @ X24 @ X22)) @ X24)
% 0.40/0.59          | ((k2_relset_1 @ X23 @ X22 @ X24) = (X22))
% 0.40/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.40/0.59      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.40/0.59          | ((k2_relset_1 @ X0 @ sk_B @ sk_C) = (sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['3', '55'])).
% 0.40/0.59  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['2', '56'])).
% 0.40/0.59  thf('58', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf('59', plain, ($false),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
