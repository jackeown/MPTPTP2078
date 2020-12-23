%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zDVZ58AzWl

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:41 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 503 expanded)
%              Number of leaves         :   40 ( 167 expanded)
%              Depth                    :   20
%              Number of atoms          :  891 (6428 expanded)
%              Number of equality atoms :   48 ( 239 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['0','5'])).

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

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','32'])).

thf('34',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_A )
      | ~ ( r2_hidden @ X37 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('40',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('46',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('50',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['41','51'])).

thf('53',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    r2_hidden @ sk_E @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','53'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_E @ X0 ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ sk_E ) @ sk_E ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_E
        = ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ X1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_E
        = ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ X1 @ sk_E ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_E @ X0 ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('67',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_E ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ sk_E ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_A )
      | ~ ( r2_hidden @ X37 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ X0 @ k1_xboole_0 @ sk_E ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ sk_E ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ sk_E ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ X0 @ k1_xboole_0 @ sk_E ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_E != sk_E )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('77',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('79',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    $false ),
    inference(simplify,[status(thm)],['79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zDVZ58AzWl
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:21:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.65/1.83  % Solved by: fo/fo7.sh
% 1.65/1.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.83  % done 1127 iterations in 1.368s
% 1.65/1.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.65/1.83  % SZS output start Refutation
% 1.65/1.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.83  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.65/1.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.65/1.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.65/1.83  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.83  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.65/1.83  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.65/1.83  thf(sk_E_type, type, sk_E: $i).
% 1.65/1.83  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.65/1.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.65/1.83  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.83  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.65/1.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.65/1.83  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.83  thf(t115_funct_2, conjecture,
% 1.65/1.83    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.83     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.65/1.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.83       ( ![E:$i]:
% 1.65/1.83         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.65/1.83              ( ![F:$i]:
% 1.65/1.83                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 1.65/1.83                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.83        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.65/1.83            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.83          ( ![E:$i]:
% 1.65/1.83            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.65/1.83                 ( ![F:$i]:
% 1.65/1.83                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 1.65/1.83                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 1.65/1.83    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 1.65/1.83  thf('0', plain,
% 1.65/1.83      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('1', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(dt_k7_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.65/1.83  thf('2', plain,
% 1.65/1.83      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.65/1.83          | (m1_subset_1 @ (k7_relset_1 @ X19 @ X20 @ X18 @ X21) @ 
% 1.65/1.83             (k1_zfmisc_1 @ X20)))),
% 1.65/1.83      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.65/1.83  thf('3', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 1.65/1.83          (k1_zfmisc_1 @ sk_B))),
% 1.65/1.83      inference('sup-', [status(thm)], ['1', '2'])).
% 1.65/1.83  thf(l3_subset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.83       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.65/1.83  thf('4', plain,
% 1.65/1.83      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X1 @ X2)
% 1.65/1.83          | (r2_hidden @ X1 @ X3)
% 1.65/1.83          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 1.65/1.83      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.65/1.83  thf('5', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((r2_hidden @ X1 @ sk_B)
% 1.65/1.83          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['3', '4'])).
% 1.65/1.83  thf('6', plain, ((r2_hidden @ sk_E @ sk_B)),
% 1.65/1.83      inference('sup-', [status(thm)], ['0', '5'])).
% 1.65/1.83  thf(d1_funct_2, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.65/1.83           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.65/1.83             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.65/1.83         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.65/1.83             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_1, axiom,
% 1.65/1.83    (![B:$i,A:$i]:
% 1.65/1.83     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83       ( zip_tseitin_0 @ B @ A ) ))).
% 1.65/1.83  thf('7', plain,
% 1.65/1.83      (![X29 : $i, X30 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('8', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.65/1.83  thf(zf_stmt_3, axiom,
% 1.65/1.83    (![C:$i,B:$i,A:$i]:
% 1.65/1.83     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.65/1.83       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.65/1.83  thf(zf_stmt_5, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.65/1.83         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.65/1.83           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.65/1.83             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.65/1.83  thf('9', plain,
% 1.65/1.83      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.65/1.83         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.65/1.83          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.65/1.83          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('10', plain,
% 1.65/1.83      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 1.65/1.83        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['8', '9'])).
% 1.65/1.83  thf('11', plain,
% 1.65/1.83      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['7', '10'])).
% 1.65/1.83  thf('12', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('13', plain,
% 1.65/1.83      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.65/1.83         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.65/1.83          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.65/1.83          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('14', plain,
% 1.65/1.83      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 1.65/1.83        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['12', '13'])).
% 1.65/1.83  thf('15', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(redefinition_k1_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.65/1.83  thf('16', plain,
% 1.65/1.83      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.83         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 1.65/1.83          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.65/1.83  thf('17', plain,
% 1.65/1.83      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['15', '16'])).
% 1.65/1.83  thf('18', plain,
% 1.65/1.83      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.65/1.83      inference('demod', [status(thm)], ['14', '17'])).
% 1.65/1.83  thf('19', plain,
% 1.65/1.83      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['11', '18'])).
% 1.65/1.83  thf('20', plain,
% 1.65/1.83      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('21', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(redefinition_k7_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.65/1.83  thf('22', plain,
% 1.65/1.83      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.65/1.83          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.65/1.83  thf('23', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 1.65/1.83           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['21', '22'])).
% 1.65/1.83  thf('24', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 1.65/1.83      inference('demod', [status(thm)], ['20', '23'])).
% 1.65/1.83  thf(t143_relat_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( v1_relat_1 @ C ) =>
% 1.65/1.83       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.65/1.83         ( ?[D:$i]:
% 1.65/1.83           ( ( r2_hidden @ D @ B ) & 
% 1.65/1.83             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.65/1.83             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.65/1.83  thf('25', plain,
% 1.65/1.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 1.65/1.83          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ (k1_relat_1 @ X14))
% 1.65/1.83          | ~ (v1_relat_1 @ X14))),
% 1.65/1.83      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.65/1.83  thf('26', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ sk_D_1)
% 1.65/1.83        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['24', '25'])).
% 1.65/1.83  thf('27', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(cc2_relat_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( v1_relat_1 @ A ) =>
% 1.65/1.83       ( ![B:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.65/1.83  thf('28', plain,
% 1.65/1.83      (![X7 : $i, X8 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 1.65/1.83          | (v1_relat_1 @ X7)
% 1.65/1.83          | ~ (v1_relat_1 @ X8))),
% 1.65/1.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.83  thf('29', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['27', '28'])).
% 1.65/1.83  thf(fc6_relat_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.65/1.83  thf('30', plain,
% 1.65/1.83      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 1.65/1.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.83  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['29', '30'])).
% 1.65/1.83  thf('32', plain,
% 1.65/1.83      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 1.65/1.83      inference('demod', [status(thm)], ['26', '31'])).
% 1.65/1.83  thf('33', plain,
% 1.65/1.83      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 1.65/1.83        | ((sk_B) = (k1_xboole_0)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['19', '32'])).
% 1.65/1.83  thf('34', plain,
% 1.65/1.83      (![X37 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X37 @ sk_A)
% 1.65/1.83          | ~ (r2_hidden @ X37 @ sk_C)
% 1.65/1.83          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X37)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('35', plain,
% 1.65/1.83      ((((sk_B) = (k1_xboole_0))
% 1.65/1.83        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 1.65/1.83        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 1.65/1.83      inference('sup-', [status(thm)], ['33', '34'])).
% 1.65/1.83  thf('36', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 1.65/1.83      inference('demod', [status(thm)], ['20', '23'])).
% 1.65/1.83  thf('37', plain,
% 1.65/1.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 1.65/1.83          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 1.65/1.83          | ~ (v1_relat_1 @ X14))),
% 1.65/1.83      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.65/1.83  thf('38', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ sk_D_1)
% 1.65/1.83        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 1.65/1.83      inference('sup-', [status(thm)], ['36', '37'])).
% 1.65/1.83  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['29', '30'])).
% 1.65/1.83  thf('40', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 1.65/1.83      inference('demod', [status(thm)], ['38', '39'])).
% 1.65/1.83  thf('41', plain,
% 1.65/1.83      ((((sk_B) = (k1_xboole_0))
% 1.65/1.83        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 1.65/1.83      inference('demod', [status(thm)], ['35', '40'])).
% 1.65/1.83  thf('42', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 1.65/1.83      inference('demod', [status(thm)], ['20', '23'])).
% 1.65/1.83  thf('43', plain,
% 1.65/1.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 1.65/1.83          | (r2_hidden @ (k4_tarski @ (sk_D @ X14 @ X12 @ X13) @ X13) @ X14)
% 1.65/1.83          | ~ (v1_relat_1 @ X14))),
% 1.65/1.83      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.65/1.83  thf('44', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ sk_D_1)
% 1.65/1.83        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 1.65/1.83           sk_D_1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['42', '43'])).
% 1.65/1.83  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['29', '30'])).
% 1.65/1.83  thf('46', plain,
% 1.65/1.83      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['44', '45'])).
% 1.65/1.83  thf(t8_funct_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.65/1.83       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.65/1.83         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.65/1.83           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.65/1.83  thf('47', plain,
% 1.65/1.83      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.65/1.83         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 1.65/1.83          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 1.65/1.83          | ~ (v1_funct_1 @ X16)
% 1.65/1.83          | ~ (v1_relat_1 @ X16))),
% 1.65/1.83      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.65/1.83  thf('48', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ sk_D_1)
% 1.65/1.83        | ~ (v1_funct_1 @ sk_D_1)
% 1.65/1.83        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['46', '47'])).
% 1.65/1.83  thf('49', plain, ((v1_relat_1 @ sk_D_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['29', '30'])).
% 1.65/1.83  thf('50', plain, ((v1_funct_1 @ sk_D_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('51', plain,
% 1.65/1.83      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 1.65/1.83      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.65/1.83  thf('52', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 1.65/1.83      inference('demod', [status(thm)], ['41', '51'])).
% 1.65/1.83  thf('53', plain, (((sk_B) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['52'])).
% 1.65/1.83  thf('54', plain, ((r2_hidden @ sk_E @ k1_xboole_0)),
% 1.65/1.83      inference('demod', [status(thm)], ['6', '53'])).
% 1.65/1.83  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.65/1.83  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.65/1.83      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.65/1.83  thf(t3_subset, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.65/1.83  thf('56', plain,
% 1.65/1.83      (![X4 : $i, X6 : $i]:
% 1.65/1.83         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 1.65/1.83      inference('cnf', [status(esa)], [t3_subset])).
% 1.65/1.83  thf('57', plain,
% 1.65/1.83      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['55', '56'])).
% 1.65/1.83  thf('58', plain,
% 1.65/1.83      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X1 @ X2)
% 1.65/1.83          | (r2_hidden @ X1 @ X3)
% 1.65/1.83          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 1.65/1.83      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.65/1.83  thf('59', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['57', '58'])).
% 1.65/1.83  thf('60', plain, (![X0 : $i]: (r2_hidden @ sk_E @ X0)),
% 1.65/1.83      inference('sup-', [status(thm)], ['54', '59'])).
% 1.65/1.83  thf('61', plain,
% 1.65/1.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 1.65/1.83          | (r2_hidden @ (k4_tarski @ (sk_D @ X14 @ X12 @ X13) @ X13) @ X14)
% 1.65/1.83          | ~ (v1_relat_1 @ X14))),
% 1.65/1.83      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.65/1.83  thf('62', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ X1)
% 1.65/1.83          | (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0 @ sk_E) @ sk_E) @ X1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['60', '61'])).
% 1.65/1.83  thf('63', plain,
% 1.65/1.83      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.65/1.83         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 1.65/1.83          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 1.65/1.83          | ~ (v1_funct_1 @ X16)
% 1.65/1.83          | ~ (v1_relat_1 @ X16))),
% 1.65/1.83      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.65/1.83  thf('64', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ X0)
% 1.65/1.83          | ~ (v1_relat_1 @ X0)
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | ((sk_E) = (k1_funct_1 @ X0 @ (sk_D @ X0 @ X1 @ sk_E))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['62', '63'])).
% 1.65/1.83  thf('65', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (((sk_E) = (k1_funct_1 @ X0 @ (sk_D @ X0 @ X1 @ sk_E)))
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_relat_1 @ X0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['64'])).
% 1.65/1.83  thf('66', plain, (![X0 : $i]: (r2_hidden @ sk_E @ X0)),
% 1.65/1.83      inference('sup-', [status(thm)], ['54', '59'])).
% 1.65/1.83  thf('67', plain,
% 1.65/1.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 1.65/1.83          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 1.65/1.83          | ~ (v1_relat_1 @ X14))),
% 1.65/1.83      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.65/1.83  thf('68', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ X1) | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_E) @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['66', '67'])).
% 1.65/1.83  thf('69', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['57', '58'])).
% 1.65/1.83  thf('70', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ X0)
% 1.65/1.83          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ sk_E) @ X1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['68', '69'])).
% 1.65/1.83  thf('71', plain,
% 1.65/1.83      (![X37 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X37 @ sk_A)
% 1.65/1.83          | ~ (r2_hidden @ X37 @ sk_C)
% 1.65/1.83          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X37)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('72', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ X0)
% 1.65/1.83          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ X0 @ k1_xboole_0 @ sk_E)))
% 1.65/1.83          | ~ (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ sk_E) @ sk_C))),
% 1.65/1.83      inference('sup-', [status(thm)], ['70', '71'])).
% 1.65/1.83  thf('73', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ X0)
% 1.65/1.83          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ sk_E) @ X1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['68', '69'])).
% 1.65/1.83  thf('74', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ X0 @ k1_xboole_0 @ sk_E)))
% 1.65/1.83          | ~ (v1_relat_1 @ X0))),
% 1.65/1.83      inference('clc', [status(thm)], ['72', '73'])).
% 1.65/1.83  thf('75', plain,
% 1.65/1.83      ((((sk_E) != (sk_E))
% 1.65/1.83        | ~ (v1_relat_1 @ sk_D_1)
% 1.65/1.83        | ~ (v1_funct_1 @ sk_D_1)
% 1.65/1.83        | ~ (v1_relat_1 @ sk_D_1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['65', '74'])).
% 1.65/1.83  thf('76', plain, ((v1_relat_1 @ sk_D_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['29', '30'])).
% 1.65/1.83  thf('77', plain, ((v1_funct_1 @ sk_D_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('78', plain, ((v1_relat_1 @ sk_D_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['29', '30'])).
% 1.65/1.83  thf('79', plain, (((sk_E) != (sk_E))),
% 1.65/1.83      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 1.65/1.83  thf('80', plain, ($false), inference('simplify', [status(thm)], ['79'])).
% 1.65/1.83  
% 1.65/1.83  % SZS output end Refutation
% 1.65/1.83  
% 1.65/1.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
