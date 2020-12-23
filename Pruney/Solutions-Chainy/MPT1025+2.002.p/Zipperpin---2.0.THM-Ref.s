%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qtYyhDOCER

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:43 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 203 expanded)
%              Number of leaves         :   46 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  796 (2275 expanded)
%              Number of equality atoms :   42 (  87 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k9_relat_1 @ X28 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X28 @ X26 @ X27 ) @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('16',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k9_relat_1 @ X28 @ X26 ) )
      | ( r2_hidden @ ( sk_D @ X28 @ X26 @ X27 ) @ X26 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_C_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X47: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X47 ) )
      | ~ ( r2_hidden @ X47 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X47 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k9_relat_1 @ X28 @ X26 ) )
      | ( r2_hidden @ ( sk_D @ X28 @ X26 @ X27 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

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

thf('32',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('34',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X15: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('41',plain,(
    r2_hidden @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_tarski @ X10 @ X8 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('43',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( r2_hidden @ ( sk_B @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['35','49'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('54',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('61',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_A ),
    inference(demod,[status(thm)],['31','68'])).

thf('70',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qtYyhDOCER
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 425 iterations in 0.334s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.60/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.60/0.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.60/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.60/0.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.60/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.78  thf(sk_E_type, type, sk_E: $i).
% 0.60/0.78  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.60/0.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.78  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.78  thf(sk_B_type, type, sk_B: $i > $i).
% 0.60/0.78  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.60/0.78  thf(t116_funct_2, conjecture,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.78       ( ![E:$i]:
% 0.60/0.78         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.60/0.78              ( ![F:$i]:
% 0.60/0.78                ( ( m1_subset_1 @ F @ A ) =>
% 0.60/0.78                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.60/0.78                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.78    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.78            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.78          ( ![E:$i]:
% 0.60/0.78            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.60/0.78                 ( ![F:$i]:
% 0.60/0.78                   ( ( m1_subset_1 @ F @ A ) =>
% 0.60/0.78                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.60/0.78                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.78    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.60/0.78  thf('0', plain,
% 0.60/0.78      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_2))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('1', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(redefinition_k7_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.60/0.78  thf('2', plain,
% 0.60/0.78      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.60/0.78          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.60/0.78  thf('3', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.60/0.78           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.78  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.60/0.78      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.78  thf(t143_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ C ) =>
% 0.60/0.78       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.60/0.78         ( ?[D:$i]:
% 0.60/0.78           ( ( r2_hidden @ D @ B ) & 
% 0.60/0.78             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.60/0.78             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.60/0.78  thf('5', plain,
% 0.60/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.78         (~ (r2_hidden @ X27 @ (k9_relat_1 @ X28 @ X26))
% 0.60/0.78          | (r2_hidden @ (k4_tarski @ (sk_D @ X28 @ X26 @ X27) @ X27) @ X28)
% 0.60/0.78          | ~ (v1_relat_1 @ X28))),
% 0.60/0.78      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.78  thf('6', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D_1)
% 0.60/0.78        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.60/0.78           sk_D_1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.78  thf('7', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(cc2_relat_1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ A ) =>
% 0.60/0.78       ( ![B:$i]:
% 0.60/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.60/0.78  thf('8', plain,
% 0.60/0.78      (![X21 : $i, X22 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.60/0.78          | (v1_relat_1 @ X21)
% 0.60/0.78          | ~ (v1_relat_1 @ X22))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.60/0.78  thf('9', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.78  thf(fc6_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.60/0.78  thf('10', plain,
% 0.60/0.78      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.78  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.60/0.78      inference('demod', [status(thm)], ['9', '10'])).
% 0.60/0.78  thf('12', plain,
% 0.60/0.78      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.60/0.78        sk_D_1)),
% 0.60/0.78      inference('demod', [status(thm)], ['6', '11'])).
% 0.60/0.78  thf(t8_funct_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.60/0.78       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.60/0.78         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.60/0.78           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.60/0.78  thf('13', plain,
% 0.60/0.78      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.60/0.78         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 0.60/0.78          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 0.60/0.78          | ~ (v1_funct_1 @ X30)
% 0.60/0.78          | ~ (v1_relat_1 @ X30))),
% 0.60/0.78      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.60/0.78  thf('14', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D_1)
% 0.60/0.78        | ~ (v1_funct_1 @ sk_D_1)
% 0.60/0.78        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.78  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.60/0.78      inference('demod', [status(thm)], ['9', '10'])).
% 0.60/0.78  thf('16', plain, ((v1_funct_1 @ sk_D_1)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('17', plain,
% 0.60/0.78      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E)))),
% 0.60/0.78      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.60/0.78  thf('18', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.60/0.78      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.78  thf('19', plain,
% 0.60/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.78         (~ (r2_hidden @ X27 @ (k9_relat_1 @ X28 @ X26))
% 0.60/0.78          | (r2_hidden @ (sk_D @ X28 @ X26 @ X27) @ X26)
% 0.60/0.78          | ~ (v1_relat_1 @ X28))),
% 0.60/0.78      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.78  thf('20', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D_1)
% 0.60/0.78        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_C_2))),
% 0.60/0.78      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.78  thf('21', plain, ((v1_relat_1 @ sk_D_1)),
% 0.60/0.78      inference('demod', [status(thm)], ['9', '10'])).
% 0.60/0.78  thf('22', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_C_2)),
% 0.60/0.78      inference('demod', [status(thm)], ['20', '21'])).
% 0.60/0.78  thf('23', plain,
% 0.60/0.78      (![X47 : $i]:
% 0.60/0.78         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X47))
% 0.60/0.78          | ~ (r2_hidden @ X47 @ sk_C_2)
% 0.60/0.78          | ~ (m1_subset_1 @ X47 @ sk_A))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('24', plain,
% 0.60/0.78      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A)
% 0.60/0.78        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['22', '23'])).
% 0.60/0.78  thf('25', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.60/0.78      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.78  thf('26', plain,
% 0.60/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.78         (~ (r2_hidden @ X27 @ (k9_relat_1 @ X28 @ X26))
% 0.60/0.78          | (r2_hidden @ (sk_D @ X28 @ X26 @ X27) @ (k1_relat_1 @ X28))
% 0.60/0.78          | ~ (v1_relat_1 @ X28))),
% 0.60/0.78      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.78  thf('27', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D_1)
% 0.60/0.78        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.60/0.78  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.60/0.78      inference('demod', [status(thm)], ['9', '10'])).
% 0.60/0.78  thf('29', plain,
% 0.60/0.78      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.60/0.78      inference('demod', [status(thm)], ['27', '28'])).
% 0.60/0.78  thf(t1_subset, axiom,
% 0.60/0.78    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.60/0.78  thf('30', plain,
% 0.60/0.78      (![X16 : $i, X17 : $i]:
% 0.60/0.78         ((m1_subset_1 @ X16 @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 0.60/0.78      inference('cnf', [status(esa)], [t1_subset])).
% 0.60/0.78  thf('31', plain,
% 0.60/0.78      ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.78  thf(d1_funct_2, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_1, axiom,
% 0.60/0.78    (![B:$i,A:$i]:
% 0.60/0.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.78       ( zip_tseitin_0 @ B @ A ) ))).
% 0.60/0.78  thf('32', plain,
% 0.60/0.78      (![X39 : $i, X40 : $i]:
% 0.60/0.78         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.78  thf(t113_zfmisc_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.60/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.78  thf('33', plain,
% 0.60/0.78      (![X13 : $i, X14 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.60/0.78          | ((X14) != (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.60/0.78  thf('34', plain,
% 0.60/0.78      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['33'])).
% 0.60/0.78  thf('35', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.60/0.78      inference('sup+', [status(thm)], ['32', '34'])).
% 0.60/0.78  thf(d1_xboole_0, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.60/0.78  thf('36', plain,
% 0.60/0.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.60/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.60/0.78  thf('37', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(t2_subset, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ A @ B ) =>
% 0.60/0.78       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.60/0.78  thf('38', plain,
% 0.60/0.78      (![X18 : $i, X19 : $i]:
% 0.60/0.78         ((r2_hidden @ X18 @ X19)
% 0.60/0.78          | (v1_xboole_0 @ X19)
% 0.60/0.78          | ~ (m1_subset_1 @ X18 @ X19))),
% 0.60/0.78      inference('cnf', [status(esa)], [t2_subset])).
% 0.60/0.78  thf('39', plain,
% 0.60/0.78      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.60/0.78        | (r2_hidden @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['37', '38'])).
% 0.60/0.78  thf(fc1_subset_1, axiom,
% 0.60/0.78    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.60/0.78  thf('40', plain, (![X15 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.60/0.78  thf('41', plain,
% 0.60/0.78      ((r2_hidden @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.60/0.78      inference('clc', [status(thm)], ['39', '40'])).
% 0.60/0.78  thf(d1_zfmisc_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.60/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.60/0.78  thf('42', plain,
% 0.60/0.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.78         (~ (r2_hidden @ X10 @ X9)
% 0.60/0.78          | (r1_tarski @ X10 @ X8)
% 0.60/0.78          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.60/0.78      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.60/0.78  thf('43', plain,
% 0.60/0.78      (![X8 : $i, X10 : $i]:
% 0.60/0.78         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.60/0.78      inference('simplify', [status(thm)], ['42'])).
% 0.60/0.78  thf('44', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['41', '43'])).
% 0.60/0.78  thf(d3_tarski, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.78  thf('45', plain,
% 0.60/0.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.78         (~ (r2_hidden @ X3 @ X4)
% 0.60/0.78          | (r2_hidden @ X3 @ X5)
% 0.60/0.78          | ~ (r1_tarski @ X4 @ X5))),
% 0.60/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.78  thf('46', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.60/0.78          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['44', '45'])).
% 0.60/0.78  thf('47', plain,
% 0.60/0.78      (((v1_xboole_0 @ sk_D_1)
% 0.60/0.78        | (r2_hidden @ (sk_B @ sk_D_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['36', '46'])).
% 0.60/0.78  thf('48', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.60/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.60/0.78  thf('49', plain,
% 0.60/0.78      (((v1_xboole_0 @ sk_D_1)
% 0.60/0.78        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['47', '48'])).
% 0.60/0.78  thf('50', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.60/0.78          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 0.60/0.78          | (v1_xboole_0 @ sk_D_1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['35', '49'])).
% 0.60/0.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.60/0.78  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.78  thf('52', plain,
% 0.60/0.78      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D_1))),
% 0.60/0.78      inference('demod', [status(thm)], ['50', '51'])).
% 0.60/0.78  thf('53', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.60/0.78  thf(zf_stmt_3, axiom,
% 0.60/0.78    (![C:$i,B:$i,A:$i]:
% 0.60/0.78     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.60/0.78       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.60/0.78  thf(zf_stmt_5, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.60/0.78         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.78           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.78             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.78  thf('54', plain,
% 0.60/0.78      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.60/0.78         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.60/0.78          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.60/0.78          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.78  thf('55', plain,
% 0.60/0.78      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.60/0.78        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.60/0.78      inference('sup-', [status(thm)], ['53', '54'])).
% 0.60/0.78  thf('56', plain,
% 0.60/0.78      (((v1_xboole_0 @ sk_D_1) | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.60/0.78      inference('sup-', [status(thm)], ['52', '55'])).
% 0.60/0.78  thf('57', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('58', plain,
% 0.60/0.78      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.60/0.78         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.60/0.78          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.60/0.78          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.78  thf('59', plain,
% 0.60/0.78      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.60/0.78        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['57', '58'])).
% 0.60/0.78  thf('60', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.78  thf('61', plain,
% 0.60/0.78      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.78         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.60/0.78          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.78  thf('62', plain,
% 0.60/0.78      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.60/0.78  thf('63', plain,
% 0.60/0.78      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.60/0.78        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.60/0.78      inference('demod', [status(thm)], ['59', '62'])).
% 0.60/0.78  thf('64', plain,
% 0.60/0.78      (((v1_xboole_0 @ sk_D_1) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['56', '63'])).
% 0.60/0.78  thf('65', plain,
% 0.60/0.78      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.60/0.78        sk_D_1)),
% 0.60/0.78      inference('demod', [status(thm)], ['6', '11'])).
% 0.60/0.78  thf('66', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.60/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.60/0.78  thf('67', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.60/0.78      inference('sup-', [status(thm)], ['65', '66'])).
% 0.60/0.78  thf('68', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['64', '67'])).
% 0.60/0.78  thf('69', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A)),
% 0.60/0.78      inference('demod', [status(thm)], ['31', '68'])).
% 0.60/0.78  thf('70', plain,
% 0.60/0.78      (((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E)))),
% 0.60/0.78      inference('demod', [status(thm)], ['24', '69'])).
% 0.60/0.78  thf('71', plain, ($false),
% 0.60/0.78      inference('simplify_reflect-', [status(thm)], ['17', '70'])).
% 0.60/0.78  
% 0.60/0.78  % SZS output end Refutation
% 0.60/0.78  
% 0.60/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
