%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rOixQoNaEl

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:50 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 202 expanded)
%              Number of leaves         :   46 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  778 (2257 expanded)
%              Number of equality atoms :   35 (  80 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k9_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X26 @ X24 @ X25 ) @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ X28 )
      | ( X29
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k9_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( sk_D @ X26 @ X24 @ X25 ) @ X24 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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
    ! [X45: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X45 ) )
      | ~ ( r2_hidden @ X45 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X45 @ sk_A ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k9_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( sk_D @ X26 @ X24 @ X25 ) @ ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

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
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X14: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
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

thf('50',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['35','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['34','50'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('60',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('61',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_A ),
    inference(demod,[status(thm)],['31','67'])).

thf('69',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','68'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rOixQoNaEl
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:43:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.62/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.80  % Solved by: fo/fo7.sh
% 0.62/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.80  % done 349 iterations in 0.319s
% 0.62/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.80  % SZS output start Refutation
% 0.62/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.62/0.80  thf(sk_E_type, type, sk_E: $i).
% 0.62/0.80  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.62/0.80  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.62/0.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.62/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.80  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.62/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.62/0.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.62/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.80  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.62/0.80  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.62/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.62/0.80  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.62/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.62/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.62/0.80  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.62/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.62/0.80  thf(t116_funct_2, conjecture,
% 0.62/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.80     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.62/0.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.62/0.80       ( ![E:$i]:
% 0.62/0.80         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.62/0.80              ( ![F:$i]:
% 0.62/0.80                ( ( m1_subset_1 @ F @ A ) =>
% 0.62/0.80                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.62/0.80                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.62/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.80        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.62/0.80            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.62/0.80          ( ![E:$i]:
% 0.62/0.80            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.62/0.80                 ( ![F:$i]:
% 0.62/0.80                   ( ( m1_subset_1 @ F @ A ) =>
% 0.62/0.80                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.62/0.80                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.62/0.80    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.62/0.80  thf('0', plain,
% 0.62/0.80      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_2))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('1', plain,
% 0.62/0.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(redefinition_k7_relset_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.80       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.62/0.80  thf('2', plain,
% 0.62/0.80      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.62/0.80         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.62/0.80          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.62/0.80      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.62/0.80  thf('3', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.62/0.80           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.62/0.80  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.62/0.80      inference('demod', [status(thm)], ['0', '3'])).
% 0.62/0.80  thf(t143_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ C ) =>
% 0.62/0.80       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.62/0.80         ( ?[D:$i]:
% 0.62/0.80           ( ( r2_hidden @ D @ B ) & 
% 0.62/0.80             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.62/0.80             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.62/0.80  thf('5', plain,
% 0.62/0.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X25 @ (k9_relat_1 @ X26 @ X24))
% 0.62/0.80          | (r2_hidden @ (k4_tarski @ (sk_D @ X26 @ X24 @ X25) @ X25) @ X26)
% 0.62/0.80          | ~ (v1_relat_1 @ X26))),
% 0.62/0.80      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.62/0.80  thf('6', plain,
% 0.62/0.80      ((~ (v1_relat_1 @ sk_D_1)
% 0.62/0.80        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.62/0.80           sk_D_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.62/0.80  thf('7', plain,
% 0.62/0.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(cc2_relat_1, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ A ) =>
% 0.62/0.80       ( ![B:$i]:
% 0.62/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.62/0.80  thf('8', plain,
% 0.62/0.80      (![X19 : $i, X20 : $i]:
% 0.62/0.80         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.62/0.80          | (v1_relat_1 @ X19)
% 0.62/0.80          | ~ (v1_relat_1 @ X20))),
% 0.62/0.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.62/0.80  thf('9', plain,
% 0.62/0.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.80  thf(fc6_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.62/0.80  thf('10', plain,
% 0.62/0.80      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.62/0.80  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.62/0.80      inference('demod', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf('12', plain,
% 0.62/0.80      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.62/0.80        sk_D_1)),
% 0.62/0.80      inference('demod', [status(thm)], ['6', '11'])).
% 0.62/0.80  thf(t8_funct_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.62/0.80       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.62/0.80         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.62/0.80           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.62/0.80  thf('13', plain,
% 0.62/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.62/0.80         (~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ X28)
% 0.62/0.80          | ((X29) = (k1_funct_1 @ X28 @ X27))
% 0.62/0.80          | ~ (v1_funct_1 @ X28)
% 0.62/0.80          | ~ (v1_relat_1 @ X28))),
% 0.62/0.80      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.62/0.80  thf('14', plain,
% 0.62/0.80      ((~ (v1_relat_1 @ sk_D_1)
% 0.62/0.80        | ~ (v1_funct_1 @ sk_D_1)
% 0.62/0.80        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E))))),
% 0.62/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.62/0.80  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.62/0.80      inference('demod', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf('16', plain, ((v1_funct_1 @ sk_D_1)),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('17', plain,
% 0.62/0.80      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E)))),
% 0.62/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.62/0.80  thf('18', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.62/0.80      inference('demod', [status(thm)], ['0', '3'])).
% 0.62/0.80  thf('19', plain,
% 0.62/0.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X25 @ (k9_relat_1 @ X26 @ X24))
% 0.62/0.80          | (r2_hidden @ (sk_D @ X26 @ X24 @ X25) @ X24)
% 0.62/0.80          | ~ (v1_relat_1 @ X26))),
% 0.62/0.80      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.62/0.80  thf('20', plain,
% 0.62/0.80      ((~ (v1_relat_1 @ sk_D_1)
% 0.62/0.80        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_C_2))),
% 0.62/0.80      inference('sup-', [status(thm)], ['18', '19'])).
% 0.62/0.80  thf('21', plain, ((v1_relat_1 @ sk_D_1)),
% 0.62/0.80      inference('demod', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf('22', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_C_2)),
% 0.62/0.80      inference('demod', [status(thm)], ['20', '21'])).
% 0.62/0.80  thf('23', plain,
% 0.62/0.80      (![X45 : $i]:
% 0.62/0.80         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X45))
% 0.62/0.80          | ~ (r2_hidden @ X45 @ sk_C_2)
% 0.62/0.80          | ~ (m1_subset_1 @ X45 @ sk_A))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('24', plain,
% 0.62/0.80      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A)
% 0.62/0.80        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E))))),
% 0.62/0.80      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.80  thf('25', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.62/0.80      inference('demod', [status(thm)], ['0', '3'])).
% 0.62/0.80  thf('26', plain,
% 0.62/0.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X25 @ (k9_relat_1 @ X26 @ X24))
% 0.62/0.80          | (r2_hidden @ (sk_D @ X26 @ X24 @ X25) @ (k1_relat_1 @ X26))
% 0.62/0.80          | ~ (v1_relat_1 @ X26))),
% 0.62/0.80      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.62/0.80  thf('27', plain,
% 0.62/0.80      ((~ (v1_relat_1 @ sk_D_1)
% 0.62/0.80        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['25', '26'])).
% 0.62/0.80  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.62/0.80      inference('demod', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf('29', plain,
% 0.62/0.80      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.62/0.80      inference('demod', [status(thm)], ['27', '28'])).
% 0.62/0.80  thf(t1_subset, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.62/0.80  thf('30', plain,
% 0.62/0.80      (![X15 : $i, X16 : $i]:
% 0.62/0.80         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.62/0.80      inference('cnf', [status(esa)], [t1_subset])).
% 0.62/0.80  thf('31', plain,
% 0.62/0.80      ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.80  thf(d1_funct_2, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.62/0.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.62/0.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.62/0.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.62/0.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.62/0.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.62/0.80  thf(zf_stmt_1, axiom,
% 0.62/0.80    (![B:$i,A:$i]:
% 0.62/0.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.62/0.80       ( zip_tseitin_0 @ B @ A ) ))).
% 0.62/0.80  thf('32', plain,
% 0.62/0.80      (![X37 : $i, X38 : $i]:
% 0.62/0.80         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.62/0.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.62/0.80  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.80  thf('34', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['32', '33'])).
% 0.62/0.80  thf(fc3_zfmisc_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.62/0.80  thf('35', plain,
% 0.62/0.80      (![X12 : $i, X13 : $i]:
% 0.62/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X12 @ X13)) | ~ (v1_xboole_0 @ X13))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.62/0.80  thf(d1_xboole_0, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.80  thf('36', plain,
% 0.62/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.62/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.80  thf('37', plain,
% 0.62/0.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(t2_subset, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( m1_subset_1 @ A @ B ) =>
% 0.62/0.80       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.62/0.80  thf('38', plain,
% 0.62/0.80      (![X17 : $i, X18 : $i]:
% 0.62/0.80         ((r2_hidden @ X17 @ X18)
% 0.62/0.80          | (v1_xboole_0 @ X18)
% 0.62/0.80          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.62/0.80      inference('cnf', [status(esa)], [t2_subset])).
% 0.62/0.80  thf('39', plain,
% 0.62/0.80      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.62/0.80        | (r2_hidden @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.62/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.62/0.80  thf(fc1_subset_1, axiom,
% 0.62/0.80    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.62/0.80  thf('40', plain, (![X14 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.62/0.80  thf('41', plain,
% 0.62/0.80      ((r2_hidden @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.80      inference('clc', [status(thm)], ['39', '40'])).
% 0.62/0.80  thf(d1_zfmisc_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.62/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.62/0.80  thf('42', plain,
% 0.62/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X10 @ X9)
% 0.62/0.80          | (r1_tarski @ X10 @ X8)
% 0.62/0.80          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.62/0.80  thf('43', plain,
% 0.62/0.80      (![X8 : $i, X10 : $i]:
% 0.62/0.80         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.62/0.80      inference('simplify', [status(thm)], ['42'])).
% 0.62/0.80  thf('44', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['41', '43'])).
% 0.62/0.80  thf(d3_tarski, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.62/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.62/0.80  thf('45', plain,
% 0.62/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X3 @ X4)
% 0.62/0.80          | (r2_hidden @ X3 @ X5)
% 0.62/0.80          | ~ (r1_tarski @ X4 @ X5))),
% 0.62/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.62/0.80  thf('46', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.62/0.80          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['44', '45'])).
% 0.62/0.80  thf('47', plain,
% 0.62/0.80      (((v1_xboole_0 @ sk_D_1)
% 0.62/0.80        | (r2_hidden @ (sk_B @ sk_D_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['36', '46'])).
% 0.62/0.80  thf('48', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.80  thf('49', plain,
% 0.62/0.80      (((v1_xboole_0 @ sk_D_1)
% 0.62/0.80        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.80  thf('50', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_D_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['35', '49'])).
% 0.62/0.80  thf('51', plain,
% 0.62/0.80      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['34', '50'])).
% 0.62/0.80  thf('52', plain,
% 0.62/0.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.62/0.80  thf(zf_stmt_3, axiom,
% 0.62/0.80    (![C:$i,B:$i,A:$i]:
% 0.62/0.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.62/0.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.62/0.80  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.62/0.80  thf(zf_stmt_5, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.62/0.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.62/0.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.62/0.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.62/0.80  thf('53', plain,
% 0.62/0.80      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.62/0.80         (~ (zip_tseitin_0 @ X42 @ X43)
% 0.62/0.80          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 0.62/0.80          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.62/0.80  thf('54', plain,
% 0.62/0.80      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.62/0.80        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.62/0.80      inference('sup-', [status(thm)], ['52', '53'])).
% 0.62/0.80  thf('55', plain,
% 0.62/0.80      (((v1_xboole_0 @ sk_D_1) | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.62/0.80      inference('sup-', [status(thm)], ['51', '54'])).
% 0.62/0.80  thf('56', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('57', plain,
% 0.62/0.80      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.62/0.80         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 0.62/0.80          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 0.62/0.80          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.62/0.80  thf('58', plain,
% 0.62/0.80      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.62/0.80        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['56', '57'])).
% 0.62/0.80  thf('59', plain,
% 0.62/0.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(redefinition_k1_relset_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.62/0.80  thf('60', plain,
% 0.62/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.62/0.80         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.62/0.80          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.62/0.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.62/0.80  thf('61', plain,
% 0.62/0.80      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['59', '60'])).
% 0.62/0.80  thf('62', plain,
% 0.62/0.80      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.62/0.80        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.62/0.80      inference('demod', [status(thm)], ['58', '61'])).
% 0.62/0.80  thf('63', plain,
% 0.62/0.80      (((v1_xboole_0 @ sk_D_1) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['55', '62'])).
% 0.62/0.80  thf('64', plain,
% 0.62/0.80      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.62/0.80        sk_D_1)),
% 0.62/0.80      inference('demod', [status(thm)], ['6', '11'])).
% 0.62/0.80  thf('65', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.80  thf('66', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.62/0.80      inference('sup-', [status(thm)], ['64', '65'])).
% 0.62/0.80  thf('67', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['63', '66'])).
% 0.62/0.80  thf('68', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A)),
% 0.62/0.80      inference('demod', [status(thm)], ['31', '67'])).
% 0.62/0.80  thf('69', plain,
% 0.62/0.80      (((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E)))),
% 0.62/0.80      inference('demod', [status(thm)], ['24', '68'])).
% 0.62/0.80  thf('70', plain, ($false),
% 0.62/0.80      inference('simplify_reflect-', [status(thm)], ['17', '69'])).
% 0.62/0.80  
% 0.62/0.80  % SZS output end Refutation
% 0.62/0.80  
% 0.62/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
