%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AW6SoZORPq

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:34 EST 2020

% Result     : Theorem 3.81s
% Output     : Refutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 624 expanded)
%              Number of leaves         :   39 ( 203 expanded)
%              Depth                    :   25
%              Number of atoms          : 1142 (8791 expanded)
%              Number of equality atoms :   80 ( 361 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

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

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('26',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['45','54'])).

thf('56',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('76',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['74','79'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('81',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['74','79'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','85','86','87'])).

thf('89',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('92',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['89','92','93'])).

thf('95',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X36: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X36 )
        = ( k1_funct_1 @ sk_D @ X36 ) )
      | ~ ( r2_hidden @ X36 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['97'])).

thf('99',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( ( k1_funct_1 @ X14 @ ( sk_C_1 @ X13 @ X14 ) )
       != ( k1_funct_1 @ X13 @ ( sk_C_1 @ X13 @ X14 ) ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('100',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('102',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['74','79'])).

thf('104',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['45','54'])).

thf('105',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['90','91'])).

thf('107',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['100','101','102','103','104','105','106'])).

thf('108',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('111',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AW6SoZORPq
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.81/4.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.81/4.06  % Solved by: fo/fo7.sh
% 3.81/4.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.81/4.06  % done 2232 iterations in 3.604s
% 3.81/4.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.81/4.06  % SZS output start Refutation
% 3.81/4.06  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.81/4.06  thf(sk_D_type, type, sk_D: $i).
% 3.81/4.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.81/4.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.81/4.06  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.81/4.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.81/4.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.81/4.06  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.81/4.06  thf(sk_A_type, type, sk_A: $i).
% 3.81/4.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.81/4.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.81/4.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.81/4.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.81/4.06  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.81/4.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.81/4.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.81/4.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.81/4.06  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.81/4.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.81/4.06  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.81/4.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.81/4.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.81/4.06  thf(t18_funct_2, conjecture,
% 3.81/4.06    (![A:$i,B:$i,C:$i]:
% 3.81/4.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.81/4.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.81/4.06       ( ![D:$i]:
% 3.81/4.06         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.81/4.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.81/4.06           ( ( ![E:$i]:
% 3.81/4.06               ( ( r2_hidden @ E @ A ) =>
% 3.81/4.06                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.81/4.06             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.81/4.06  thf(zf_stmt_0, negated_conjecture,
% 3.81/4.06    (~( ![A:$i,B:$i,C:$i]:
% 3.81/4.06        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.81/4.06            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.81/4.06          ( ![D:$i]:
% 3.81/4.06            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.81/4.06                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.81/4.06              ( ( ![E:$i]:
% 3.81/4.06                  ( ( r2_hidden @ E @ A ) =>
% 3.81/4.06                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.81/4.06                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.81/4.06    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 3.81/4.06  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('1', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf(redefinition_r2_relset_1, axiom,
% 3.81/4.06    (![A:$i,B:$i,C:$i,D:$i]:
% 3.81/4.06     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.81/4.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.81/4.06       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.81/4.06  thf('2', plain,
% 3.81/4.06      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.81/4.06         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.81/4.06          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.81/4.06          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 3.81/4.06          | ((X24) != (X27)))),
% 3.81/4.06      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.81/4.06  thf('3', plain,
% 3.81/4.06      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.81/4.06         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 3.81/4.06          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.81/4.06      inference('simplify', [status(thm)], ['2'])).
% 3.81/4.06  thf('4', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 3.81/4.06      inference('sup-', [status(thm)], ['1', '3'])).
% 3.81/4.06  thf(d1_funct_2, axiom,
% 3.81/4.06    (![A:$i,B:$i,C:$i]:
% 3.81/4.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.81/4.06       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.81/4.06           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.81/4.06             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.81/4.06         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.81/4.06           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.81/4.06             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.81/4.06  thf(zf_stmt_1, axiom,
% 3.81/4.06    (![B:$i,A:$i]:
% 3.81/4.06     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.81/4.06       ( zip_tseitin_0 @ B @ A ) ))).
% 3.81/4.06  thf('5', plain,
% 3.81/4.06      (![X28 : $i, X29 : $i]:
% 3.81/4.06         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.81/4.06  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.81/4.06  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.81/4.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.81/4.06  thf('7', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.81/4.06      inference('sup+', [status(thm)], ['5', '6'])).
% 3.81/4.06  thf(d10_xboole_0, axiom,
% 3.81/4.06    (![A:$i,B:$i]:
% 3.81/4.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.81/4.06  thf('8', plain,
% 3.81/4.06      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 3.81/4.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.81/4.06  thf('9', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 3.81/4.06      inference('simplify', [status(thm)], ['8'])).
% 3.81/4.06  thf(t3_subset, axiom,
% 3.81/4.06    (![A:$i,B:$i]:
% 3.81/4.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.81/4.06  thf('10', plain,
% 3.81/4.06      (![X10 : $i, X12 : $i]:
% 3.81/4.06         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 3.81/4.06      inference('cnf', [status(esa)], [t3_subset])).
% 3.81/4.06  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.81/4.06      inference('sup-', [status(thm)], ['9', '10'])).
% 3.81/4.06  thf(cc4_relset_1, axiom,
% 3.81/4.06    (![A:$i,B:$i]:
% 3.81/4.06     ( ( v1_xboole_0 @ A ) =>
% 3.81/4.06       ( ![C:$i]:
% 3.81/4.06         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 3.81/4.06           ( v1_xboole_0 @ C ) ) ) ))).
% 3.81/4.06  thf('12', plain,
% 3.81/4.06      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.81/4.06         (~ (v1_xboole_0 @ X18)
% 3.81/4.06          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 3.81/4.06          | (v1_xboole_0 @ X19))),
% 3.81/4.06      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.81/4.06  thf('13', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]:
% 3.81/4.06         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.81/4.06      inference('sup-', [status(thm)], ['11', '12'])).
% 3.81/4.06  thf(d3_tarski, axiom,
% 3.81/4.06    (![A:$i,B:$i]:
% 3.81/4.06     ( ( r1_tarski @ A @ B ) <=>
% 3.81/4.06       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.81/4.06  thf('14', plain,
% 3.81/4.06      (![X4 : $i, X6 : $i]:
% 3.81/4.06         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.81/4.06      inference('cnf', [status(esa)], [d3_tarski])).
% 3.81/4.06  thf('15', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('16', plain,
% 3.81/4.06      (![X10 : $i, X11 : $i]:
% 3.81/4.06         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 3.81/4.06      inference('cnf', [status(esa)], [t3_subset])).
% 3.81/4.06  thf('17', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 3.81/4.06      inference('sup-', [status(thm)], ['15', '16'])).
% 3.81/4.06  thf('18', plain,
% 3.81/4.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.81/4.06         (~ (r2_hidden @ X3 @ X4)
% 3.81/4.06          | (r2_hidden @ X3 @ X5)
% 3.81/4.06          | ~ (r1_tarski @ X4 @ X5))),
% 3.81/4.06      inference('cnf', [status(esa)], [d3_tarski])).
% 3.81/4.06  thf('19', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.81/4.06          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 3.81/4.06      inference('sup-', [status(thm)], ['17', '18'])).
% 3.81/4.06  thf('20', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         ((r1_tarski @ sk_C_2 @ X0)
% 3.81/4.06          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['14', '19'])).
% 3.81/4.06  thf(d1_xboole_0, axiom,
% 3.81/4.06    (![A:$i]:
% 3.81/4.06     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.81/4.06  thf('21', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.81/4.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.81/4.06  thf('22', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         ((r1_tarski @ sk_C_2 @ X0)
% 3.81/4.06          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['20', '21'])).
% 3.81/4.06  thf('23', plain,
% 3.81/4.06      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | (r1_tarski @ sk_C_2 @ X0))),
% 3.81/4.06      inference('sup-', [status(thm)], ['13', '22'])).
% 3.81/4.06  thf('24', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]:
% 3.81/4.06         ((zip_tseitin_0 @ sk_B_1 @ X1) | (r1_tarski @ sk_C_2 @ X0))),
% 3.81/4.06      inference('sup-', [status(thm)], ['7', '23'])).
% 3.81/4.06  thf('25', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.81/4.06  thf(zf_stmt_3, axiom,
% 3.81/4.06    (![C:$i,B:$i,A:$i]:
% 3.81/4.06     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.81/4.06       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.81/4.06  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.81/4.06  thf(zf_stmt_5, axiom,
% 3.81/4.06    (![A:$i,B:$i,C:$i]:
% 3.81/4.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.81/4.06       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.81/4.06         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.81/4.06           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.81/4.06             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.81/4.06  thf('26', plain,
% 3.81/4.06      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.81/4.06         (~ (zip_tseitin_0 @ X33 @ X34)
% 3.81/4.06          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 3.81/4.06          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.81/4.06  thf('27', plain,
% 3.81/4.06      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.81/4.06        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.81/4.06      inference('sup-', [status(thm)], ['25', '26'])).
% 3.81/4.06  thf('28', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.81/4.06      inference('sup-', [status(thm)], ['24', '27'])).
% 3.81/4.06  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('30', plain,
% 3.81/4.06      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.81/4.06         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 3.81/4.06          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 3.81/4.06          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.81/4.06  thf('31', plain,
% 3.81/4.06      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.81/4.06        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['29', '30'])).
% 3.81/4.06  thf('32', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf(redefinition_k1_relset_1, axiom,
% 3.81/4.06    (![A:$i,B:$i,C:$i]:
% 3.81/4.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.81/4.06       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.81/4.06  thf('33', plain,
% 3.81/4.06      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.81/4.06         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 3.81/4.06          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.81/4.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.81/4.06  thf('34', plain,
% 3.81/4.06      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.81/4.06      inference('sup-', [status(thm)], ['32', '33'])).
% 3.81/4.06  thf('35', plain,
% 3.81/4.06      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.81/4.06        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.81/4.06      inference('demod', [status(thm)], ['31', '34'])).
% 3.81/4.06  thf('36', plain,
% 3.81/4.06      (![X0 : $i]: ((r1_tarski @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['28', '35'])).
% 3.81/4.06  thf('37', plain,
% 3.81/4.06      (![X4 : $i, X6 : $i]:
% 3.81/4.06         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.81/4.06      inference('cnf', [status(esa)], [d3_tarski])).
% 3.81/4.06  thf('38', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.81/4.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.81/4.06  thf('39', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.81/4.06      inference('sup-', [status(thm)], ['37', '38'])).
% 3.81/4.06  thf('40', plain,
% 3.81/4.06      (![X7 : $i, X9 : $i]:
% 3.81/4.06         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.81/4.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.81/4.06  thf('41', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]:
% 3.81/4.06         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['39', '40'])).
% 3.81/4.06  thf('42', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         (((sk_A) = (k1_relat_1 @ sk_D))
% 3.81/4.06          | ((sk_C_2) = (X0))
% 3.81/4.06          | ~ (v1_xboole_0 @ X0))),
% 3.81/4.06      inference('sup-', [status(thm)], ['36', '41'])).
% 3.81/4.06  thf('43', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('44', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 3.81/4.06          | ~ (v1_xboole_0 @ X0)
% 3.81/4.06          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['42', '43'])).
% 3.81/4.06  thf('45', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | ~ (v1_xboole_0 @ sk_D))),
% 3.81/4.06      inference('sup-', [status(thm)], ['4', '44'])).
% 3.81/4.06  thf('46', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.81/4.06      inference('sup+', [status(thm)], ['5', '6'])).
% 3.81/4.06  thf('47', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('48', plain,
% 3.81/4.06      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.81/4.06         (~ (v1_xboole_0 @ X18)
% 3.81/4.06          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 3.81/4.06          | (v1_xboole_0 @ X19))),
% 3.81/4.06      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.81/4.06  thf('49', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 3.81/4.06      inference('sup-', [status(thm)], ['47', '48'])).
% 3.81/4.06  thf('50', plain,
% 3.81/4.06      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 3.81/4.06      inference('sup-', [status(thm)], ['46', '49'])).
% 3.81/4.06  thf('51', plain,
% 3.81/4.06      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.81/4.06        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.81/4.06      inference('sup-', [status(thm)], ['25', '26'])).
% 3.81/4.06  thf('52', plain,
% 3.81/4.06      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.81/4.06      inference('sup-', [status(thm)], ['50', '51'])).
% 3.81/4.06  thf('53', plain,
% 3.81/4.06      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.81/4.06        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.81/4.06      inference('demod', [status(thm)], ['31', '34'])).
% 3.81/4.06  thf('54', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['52', '53'])).
% 3.81/4.06  thf('55', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.81/4.06      inference('clc', [status(thm)], ['45', '54'])).
% 3.81/4.06  thf('56', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 3.81/4.06      inference('sup-', [status(thm)], ['1', '3'])).
% 3.81/4.06  thf('57', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]:
% 3.81/4.06         ((zip_tseitin_0 @ sk_B_1 @ X1) | (r1_tarski @ sk_C_2 @ X0))),
% 3.81/4.06      inference('sup-', [status(thm)], ['7', '23'])).
% 3.81/4.06  thf('58', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('59', plain,
% 3.81/4.06      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.81/4.06         (~ (zip_tseitin_0 @ X33 @ X34)
% 3.81/4.06          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 3.81/4.06          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.81/4.06  thf('60', plain,
% 3.81/4.06      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.81/4.06        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.81/4.06      inference('sup-', [status(thm)], ['58', '59'])).
% 3.81/4.06  thf('61', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 3.81/4.06      inference('sup-', [status(thm)], ['57', '60'])).
% 3.81/4.06  thf('62', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('63', plain,
% 3.81/4.06      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.81/4.06         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 3.81/4.06          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 3.81/4.06          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.81/4.06  thf('64', plain,
% 3.81/4.06      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.81/4.06        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['62', '63'])).
% 3.81/4.06  thf('65', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('66', plain,
% 3.81/4.06      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.81/4.06         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 3.81/4.06          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.81/4.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.81/4.06  thf('67', plain,
% 3.81/4.06      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.81/4.06      inference('sup-', [status(thm)], ['65', '66'])).
% 3.81/4.06  thf('68', plain,
% 3.81/4.06      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.81/4.06        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.81/4.06      inference('demod', [status(thm)], ['64', '67'])).
% 3.81/4.06  thf('69', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         ((r1_tarski @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['61', '68'])).
% 3.81/4.06  thf('70', plain,
% 3.81/4.06      (![X0 : $i, X1 : $i]:
% 3.81/4.06         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['39', '40'])).
% 3.81/4.06  thf('71', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 3.81/4.06          | ((sk_C_2) = (X0))
% 3.81/4.06          | ~ (v1_xboole_0 @ X0))),
% 3.81/4.06      inference('sup-', [status(thm)], ['69', '70'])).
% 3.81/4.06  thf('72', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('73', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 3.81/4.06          | ~ (v1_xboole_0 @ X0)
% 3.81/4.06          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['71', '72'])).
% 3.81/4.06  thf('74', plain,
% 3.81/4.06      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_D))),
% 3.81/4.06      inference('sup-', [status(thm)], ['56', '73'])).
% 3.81/4.06  thf('75', plain,
% 3.81/4.06      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 3.81/4.06      inference('sup-', [status(thm)], ['46', '49'])).
% 3.81/4.06  thf('76', plain,
% 3.81/4.06      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.81/4.06        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.81/4.06      inference('sup-', [status(thm)], ['58', '59'])).
% 3.81/4.06  thf('77', plain,
% 3.81/4.06      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 3.81/4.06      inference('sup-', [status(thm)], ['75', '76'])).
% 3.81/4.06  thf('78', plain,
% 3.81/4.06      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.81/4.06        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.81/4.06      inference('demod', [status(thm)], ['64', '67'])).
% 3.81/4.06  thf('79', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.81/4.06      inference('sup-', [status(thm)], ['77', '78'])).
% 3.81/4.06  thf('80', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.81/4.06      inference('clc', [status(thm)], ['74', '79'])).
% 3.81/4.06  thf(t9_funct_1, axiom,
% 3.81/4.06    (![A:$i]:
% 3.81/4.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.81/4.06       ( ![B:$i]:
% 3.81/4.06         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.81/4.06           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.81/4.06               ( ![C:$i]:
% 3.81/4.06                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.81/4.06                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.81/4.06             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.81/4.06  thf('81', plain,
% 3.81/4.06      (![X13 : $i, X14 : $i]:
% 3.81/4.06         (~ (v1_relat_1 @ X13)
% 3.81/4.06          | ~ (v1_funct_1 @ X13)
% 3.81/4.06          | ((X14) = (X13))
% 3.81/4.06          | (r2_hidden @ (sk_C_1 @ X13 @ X14) @ (k1_relat_1 @ X14))
% 3.81/4.06          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 3.81/4.06          | ~ (v1_funct_1 @ X14)
% 3.81/4.06          | ~ (v1_relat_1 @ X14))),
% 3.81/4.06      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.81/4.06  thf('82', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         (((sk_A) != (k1_relat_1 @ X0))
% 3.81/4.06          | ~ (v1_relat_1 @ sk_C_2)
% 3.81/4.06          | ~ (v1_funct_1 @ sk_C_2)
% 3.81/4.06          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 3.81/4.06          | ((sk_C_2) = (X0))
% 3.81/4.06          | ~ (v1_funct_1 @ X0)
% 3.81/4.06          | ~ (v1_relat_1 @ X0))),
% 3.81/4.06      inference('sup-', [status(thm)], ['80', '81'])).
% 3.81/4.06  thf('83', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf(cc1_relset_1, axiom,
% 3.81/4.06    (![A:$i,B:$i,C:$i]:
% 3.81/4.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.81/4.06       ( v1_relat_1 @ C ) ))).
% 3.81/4.06  thf('84', plain,
% 3.81/4.06      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.81/4.06         ((v1_relat_1 @ X15)
% 3.81/4.06          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.81/4.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.81/4.06  thf('85', plain, ((v1_relat_1 @ sk_C_2)),
% 3.81/4.06      inference('sup-', [status(thm)], ['83', '84'])).
% 3.81/4.06  thf('86', plain, ((v1_funct_1 @ sk_C_2)),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('87', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.81/4.06      inference('clc', [status(thm)], ['74', '79'])).
% 3.81/4.06  thf('88', plain,
% 3.81/4.06      (![X0 : $i]:
% 3.81/4.06         (((sk_A) != (k1_relat_1 @ X0))
% 3.81/4.06          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 3.81/4.06          | ((sk_C_2) = (X0))
% 3.81/4.06          | ~ (v1_funct_1 @ X0)
% 3.81/4.06          | ~ (v1_relat_1 @ X0))),
% 3.81/4.06      inference('demod', [status(thm)], ['82', '85', '86', '87'])).
% 3.81/4.06  thf('89', plain,
% 3.81/4.06      ((((sk_A) != (sk_A))
% 3.81/4.06        | ~ (v1_relat_1 @ sk_D)
% 3.81/4.06        | ~ (v1_funct_1 @ sk_D)
% 3.81/4.06        | ((sk_C_2) = (sk_D))
% 3.81/4.06        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.81/4.06      inference('sup-', [status(thm)], ['55', '88'])).
% 3.81/4.06  thf('90', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('91', plain,
% 3.81/4.06      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.81/4.06         ((v1_relat_1 @ X15)
% 3.81/4.06          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.81/4.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.81/4.06  thf('92', plain, ((v1_relat_1 @ sk_D)),
% 3.81/4.06      inference('sup-', [status(thm)], ['90', '91'])).
% 3.81/4.06  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('94', plain,
% 3.81/4.06      ((((sk_A) != (sk_A))
% 3.81/4.06        | ((sk_C_2) = (sk_D))
% 3.81/4.06        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.81/4.06      inference('demod', [status(thm)], ['89', '92', '93'])).
% 3.81/4.06  thf('95', plain,
% 3.81/4.06      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 3.81/4.06      inference('simplify', [status(thm)], ['94'])).
% 3.81/4.06  thf('96', plain,
% 3.81/4.06      (![X36 : $i]:
% 3.81/4.06         (((k1_funct_1 @ sk_C_2 @ X36) = (k1_funct_1 @ sk_D @ X36))
% 3.81/4.06          | ~ (r2_hidden @ X36 @ sk_A))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('97', plain,
% 3.81/4.06      ((((sk_C_2) = (sk_D))
% 3.81/4.06        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.81/4.06            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 3.81/4.06      inference('sup-', [status(thm)], ['95', '96'])).
% 3.81/4.06  thf('98', plain,
% 3.81/4.06      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.81/4.06         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 3.81/4.06      inference('condensation', [status(thm)], ['97'])).
% 3.81/4.06  thf('99', plain,
% 3.81/4.06      (![X13 : $i, X14 : $i]:
% 3.81/4.06         (~ (v1_relat_1 @ X13)
% 3.81/4.06          | ~ (v1_funct_1 @ X13)
% 3.81/4.06          | ((X14) = (X13))
% 3.81/4.06          | ((k1_funct_1 @ X14 @ (sk_C_1 @ X13 @ X14))
% 3.81/4.06              != (k1_funct_1 @ X13 @ (sk_C_1 @ X13 @ X14)))
% 3.81/4.06          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 3.81/4.06          | ~ (v1_funct_1 @ X14)
% 3.81/4.06          | ~ (v1_relat_1 @ X14))),
% 3.81/4.06      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.81/4.06  thf('100', plain,
% 3.81/4.06      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.81/4.06          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.81/4.06        | ~ (v1_relat_1 @ sk_C_2)
% 3.81/4.06        | ~ (v1_funct_1 @ sk_C_2)
% 3.81/4.06        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 3.81/4.06        | ((sk_C_2) = (sk_D))
% 3.81/4.06        | ~ (v1_funct_1 @ sk_D)
% 3.81/4.06        | ~ (v1_relat_1 @ sk_D))),
% 3.81/4.06      inference('sup-', [status(thm)], ['98', '99'])).
% 3.81/4.06  thf('101', plain, ((v1_relat_1 @ sk_C_2)),
% 3.81/4.06      inference('sup-', [status(thm)], ['83', '84'])).
% 3.81/4.06  thf('102', plain, ((v1_funct_1 @ sk_C_2)),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('103', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.81/4.06      inference('clc', [status(thm)], ['74', '79'])).
% 3.81/4.06  thf('104', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.81/4.06      inference('clc', [status(thm)], ['45', '54'])).
% 3.81/4.06  thf('105', plain, ((v1_funct_1 @ sk_D)),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 3.81/4.06      inference('sup-', [status(thm)], ['90', '91'])).
% 3.81/4.06  thf('107', plain,
% 3.81/4.06      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.81/4.06          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.81/4.06        | ((sk_A) != (sk_A))
% 3.81/4.06        | ((sk_C_2) = (sk_D)))),
% 3.81/4.06      inference('demod', [status(thm)],
% 3.81/4.06                ['100', '101', '102', '103', '104', '105', '106'])).
% 3.81/4.06  thf('108', plain, (((sk_C_2) = (sk_D))),
% 3.81/4.06      inference('simplify', [status(thm)], ['107'])).
% 3.81/4.06  thf('109', plain,
% 3.81/4.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.81/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.06  thf('110', plain,
% 3.81/4.06      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.81/4.06         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 3.81/4.06          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.81/4.06      inference('simplify', [status(thm)], ['2'])).
% 3.81/4.06  thf('111', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 3.81/4.06      inference('sup-', [status(thm)], ['109', '110'])).
% 3.81/4.06  thf('112', plain, ($false),
% 3.81/4.06      inference('demod', [status(thm)], ['0', '108', '111'])).
% 3.81/4.06  
% 3.81/4.06  % SZS output end Refutation
% 3.81/4.06  
% 3.81/4.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
