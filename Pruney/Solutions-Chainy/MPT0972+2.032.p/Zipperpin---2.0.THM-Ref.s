%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YQ1Dm6OZ0q

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:37 EST 2020

% Result     : Theorem 6.12s
% Output     : Refutation 6.12s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 564 expanded)
%              Number of leaves         :   40 ( 188 expanded)
%              Depth                    :   23
%              Number of atoms          : 1031 (6611 expanded)
%              Number of equality atoms :   73 ( 316 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('9',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 )
      | ( X27 != X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','35'])).

thf('37',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('41',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['39','52'])).

thf('54',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','53'])).

thf('55',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('61',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['39','52'])).

thf('67',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['62','67'])).

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

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( r2_hidden @ ( sk_C_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','73','74','75'])).

thf('77',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['77','80','81'])).

thf('83',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X39: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X39 )
        = ( k1_funct_1 @ sk_D @ X39 ) )
      | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['85'])).

thf('87',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( ( k1_funct_1 @ X20 @ ( sk_C_1 @ X19 @ X20 ) )
       != ( k1_funct_1 @ X19 @ ( sk_C_1 @ X19 @ X20 ) ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('88',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('92',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','54'])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('95',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['88','89','90','91','92','93','94'])).

thf('96',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('99',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','96','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YQ1Dm6OZ0q
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:50:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 6.12/6.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.12/6.34  % Solved by: fo/fo7.sh
% 6.12/6.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.12/6.34  % done 3998 iterations in 5.875s
% 6.12/6.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.12/6.34  % SZS output start Refutation
% 6.12/6.34  thf(sk_A_type, type, sk_A: $i).
% 6.12/6.34  thf(sk_B_type, type, sk_B: $i > $i).
% 6.12/6.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.12/6.34  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.12/6.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.12/6.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.12/6.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.12/6.34  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.12/6.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.12/6.34  thf(sk_D_type, type, sk_D: $i).
% 6.12/6.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.12/6.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.12/6.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.12/6.34  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.12/6.34  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.12/6.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.12/6.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.12/6.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.12/6.34  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.12/6.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.12/6.34  thf(sk_C_2_type, type, sk_C_2: $i).
% 6.12/6.34  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.12/6.34  thf(t18_funct_2, conjecture,
% 6.12/6.34    (![A:$i,B:$i,C:$i]:
% 6.12/6.34     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.12/6.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.12/6.34       ( ![D:$i]:
% 6.12/6.34         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.12/6.34             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.12/6.34           ( ( ![E:$i]:
% 6.12/6.34               ( ( r2_hidden @ E @ A ) =>
% 6.12/6.34                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.12/6.34             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 6.12/6.34  thf(zf_stmt_0, negated_conjecture,
% 6.12/6.34    (~( ![A:$i,B:$i,C:$i]:
% 6.12/6.34        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.12/6.34            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.12/6.34          ( ![D:$i]:
% 6.12/6.34            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.12/6.34                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.12/6.34              ( ( ![E:$i]:
% 6.12/6.34                  ( ( r2_hidden @ E @ A ) =>
% 6.12/6.34                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.12/6.34                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 6.12/6.34    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 6.12/6.34  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf(d1_funct_2, axiom,
% 6.12/6.34    (![A:$i,B:$i,C:$i]:
% 6.12/6.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.12/6.34       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.12/6.34           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.12/6.34             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.12/6.34         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.12/6.34           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.12/6.34             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.12/6.34  thf(zf_stmt_1, axiom,
% 6.12/6.34    (![C:$i,B:$i,A:$i]:
% 6.12/6.34     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.12/6.34       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.12/6.34  thf('2', plain,
% 6.12/6.34      (![X33 : $i, X34 : $i, X35 : $i]:
% 6.12/6.34         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 6.12/6.34          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 6.12/6.34          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.12/6.34  thf('3', plain,
% 6.12/6.34      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.12/6.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 6.12/6.34      inference('sup-', [status(thm)], ['1', '2'])).
% 6.12/6.34  thf('4', plain,
% 6.12/6.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf(redefinition_k1_relset_1, axiom,
% 6.12/6.34    (![A:$i,B:$i,C:$i]:
% 6.12/6.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.12/6.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.12/6.34  thf('5', plain,
% 6.12/6.34      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.12/6.34         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 6.12/6.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 6.12/6.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.12/6.34  thf('6', plain,
% 6.12/6.34      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.12/6.34      inference('sup-', [status(thm)], ['4', '5'])).
% 6.12/6.34  thf('7', plain,
% 6.12/6.34      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.12/6.34        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.12/6.34      inference('demod', [status(thm)], ['3', '6'])).
% 6.12/6.34  thf('8', plain,
% 6.12/6.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.12/6.34  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 6.12/6.34  thf(zf_stmt_4, axiom,
% 6.12/6.34    (![B:$i,A:$i]:
% 6.12/6.34     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.12/6.34       ( zip_tseitin_0 @ B @ A ) ))).
% 6.12/6.34  thf(zf_stmt_5, axiom,
% 6.12/6.34    (![A:$i,B:$i,C:$i]:
% 6.12/6.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.12/6.34       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.12/6.34         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.12/6.34           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.12/6.34             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.12/6.34  thf('9', plain,
% 6.12/6.34      (![X36 : $i, X37 : $i, X38 : $i]:
% 6.12/6.34         (~ (zip_tseitin_0 @ X36 @ X37)
% 6.12/6.34          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 6.12/6.34          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.12/6.34  thf('10', plain,
% 6.12/6.34      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.12/6.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.12/6.34      inference('sup-', [status(thm)], ['8', '9'])).
% 6.12/6.34  thf('11', plain,
% 6.12/6.34      (![X31 : $i, X32 : $i]:
% 6.12/6.34         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.12/6.34  thf(t113_zfmisc_1, axiom,
% 6.12/6.34    (![A:$i,B:$i]:
% 6.12/6.34     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.12/6.34       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.12/6.34  thf('12', plain,
% 6.12/6.34      (![X10 : $i, X11 : $i]:
% 6.12/6.34         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 6.12/6.34          | ((X11) != (k1_xboole_0)))),
% 6.12/6.34      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.12/6.34  thf('13', plain,
% 6.12/6.34      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 6.12/6.34      inference('simplify', [status(thm)], ['12'])).
% 6.12/6.34  thf('14', plain,
% 6.12/6.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.12/6.34         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.12/6.34      inference('sup+', [status(thm)], ['11', '13'])).
% 6.12/6.34  thf(d1_xboole_0, axiom,
% 6.12/6.34    (![A:$i]:
% 6.12/6.34     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.12/6.34  thf('15', plain,
% 6.12/6.34      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.12/6.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.12/6.34  thf('16', plain,
% 6.12/6.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf(t3_subset, axiom,
% 6.12/6.34    (![A:$i,B:$i]:
% 6.12/6.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.12/6.34  thf('17', plain,
% 6.12/6.34      (![X13 : $i, X14 : $i]:
% 6.12/6.34         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 6.12/6.34      inference('cnf', [status(esa)], [t3_subset])).
% 6.12/6.34  thf('18', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 6.12/6.34      inference('sup-', [status(thm)], ['16', '17'])).
% 6.12/6.34  thf(d3_tarski, axiom,
% 6.12/6.34    (![A:$i,B:$i]:
% 6.12/6.34     ( ( r1_tarski @ A @ B ) <=>
% 6.12/6.34       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.12/6.34  thf('19', plain,
% 6.12/6.34      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.12/6.34         (~ (r2_hidden @ X3 @ X4)
% 6.12/6.34          | (r2_hidden @ X3 @ X5)
% 6.12/6.34          | ~ (r1_tarski @ X4 @ X5))),
% 6.12/6.34      inference('cnf', [status(esa)], [d3_tarski])).
% 6.12/6.34  thf('20', plain,
% 6.12/6.34      (![X0 : $i]:
% 6.12/6.34         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.12/6.34          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 6.12/6.34      inference('sup-', [status(thm)], ['18', '19'])).
% 6.12/6.34  thf('21', plain,
% 6.12/6.34      (((v1_xboole_0 @ sk_C_2)
% 6.12/6.34        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('sup-', [status(thm)], ['15', '20'])).
% 6.12/6.34  thf('22', plain,
% 6.12/6.34      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.12/6.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.12/6.34  thf('23', plain,
% 6.12/6.34      (((v1_xboole_0 @ sk_C_2)
% 6.12/6.34        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('sup-', [status(thm)], ['21', '22'])).
% 6.12/6.34  thf('24', plain,
% 6.12/6.34      (![X0 : $i]:
% 6.12/6.34         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.12/6.34          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 6.12/6.34          | (v1_xboole_0 @ sk_C_2))),
% 6.12/6.34      inference('sup-', [status(thm)], ['14', '23'])).
% 6.12/6.34  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.12/6.34  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.12/6.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.12/6.34  thf('26', plain,
% 6.12/6.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 6.12/6.34      inference('demod', [status(thm)], ['24', '25'])).
% 6.12/6.34  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.12/6.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.12/6.34  thf(t8_boole, axiom,
% 6.12/6.34    (![A:$i,B:$i]:
% 6.12/6.34     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 6.12/6.34  thf('28', plain,
% 6.12/6.34      (![X7 : $i, X8 : $i]:
% 6.12/6.34         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 6.12/6.34      inference('cnf', [status(esa)], [t8_boole])).
% 6.12/6.34  thf('29', plain,
% 6.12/6.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.12/6.34      inference('sup-', [status(thm)], ['27', '28'])).
% 6.12/6.34  thf('30', plain,
% 6.12/6.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.12/6.34      inference('sup-', [status(thm)], ['27', '28'])).
% 6.12/6.34  thf(t4_subset_1, axiom,
% 6.12/6.34    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.12/6.34  thf('31', plain,
% 6.12/6.34      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 6.12/6.34      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.12/6.34  thf(redefinition_r2_relset_1, axiom,
% 6.12/6.34    (![A:$i,B:$i,C:$i,D:$i]:
% 6.12/6.34     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.12/6.34         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.12/6.34       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.12/6.34  thf('32', plain,
% 6.12/6.34      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 6.12/6.34         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 6.12/6.34          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 6.12/6.34          | (r2_relset_1 @ X28 @ X29 @ X27 @ X30)
% 6.12/6.34          | ((X27) != (X30)))),
% 6.12/6.34      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.12/6.34  thf('33', plain,
% 6.12/6.34      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.12/6.34         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 6.12/6.34          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 6.12/6.34      inference('simplify', [status(thm)], ['32'])).
% 6.12/6.34  thf('34', plain,
% 6.12/6.34      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 6.12/6.34      inference('sup-', [status(thm)], ['31', '33'])).
% 6.12/6.34  thf('35', plain,
% 6.12/6.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.12/6.34         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 6.12/6.34      inference('sup+', [status(thm)], ['30', '34'])).
% 6.12/6.34  thf('36', plain,
% 6.12/6.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.12/6.34         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 6.12/6.34          | ~ (v1_xboole_0 @ X0)
% 6.12/6.34          | ~ (v1_xboole_0 @ X1))),
% 6.12/6.34      inference('sup+', [status(thm)], ['29', '35'])).
% 6.12/6.34  thf('37', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('38', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 6.12/6.34      inference('sup-', [status(thm)], ['36', '37'])).
% 6.12/6.34  thf('39', plain,
% 6.12/6.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 6.12/6.34      inference('sup-', [status(thm)], ['26', '38'])).
% 6.12/6.34  thf('40', plain,
% 6.12/6.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.12/6.34         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.12/6.34      inference('sup+', [status(thm)], ['11', '13'])).
% 6.12/6.34  thf('41', plain,
% 6.12/6.34      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.12/6.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.12/6.34  thf('42', plain,
% 6.12/6.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('43', plain,
% 6.12/6.34      (![X13 : $i, X14 : $i]:
% 6.12/6.34         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 6.12/6.34      inference('cnf', [status(esa)], [t3_subset])).
% 6.12/6.34  thf('44', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 6.12/6.34      inference('sup-', [status(thm)], ['42', '43'])).
% 6.12/6.34  thf('45', plain,
% 6.12/6.34      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.12/6.34         (~ (r2_hidden @ X3 @ X4)
% 6.12/6.34          | (r2_hidden @ X3 @ X5)
% 6.12/6.34          | ~ (r1_tarski @ X4 @ X5))),
% 6.12/6.34      inference('cnf', [status(esa)], [d3_tarski])).
% 6.12/6.34  thf('46', plain,
% 6.12/6.34      (![X0 : $i]:
% 6.12/6.34         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.12/6.34          | ~ (r2_hidden @ X0 @ sk_D))),
% 6.12/6.34      inference('sup-', [status(thm)], ['44', '45'])).
% 6.12/6.34  thf('47', plain,
% 6.12/6.34      (((v1_xboole_0 @ sk_D)
% 6.12/6.34        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('sup-', [status(thm)], ['41', '46'])).
% 6.12/6.34  thf('48', plain,
% 6.12/6.34      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.12/6.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.12/6.34  thf('49', plain,
% 6.12/6.34      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('sup-', [status(thm)], ['47', '48'])).
% 6.12/6.34  thf('50', plain,
% 6.12/6.34      (![X0 : $i]:
% 6.12/6.34         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.12/6.34          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 6.12/6.34          | (v1_xboole_0 @ sk_D))),
% 6.12/6.34      inference('sup-', [status(thm)], ['40', '49'])).
% 6.12/6.34  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.12/6.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.12/6.34  thf('52', plain,
% 6.12/6.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 6.12/6.34      inference('demod', [status(thm)], ['50', '51'])).
% 6.12/6.34  thf('53', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 6.12/6.34      inference('clc', [status(thm)], ['39', '52'])).
% 6.12/6.34  thf('54', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 6.12/6.34      inference('demod', [status(thm)], ['10', '53'])).
% 6.12/6.34  thf('55', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.12/6.34      inference('demod', [status(thm)], ['7', '54'])).
% 6.12/6.34  thf('56', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('57', plain,
% 6.12/6.34      (![X33 : $i, X34 : $i, X35 : $i]:
% 6.12/6.34         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 6.12/6.34          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 6.12/6.34          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.12/6.34  thf('58', plain,
% 6.12/6.34      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.12/6.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 6.12/6.34      inference('sup-', [status(thm)], ['56', '57'])).
% 6.12/6.34  thf('59', plain,
% 6.12/6.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('60', plain,
% 6.12/6.34      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.12/6.34         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 6.12/6.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 6.12/6.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.12/6.34  thf('61', plain,
% 6.12/6.34      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 6.12/6.34      inference('sup-', [status(thm)], ['59', '60'])).
% 6.12/6.34  thf('62', plain,
% 6.12/6.34      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.12/6.34        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.12/6.34      inference('demod', [status(thm)], ['58', '61'])).
% 6.12/6.34  thf('63', plain,
% 6.12/6.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('64', plain,
% 6.12/6.34      (![X36 : $i, X37 : $i, X38 : $i]:
% 6.12/6.34         (~ (zip_tseitin_0 @ X36 @ X37)
% 6.12/6.34          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 6.12/6.34          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.12/6.34  thf('65', plain,
% 6.12/6.34      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.12/6.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.12/6.34      inference('sup-', [status(thm)], ['63', '64'])).
% 6.12/6.34  thf('66', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 6.12/6.34      inference('clc', [status(thm)], ['39', '52'])).
% 6.12/6.34  thf('67', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 6.12/6.34      inference('demod', [status(thm)], ['65', '66'])).
% 6.12/6.34  thf('68', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.12/6.34      inference('demod', [status(thm)], ['62', '67'])).
% 6.12/6.34  thf(t9_funct_1, axiom,
% 6.12/6.34    (![A:$i]:
% 6.12/6.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.12/6.34       ( ![B:$i]:
% 6.12/6.34         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.12/6.34           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.12/6.34               ( ![C:$i]:
% 6.12/6.34                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 6.12/6.34                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 6.12/6.34             ( ( A ) = ( B ) ) ) ) ) ))).
% 6.12/6.34  thf('69', plain,
% 6.12/6.34      (![X19 : $i, X20 : $i]:
% 6.12/6.34         (~ (v1_relat_1 @ X19)
% 6.12/6.34          | ~ (v1_funct_1 @ X19)
% 6.12/6.34          | ((X20) = (X19))
% 6.12/6.34          | (r2_hidden @ (sk_C_1 @ X19 @ X20) @ (k1_relat_1 @ X20))
% 6.12/6.34          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 6.12/6.34          | ~ (v1_funct_1 @ X20)
% 6.12/6.34          | ~ (v1_relat_1 @ X20))),
% 6.12/6.34      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.12/6.34  thf('70', plain,
% 6.12/6.34      (![X0 : $i]:
% 6.12/6.34         (((sk_A) != (k1_relat_1 @ X0))
% 6.12/6.34          | ~ (v1_relat_1 @ sk_C_2)
% 6.12/6.34          | ~ (v1_funct_1 @ sk_C_2)
% 6.12/6.34          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 6.12/6.34          | ((sk_C_2) = (X0))
% 6.12/6.34          | ~ (v1_funct_1 @ X0)
% 6.12/6.34          | ~ (v1_relat_1 @ X0))),
% 6.12/6.34      inference('sup-', [status(thm)], ['68', '69'])).
% 6.12/6.34  thf('71', plain,
% 6.12/6.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf(cc1_relset_1, axiom,
% 6.12/6.34    (![A:$i,B:$i,C:$i]:
% 6.12/6.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.12/6.34       ( v1_relat_1 @ C ) ))).
% 6.12/6.34  thf('72', plain,
% 6.12/6.34      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.12/6.34         ((v1_relat_1 @ X21)
% 6.12/6.34          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 6.12/6.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.12/6.34  thf('73', plain, ((v1_relat_1 @ sk_C_2)),
% 6.12/6.34      inference('sup-', [status(thm)], ['71', '72'])).
% 6.12/6.34  thf('74', plain, ((v1_funct_1 @ sk_C_2)),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('75', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.12/6.34      inference('demod', [status(thm)], ['62', '67'])).
% 6.12/6.34  thf('76', plain,
% 6.12/6.34      (![X0 : $i]:
% 6.12/6.34         (((sk_A) != (k1_relat_1 @ X0))
% 6.12/6.34          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 6.12/6.34          | ((sk_C_2) = (X0))
% 6.12/6.34          | ~ (v1_funct_1 @ X0)
% 6.12/6.34          | ~ (v1_relat_1 @ X0))),
% 6.12/6.34      inference('demod', [status(thm)], ['70', '73', '74', '75'])).
% 6.12/6.34  thf('77', plain,
% 6.12/6.34      ((((sk_A) != (sk_A))
% 6.12/6.34        | ~ (v1_relat_1 @ sk_D)
% 6.12/6.34        | ~ (v1_funct_1 @ sk_D)
% 6.12/6.34        | ((sk_C_2) = (sk_D))
% 6.12/6.34        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 6.12/6.34      inference('sup-', [status(thm)], ['55', '76'])).
% 6.12/6.34  thf('78', plain,
% 6.12/6.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('79', plain,
% 6.12/6.34      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.12/6.34         ((v1_relat_1 @ X21)
% 6.12/6.34          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 6.12/6.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.12/6.34  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 6.12/6.34      inference('sup-', [status(thm)], ['78', '79'])).
% 6.12/6.34  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('82', plain,
% 6.12/6.34      ((((sk_A) != (sk_A))
% 6.12/6.34        | ((sk_C_2) = (sk_D))
% 6.12/6.34        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 6.12/6.34      inference('demod', [status(thm)], ['77', '80', '81'])).
% 6.12/6.34  thf('83', plain,
% 6.12/6.34      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 6.12/6.34      inference('simplify', [status(thm)], ['82'])).
% 6.12/6.34  thf('84', plain,
% 6.12/6.34      (![X39 : $i]:
% 6.12/6.34         (((k1_funct_1 @ sk_C_2 @ X39) = (k1_funct_1 @ sk_D @ X39))
% 6.12/6.34          | ~ (r2_hidden @ X39 @ sk_A))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('85', plain,
% 6.12/6.34      ((((sk_C_2) = (sk_D))
% 6.12/6.34        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.12/6.34            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 6.12/6.34      inference('sup-', [status(thm)], ['83', '84'])).
% 6.12/6.34  thf('86', plain,
% 6.12/6.34      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.12/6.34         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 6.12/6.34      inference('condensation', [status(thm)], ['85'])).
% 6.12/6.34  thf('87', plain,
% 6.12/6.34      (![X19 : $i, X20 : $i]:
% 6.12/6.34         (~ (v1_relat_1 @ X19)
% 6.12/6.34          | ~ (v1_funct_1 @ X19)
% 6.12/6.34          | ((X20) = (X19))
% 6.12/6.34          | ((k1_funct_1 @ X20 @ (sk_C_1 @ X19 @ X20))
% 6.12/6.34              != (k1_funct_1 @ X19 @ (sk_C_1 @ X19 @ X20)))
% 6.12/6.34          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 6.12/6.34          | ~ (v1_funct_1 @ X20)
% 6.12/6.34          | ~ (v1_relat_1 @ X20))),
% 6.12/6.34      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.12/6.34  thf('88', plain,
% 6.12/6.34      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.12/6.34          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 6.12/6.34        | ~ (v1_relat_1 @ sk_C_2)
% 6.12/6.34        | ~ (v1_funct_1 @ sk_C_2)
% 6.12/6.34        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 6.12/6.34        | ((sk_C_2) = (sk_D))
% 6.12/6.34        | ~ (v1_funct_1 @ sk_D)
% 6.12/6.34        | ~ (v1_relat_1 @ sk_D))),
% 6.12/6.34      inference('sup-', [status(thm)], ['86', '87'])).
% 6.12/6.34  thf('89', plain, ((v1_relat_1 @ sk_C_2)),
% 6.12/6.34      inference('sup-', [status(thm)], ['71', '72'])).
% 6.12/6.34  thf('90', plain, ((v1_funct_1 @ sk_C_2)),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('91', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.12/6.34      inference('demod', [status(thm)], ['62', '67'])).
% 6.12/6.34  thf('92', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.12/6.34      inference('demod', [status(thm)], ['7', '54'])).
% 6.12/6.34  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('94', plain, ((v1_relat_1 @ sk_D)),
% 6.12/6.34      inference('sup-', [status(thm)], ['78', '79'])).
% 6.12/6.34  thf('95', plain,
% 6.12/6.34      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.12/6.34          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 6.12/6.34        | ((sk_A) != (sk_A))
% 6.12/6.34        | ((sk_C_2) = (sk_D)))),
% 6.12/6.34      inference('demod', [status(thm)],
% 6.12/6.34                ['88', '89', '90', '91', '92', '93', '94'])).
% 6.12/6.34  thf('96', plain, (((sk_C_2) = (sk_D))),
% 6.12/6.34      inference('simplify', [status(thm)], ['95'])).
% 6.12/6.34  thf('97', plain,
% 6.12/6.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.12/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.34  thf('98', plain,
% 6.12/6.34      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.12/6.34         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 6.12/6.34          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 6.12/6.34      inference('simplify', [status(thm)], ['32'])).
% 6.12/6.34  thf('99', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 6.12/6.34      inference('sup-', [status(thm)], ['97', '98'])).
% 6.12/6.34  thf('100', plain, ($false),
% 6.12/6.34      inference('demod', [status(thm)], ['0', '96', '99'])).
% 6.12/6.34  
% 6.12/6.34  % SZS output end Refutation
% 6.12/6.34  
% 6.12/6.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
