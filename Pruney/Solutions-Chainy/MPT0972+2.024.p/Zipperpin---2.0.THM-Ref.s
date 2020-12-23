%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KyuFjFQUCb

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:36 EST 2020

% Result     : Theorem 6.26s
% Output     : Refutation 6.26s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 640 expanded)
%              Number of leaves         :   41 ( 214 expanded)
%              Depth                    :   23
%              Number of atoms          : 1063 (7095 expanded)
%              Number of equality atoms :   72 ( 314 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
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
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('35',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('38',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','41'])).

thf('43',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['45','58'])).

thf('60',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('71',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['45','58'])).

thf('73',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['68','73'])).

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

thf('75',plain,(
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

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('78',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('79',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','79','80','81'])).

thf('83',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['83','86','87'])).

thf('89',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X39: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X39 )
        = ( k1_funct_1 @ sk_D @ X39 ) )
      | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,(
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

thf('94',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('96',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('98',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','60'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('101',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99','100'])).

thf('102',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['38'])).

thf('105',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','102','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KyuFjFQUCb
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 6.26/6.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.26/6.47  % Solved by: fo/fo7.sh
% 6.26/6.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.26/6.47  % done 4056 iterations in 6.049s
% 6.26/6.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.26/6.47  % SZS output start Refutation
% 6.26/6.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.26/6.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.26/6.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.26/6.47  thf(sk_C_2_type, type, sk_C_2: $i).
% 6.26/6.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.26/6.47  thf(sk_B_type, type, sk_B: $i > $i).
% 6.26/6.47  thf(sk_A_type, type, sk_A: $i).
% 6.26/6.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.26/6.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.26/6.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.26/6.47  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.26/6.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.26/6.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.26/6.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.26/6.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.26/6.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.26/6.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.26/6.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.26/6.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.26/6.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.26/6.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.26/6.47  thf(sk_D_type, type, sk_D: $i).
% 6.26/6.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.26/6.47  thf(t18_funct_2, conjecture,
% 6.26/6.47    (![A:$i,B:$i,C:$i]:
% 6.26/6.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.26/6.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.26/6.47       ( ![D:$i]:
% 6.26/6.47         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.26/6.47             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.26/6.47           ( ( ![E:$i]:
% 6.26/6.47               ( ( r2_hidden @ E @ A ) =>
% 6.26/6.47                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.26/6.47             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 6.26/6.47  thf(zf_stmt_0, negated_conjecture,
% 6.26/6.47    (~( ![A:$i,B:$i,C:$i]:
% 6.26/6.47        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.26/6.47            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.26/6.47          ( ![D:$i]:
% 6.26/6.47            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.26/6.47                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.26/6.47              ( ( ![E:$i]:
% 6.26/6.47                  ( ( r2_hidden @ E @ A ) =>
% 6.26/6.47                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.26/6.47                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 6.26/6.47    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 6.26/6.47  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf(d1_funct_2, axiom,
% 6.26/6.47    (![A:$i,B:$i,C:$i]:
% 6.26/6.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.26/6.47       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.26/6.47           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.26/6.47             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.26/6.47         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.26/6.47           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.26/6.47             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.26/6.47  thf(zf_stmt_1, axiom,
% 6.26/6.47    (![C:$i,B:$i,A:$i]:
% 6.26/6.47     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.26/6.47       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.26/6.47  thf('2', plain,
% 6.26/6.47      (![X33 : $i, X34 : $i, X35 : $i]:
% 6.26/6.47         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 6.26/6.47          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 6.26/6.47          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.26/6.47  thf('3', plain,
% 6.26/6.47      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.26/6.47        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 6.26/6.47      inference('sup-', [status(thm)], ['1', '2'])).
% 6.26/6.47  thf('4', plain,
% 6.26/6.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf(redefinition_k1_relset_1, axiom,
% 6.26/6.47    (![A:$i,B:$i,C:$i]:
% 6.26/6.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.26/6.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.26/6.47  thf('5', plain,
% 6.26/6.47      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.26/6.47         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 6.26/6.47          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 6.26/6.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.26/6.47  thf('6', plain,
% 6.26/6.47      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.26/6.47      inference('sup-', [status(thm)], ['4', '5'])).
% 6.26/6.47  thf('7', plain,
% 6.26/6.47      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.26/6.47        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.26/6.47      inference('demod', [status(thm)], ['3', '6'])).
% 6.26/6.47  thf('8', plain,
% 6.26/6.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.26/6.47  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 6.26/6.47  thf(zf_stmt_4, axiom,
% 6.26/6.47    (![B:$i,A:$i]:
% 6.26/6.47     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.26/6.47       ( zip_tseitin_0 @ B @ A ) ))).
% 6.26/6.47  thf(zf_stmt_5, axiom,
% 6.26/6.47    (![A:$i,B:$i,C:$i]:
% 6.26/6.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.26/6.47       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.26/6.47         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.26/6.47           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.26/6.47             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.26/6.47  thf('9', plain,
% 6.26/6.47      (![X36 : $i, X37 : $i, X38 : $i]:
% 6.26/6.47         (~ (zip_tseitin_0 @ X36 @ X37)
% 6.26/6.47          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 6.26/6.47          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.26/6.47  thf('10', plain,
% 6.26/6.47      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.26/6.47        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.26/6.47      inference('sup-', [status(thm)], ['8', '9'])).
% 6.26/6.47  thf('11', plain,
% 6.26/6.47      (![X31 : $i, X32 : $i]:
% 6.26/6.47         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.26/6.47  thf(t113_zfmisc_1, axiom,
% 6.26/6.47    (![A:$i,B:$i]:
% 6.26/6.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.26/6.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.26/6.47  thf('12', plain,
% 6.26/6.47      (![X14 : $i, X15 : $i]:
% 6.26/6.47         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 6.26/6.47          | ((X15) != (k1_xboole_0)))),
% 6.26/6.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.26/6.47  thf('13', plain,
% 6.26/6.47      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 6.26/6.47      inference('simplify', [status(thm)], ['12'])).
% 6.26/6.47  thf('14', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.26/6.47         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.26/6.47      inference('sup+', [status(thm)], ['11', '13'])).
% 6.26/6.47  thf(d1_xboole_0, axiom,
% 6.26/6.47    (![A:$i]:
% 6.26/6.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.26/6.47  thf('15', plain,
% 6.26/6.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.26/6.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.26/6.47  thf('16', plain,
% 6.26/6.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf(t3_subset, axiom,
% 6.26/6.47    (![A:$i,B:$i]:
% 6.26/6.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.26/6.47  thf('17', plain,
% 6.26/6.47      (![X16 : $i, X17 : $i]:
% 6.26/6.47         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 6.26/6.47      inference('cnf', [status(esa)], [t3_subset])).
% 6.26/6.47  thf('18', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 6.26/6.47      inference('sup-', [status(thm)], ['16', '17'])).
% 6.26/6.47  thf(d3_tarski, axiom,
% 6.26/6.47    (![A:$i,B:$i]:
% 6.26/6.47     ( ( r1_tarski @ A @ B ) <=>
% 6.26/6.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.26/6.47  thf('19', plain,
% 6.26/6.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.26/6.47         (~ (r2_hidden @ X3 @ X4)
% 6.26/6.47          | (r2_hidden @ X3 @ X5)
% 6.26/6.47          | ~ (r1_tarski @ X4 @ X5))),
% 6.26/6.47      inference('cnf', [status(esa)], [d3_tarski])).
% 6.26/6.47  thf('20', plain,
% 6.26/6.47      (![X0 : $i]:
% 6.26/6.47         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.26/6.47          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 6.26/6.47      inference('sup-', [status(thm)], ['18', '19'])).
% 6.26/6.47  thf('21', plain,
% 6.26/6.47      (((v1_xboole_0 @ sk_C_2)
% 6.26/6.47        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('sup-', [status(thm)], ['15', '20'])).
% 6.26/6.47  thf('22', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.26/6.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.26/6.47  thf('23', plain,
% 6.26/6.47      (((v1_xboole_0 @ sk_C_2)
% 6.26/6.47        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('sup-', [status(thm)], ['21', '22'])).
% 6.26/6.47  thf('24', plain,
% 6.26/6.47      (![X0 : $i]:
% 6.26/6.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.26/6.47          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 6.26/6.47          | (v1_xboole_0 @ sk_C_2))),
% 6.26/6.47      inference('sup-', [status(thm)], ['14', '23'])).
% 6.26/6.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.26/6.47  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.26/6.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.26/6.47  thf('26', plain,
% 6.26/6.47      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 6.26/6.47      inference('demod', [status(thm)], ['24', '25'])).
% 6.26/6.47  thf('27', plain,
% 6.26/6.47      (![X4 : $i, X6 : $i]:
% 6.26/6.47         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 6.26/6.47      inference('cnf', [status(esa)], [d3_tarski])).
% 6.26/6.47  thf('28', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.26/6.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.26/6.47  thf('29', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.26/6.47      inference('sup-', [status(thm)], ['27', '28'])).
% 6.26/6.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.26/6.47  thf('30', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 6.26/6.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.26/6.47  thf(d10_xboole_0, axiom,
% 6.26/6.47    (![A:$i,B:$i]:
% 6.26/6.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.26/6.47  thf('31', plain,
% 6.26/6.47      (![X7 : $i, X9 : $i]:
% 6.26/6.47         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 6.26/6.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.26/6.47  thf('32', plain,
% 6.26/6.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.26/6.47      inference('sup-', [status(thm)], ['30', '31'])).
% 6.26/6.47  thf('33', plain,
% 6.26/6.47      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 6.26/6.47      inference('sup-', [status(thm)], ['29', '32'])).
% 6.26/6.47  thf('34', plain,
% 6.26/6.47      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 6.26/6.47      inference('sup-', [status(thm)], ['29', '32'])).
% 6.26/6.47  thf('35', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 6.26/6.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.26/6.47  thf('36', plain,
% 6.26/6.47      (![X16 : $i, X18 : $i]:
% 6.26/6.47         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 6.26/6.47      inference('cnf', [status(esa)], [t3_subset])).
% 6.26/6.47  thf('37', plain,
% 6.26/6.47      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.26/6.47      inference('sup-', [status(thm)], ['35', '36'])).
% 6.26/6.47  thf(reflexivity_r2_relset_1, axiom,
% 6.26/6.47    (![A:$i,B:$i,C:$i,D:$i]:
% 6.26/6.47     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.26/6.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.26/6.47       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 6.26/6.47  thf('38', plain,
% 6.26/6.47      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 6.26/6.47         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 6.26/6.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 6.26/6.47          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 6.26/6.47      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 6.26/6.47  thf('39', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.26/6.47         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 6.26/6.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 6.26/6.47      inference('condensation', [status(thm)], ['38'])).
% 6.26/6.47  thf('40', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 6.26/6.47      inference('sup-', [status(thm)], ['37', '39'])).
% 6.26/6.47  thf('41', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.26/6.47         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 6.26/6.47      inference('sup+', [status(thm)], ['34', '40'])).
% 6.26/6.47  thf('42', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.26/6.47         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 6.26/6.47          | ~ (v1_xboole_0 @ X0)
% 6.26/6.47          | ~ (v1_xboole_0 @ X1))),
% 6.26/6.47      inference('sup+', [status(thm)], ['33', '41'])).
% 6.26/6.47  thf('43', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('44', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 6.26/6.47      inference('sup-', [status(thm)], ['42', '43'])).
% 6.26/6.47  thf('45', plain,
% 6.26/6.47      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 6.26/6.47      inference('sup-', [status(thm)], ['26', '44'])).
% 6.26/6.47  thf('46', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.26/6.47         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.26/6.47      inference('sup+', [status(thm)], ['11', '13'])).
% 6.26/6.47  thf('47', plain,
% 6.26/6.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.26/6.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.26/6.47  thf('48', plain,
% 6.26/6.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('49', plain,
% 6.26/6.47      (![X16 : $i, X17 : $i]:
% 6.26/6.47         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 6.26/6.47      inference('cnf', [status(esa)], [t3_subset])).
% 6.26/6.47  thf('50', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 6.26/6.47      inference('sup-', [status(thm)], ['48', '49'])).
% 6.26/6.47  thf('51', plain,
% 6.26/6.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.26/6.47         (~ (r2_hidden @ X3 @ X4)
% 6.26/6.47          | (r2_hidden @ X3 @ X5)
% 6.26/6.47          | ~ (r1_tarski @ X4 @ X5))),
% 6.26/6.47      inference('cnf', [status(esa)], [d3_tarski])).
% 6.26/6.47  thf('52', plain,
% 6.26/6.47      (![X0 : $i]:
% 6.26/6.47         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.26/6.47          | ~ (r2_hidden @ X0 @ sk_D))),
% 6.26/6.47      inference('sup-', [status(thm)], ['50', '51'])).
% 6.26/6.47  thf('53', plain,
% 6.26/6.47      (((v1_xboole_0 @ sk_D)
% 6.26/6.47        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('sup-', [status(thm)], ['47', '52'])).
% 6.26/6.47  thf('54', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.26/6.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.26/6.47  thf('55', plain,
% 6.26/6.47      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('sup-', [status(thm)], ['53', '54'])).
% 6.26/6.47  thf('56', plain,
% 6.26/6.47      (![X0 : $i]:
% 6.26/6.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.26/6.47          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 6.26/6.47          | (v1_xboole_0 @ sk_D))),
% 6.26/6.47      inference('sup-', [status(thm)], ['46', '55'])).
% 6.26/6.47  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.26/6.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.26/6.47  thf('58', plain,
% 6.26/6.47      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 6.26/6.47      inference('demod', [status(thm)], ['56', '57'])).
% 6.26/6.47  thf('59', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 6.26/6.47      inference('clc', [status(thm)], ['45', '58'])).
% 6.26/6.47  thf('60', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 6.26/6.47      inference('demod', [status(thm)], ['10', '59'])).
% 6.26/6.47  thf('61', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.26/6.47      inference('demod', [status(thm)], ['7', '60'])).
% 6.26/6.47  thf('62', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('63', plain,
% 6.26/6.47      (![X33 : $i, X34 : $i, X35 : $i]:
% 6.26/6.47         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 6.26/6.47          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 6.26/6.47          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.26/6.47  thf('64', plain,
% 6.26/6.47      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.26/6.47        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 6.26/6.47      inference('sup-', [status(thm)], ['62', '63'])).
% 6.26/6.47  thf('65', plain,
% 6.26/6.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('66', plain,
% 6.26/6.47      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.26/6.47         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 6.26/6.47          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 6.26/6.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.26/6.47  thf('67', plain,
% 6.26/6.47      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 6.26/6.47      inference('sup-', [status(thm)], ['65', '66'])).
% 6.26/6.47  thf('68', plain,
% 6.26/6.47      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.26/6.47        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.26/6.47      inference('demod', [status(thm)], ['64', '67'])).
% 6.26/6.47  thf('69', plain,
% 6.26/6.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('70', plain,
% 6.26/6.47      (![X36 : $i, X37 : $i, X38 : $i]:
% 6.26/6.47         (~ (zip_tseitin_0 @ X36 @ X37)
% 6.26/6.47          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 6.26/6.47          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.26/6.47  thf('71', plain,
% 6.26/6.47      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.26/6.47        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.26/6.47      inference('sup-', [status(thm)], ['69', '70'])).
% 6.26/6.47  thf('72', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 6.26/6.47      inference('clc', [status(thm)], ['45', '58'])).
% 6.26/6.47  thf('73', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 6.26/6.47      inference('demod', [status(thm)], ['71', '72'])).
% 6.26/6.47  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.26/6.47      inference('demod', [status(thm)], ['68', '73'])).
% 6.26/6.47  thf(t9_funct_1, axiom,
% 6.26/6.47    (![A:$i]:
% 6.26/6.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.26/6.47       ( ![B:$i]:
% 6.26/6.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.26/6.47           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.26/6.47               ( ![C:$i]:
% 6.26/6.47                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 6.26/6.47                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 6.26/6.47             ( ( A ) = ( B ) ) ) ) ) ))).
% 6.26/6.47  thf('75', plain,
% 6.26/6.47      (![X19 : $i, X20 : $i]:
% 6.26/6.47         (~ (v1_relat_1 @ X19)
% 6.26/6.47          | ~ (v1_funct_1 @ X19)
% 6.26/6.47          | ((X20) = (X19))
% 6.26/6.47          | (r2_hidden @ (sk_C_1 @ X19 @ X20) @ (k1_relat_1 @ X20))
% 6.26/6.47          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 6.26/6.47          | ~ (v1_funct_1 @ X20)
% 6.26/6.47          | ~ (v1_relat_1 @ X20))),
% 6.26/6.47      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.26/6.47  thf('76', plain,
% 6.26/6.47      (![X0 : $i]:
% 6.26/6.47         (((sk_A) != (k1_relat_1 @ X0))
% 6.26/6.47          | ~ (v1_relat_1 @ sk_C_2)
% 6.26/6.47          | ~ (v1_funct_1 @ sk_C_2)
% 6.26/6.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 6.26/6.47          | ((sk_C_2) = (X0))
% 6.26/6.47          | ~ (v1_funct_1 @ X0)
% 6.26/6.47          | ~ (v1_relat_1 @ X0))),
% 6.26/6.47      inference('sup-', [status(thm)], ['74', '75'])).
% 6.26/6.47  thf('77', plain,
% 6.26/6.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf(cc1_relset_1, axiom,
% 6.26/6.47    (![A:$i,B:$i,C:$i]:
% 6.26/6.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.26/6.47       ( v1_relat_1 @ C ) ))).
% 6.26/6.47  thf('78', plain,
% 6.26/6.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.26/6.47         ((v1_relat_1 @ X21)
% 6.26/6.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 6.26/6.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.26/6.47  thf('79', plain, ((v1_relat_1 @ sk_C_2)),
% 6.26/6.47      inference('sup-', [status(thm)], ['77', '78'])).
% 6.26/6.47  thf('80', plain, ((v1_funct_1 @ sk_C_2)),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('81', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.26/6.47      inference('demod', [status(thm)], ['68', '73'])).
% 6.26/6.47  thf('82', plain,
% 6.26/6.47      (![X0 : $i]:
% 6.26/6.47         (((sk_A) != (k1_relat_1 @ X0))
% 6.26/6.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 6.26/6.47          | ((sk_C_2) = (X0))
% 6.26/6.47          | ~ (v1_funct_1 @ X0)
% 6.26/6.47          | ~ (v1_relat_1 @ X0))),
% 6.26/6.47      inference('demod', [status(thm)], ['76', '79', '80', '81'])).
% 6.26/6.47  thf('83', plain,
% 6.26/6.47      ((((sk_A) != (sk_A))
% 6.26/6.47        | ~ (v1_relat_1 @ sk_D)
% 6.26/6.47        | ~ (v1_funct_1 @ sk_D)
% 6.26/6.47        | ((sk_C_2) = (sk_D))
% 6.26/6.47        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 6.26/6.47      inference('sup-', [status(thm)], ['61', '82'])).
% 6.26/6.47  thf('84', plain,
% 6.26/6.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('85', plain,
% 6.26/6.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.26/6.47         ((v1_relat_1 @ X21)
% 6.26/6.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 6.26/6.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.26/6.47  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 6.26/6.47      inference('sup-', [status(thm)], ['84', '85'])).
% 6.26/6.47  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('88', plain,
% 6.26/6.47      ((((sk_A) != (sk_A))
% 6.26/6.47        | ((sk_C_2) = (sk_D))
% 6.26/6.47        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 6.26/6.47      inference('demod', [status(thm)], ['83', '86', '87'])).
% 6.26/6.47  thf('89', plain,
% 6.26/6.47      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 6.26/6.47      inference('simplify', [status(thm)], ['88'])).
% 6.26/6.47  thf('90', plain,
% 6.26/6.47      (![X39 : $i]:
% 6.26/6.47         (((k1_funct_1 @ sk_C_2 @ X39) = (k1_funct_1 @ sk_D @ X39))
% 6.26/6.47          | ~ (r2_hidden @ X39 @ sk_A))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('91', plain,
% 6.26/6.47      ((((sk_C_2) = (sk_D))
% 6.26/6.47        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.26/6.47            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 6.26/6.47      inference('sup-', [status(thm)], ['89', '90'])).
% 6.26/6.47  thf('92', plain,
% 6.26/6.47      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.26/6.47         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 6.26/6.47      inference('condensation', [status(thm)], ['91'])).
% 6.26/6.47  thf('93', plain,
% 6.26/6.47      (![X19 : $i, X20 : $i]:
% 6.26/6.47         (~ (v1_relat_1 @ X19)
% 6.26/6.47          | ~ (v1_funct_1 @ X19)
% 6.26/6.47          | ((X20) = (X19))
% 6.26/6.47          | ((k1_funct_1 @ X20 @ (sk_C_1 @ X19 @ X20))
% 6.26/6.47              != (k1_funct_1 @ X19 @ (sk_C_1 @ X19 @ X20)))
% 6.26/6.47          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 6.26/6.47          | ~ (v1_funct_1 @ X20)
% 6.26/6.47          | ~ (v1_relat_1 @ X20))),
% 6.26/6.47      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.26/6.47  thf('94', plain,
% 6.26/6.47      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.26/6.47          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 6.26/6.47        | ~ (v1_relat_1 @ sk_C_2)
% 6.26/6.47        | ~ (v1_funct_1 @ sk_C_2)
% 6.26/6.47        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 6.26/6.47        | ((sk_C_2) = (sk_D))
% 6.26/6.47        | ~ (v1_funct_1 @ sk_D)
% 6.26/6.47        | ~ (v1_relat_1 @ sk_D))),
% 6.26/6.47      inference('sup-', [status(thm)], ['92', '93'])).
% 6.26/6.47  thf('95', plain, ((v1_relat_1 @ sk_C_2)),
% 6.26/6.47      inference('sup-', [status(thm)], ['77', '78'])).
% 6.26/6.47  thf('96', plain, ((v1_funct_1 @ sk_C_2)),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('97', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.26/6.47      inference('demod', [status(thm)], ['68', '73'])).
% 6.26/6.47  thf('98', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.26/6.47      inference('demod', [status(thm)], ['7', '60'])).
% 6.26/6.47  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 6.26/6.47      inference('sup-', [status(thm)], ['84', '85'])).
% 6.26/6.47  thf('101', plain,
% 6.26/6.47      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.26/6.47          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 6.26/6.47        | ((sk_A) != (sk_A))
% 6.26/6.47        | ((sk_C_2) = (sk_D)))),
% 6.26/6.47      inference('demod', [status(thm)],
% 6.26/6.47                ['94', '95', '96', '97', '98', '99', '100'])).
% 6.26/6.47  thf('102', plain, (((sk_C_2) = (sk_D))),
% 6.26/6.47      inference('simplify', [status(thm)], ['101'])).
% 6.26/6.47  thf('103', plain,
% 6.26/6.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.26/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.26/6.47  thf('104', plain,
% 6.26/6.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.26/6.47         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 6.26/6.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 6.26/6.47      inference('condensation', [status(thm)], ['38'])).
% 6.26/6.47  thf('105', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 6.26/6.47      inference('sup-', [status(thm)], ['103', '104'])).
% 6.26/6.47  thf('106', plain, ($false),
% 6.26/6.47      inference('demod', [status(thm)], ['0', '102', '105'])).
% 6.26/6.47  
% 6.26/6.47  % SZS output end Refutation
% 6.26/6.47  
% 6.26/6.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
