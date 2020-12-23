%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pWO2aXssFW

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:33 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 423 expanded)
%              Number of leaves         :   36 ( 142 expanded)
%              Depth                    :   21
%              Number of atoms          :  895 (6110 expanded)
%              Number of equality atoms :   64 ( 239 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_C_3 ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_B_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_2 @ X0 ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('37',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['10','36'])).

thf('38',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_2 @ X0 ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('50',plain,(
    zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['45','50'])).

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

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ sk_C_3 ) )
      | ( sk_C_3 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ sk_A )
      | ( sk_C_3 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','56','57','58'])).

thf('60',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_3 = sk_D )
    | ( r2_hidden @ ( sk_C_2 @ sk_D @ sk_C_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_3 = sk_D )
    | ( r2_hidden @ ( sk_C_2 @ sk_D @ sk_C_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_D @ sk_C_3 ) @ sk_A )
    | ( sk_C_3 = sk_D ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X38: $i] :
      ( ( ( k1_funct_1 @ sk_C_3 @ X38 )
        = ( k1_funct_1 @ sk_D @ X38 ) )
      | ~ ( r2_hidden @ X38 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_C_3 = sk_D )
    | ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) ),
    inference(condensation,[status(thm)],['68'])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( ( k1_funct_1 @ X13 @ ( sk_C_2 @ X12 @ X13 ) )
       != ( k1_funct_1 @ X12 @ ( sk_C_2 @ X12 @ X13 ) ) )
      | ( ( k1_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('71',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
     != ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_3 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('75',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','37'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['61','62'])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
     != ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_3 = sk_D ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77'])).

thf('79',plain,(
    sk_C_3 = sk_D ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_C_3 ),
    inference('sup-',[status(thm)],['11','13'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pWO2aXssFW
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 09:21:23 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 1.39/1.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.39/1.60  % Solved by: fo/fo7.sh
% 1.39/1.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.39/1.60  % done 1243 iterations in 1.164s
% 1.39/1.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.39/1.60  % SZS output start Refutation
% 1.39/1.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.39/1.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.39/1.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.39/1.60  thf(sk_D_type, type, sk_D: $i).
% 1.39/1.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.39/1.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.39/1.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.39/1.60  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.39/1.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.39/1.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.39/1.60  thf(sk_C_3_type, type, sk_C_3: $i).
% 1.39/1.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.39/1.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.39/1.60  thf(sk_A_type, type, sk_A: $i).
% 1.39/1.60  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.39/1.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.39/1.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.39/1.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.39/1.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.39/1.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.39/1.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.39/1.60  thf(t18_funct_2, conjecture,
% 1.39/1.60    (![A:$i,B:$i,C:$i]:
% 1.39/1.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.39/1.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.39/1.60       ( ![D:$i]:
% 1.39/1.60         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.39/1.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.39/1.60           ( ( ![E:$i]:
% 1.39/1.60               ( ( r2_hidden @ E @ A ) =>
% 1.39/1.60                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.39/1.60             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 1.39/1.60  thf(zf_stmt_0, negated_conjecture,
% 1.39/1.60    (~( ![A:$i,B:$i,C:$i]:
% 1.39/1.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.39/1.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.39/1.60          ( ![D:$i]:
% 1.39/1.60            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.39/1.60                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.39/1.60              ( ( ![E:$i]:
% 1.39/1.60                  ( ( r2_hidden @ E @ A ) =>
% 1.39/1.60                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.39/1.60                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 1.39/1.60    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 1.39/1.60  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf(d1_funct_2, axiom,
% 1.39/1.60    (![A:$i,B:$i,C:$i]:
% 1.39/1.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.39/1.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.39/1.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.39/1.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.39/1.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.39/1.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.39/1.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.39/1.60  thf(zf_stmt_1, axiom,
% 1.39/1.60    (![C:$i,B:$i,A:$i]:
% 1.39/1.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.39/1.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.39/1.60  thf('2', plain,
% 1.39/1.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.39/1.60         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 1.39/1.60          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 1.39/1.60          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.39/1.60  thf('3', plain,
% 1.39/1.60      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 1.39/1.60        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['1', '2'])).
% 1.39/1.60  thf('4', plain,
% 1.39/1.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf(redefinition_k1_relset_1, axiom,
% 1.39/1.60    (![A:$i,B:$i,C:$i]:
% 1.39/1.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.39/1.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.39/1.60  thf('5', plain,
% 1.39/1.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.39/1.60         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.39/1.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.39/1.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.39/1.60  thf('6', plain,
% 1.39/1.60      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.39/1.60      inference('sup-', [status(thm)], ['4', '5'])).
% 1.39/1.60  thf('7', plain,
% 1.39/1.60      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 1.39/1.60        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.39/1.60      inference('demod', [status(thm)], ['3', '6'])).
% 1.39/1.60  thf('8', plain,
% 1.39/1.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.39/1.60  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.39/1.60  thf(zf_stmt_4, axiom,
% 1.39/1.60    (![B:$i,A:$i]:
% 1.39/1.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.39/1.60       ( zip_tseitin_0 @ B @ A ) ))).
% 1.39/1.60  thf(zf_stmt_5, axiom,
% 1.39/1.60    (![A:$i,B:$i,C:$i]:
% 1.39/1.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.39/1.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.39/1.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.39/1.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.39/1.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.39/1.60  thf('9', plain,
% 1.39/1.60      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.39/1.60         (~ (zip_tseitin_0 @ X35 @ X36)
% 1.39/1.60          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 1.39/1.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.39/1.60  thf('10', plain,
% 1.39/1.60      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 1.39/1.60        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 1.39/1.60      inference('sup-', [status(thm)], ['8', '9'])).
% 1.39/1.60  thf('11', plain,
% 1.39/1.60      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf(reflexivity_r2_relset_1, axiom,
% 1.39/1.60    (![A:$i,B:$i,C:$i,D:$i]:
% 1.39/1.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.39/1.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.39/1.60       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 1.39/1.60  thf('12', plain,
% 1.39/1.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.39/1.60         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 1.39/1.60          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.39/1.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.39/1.60      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 1.39/1.60  thf('13', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.60         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.39/1.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.39/1.60      inference('condensation', [status(thm)], ['12'])).
% 1.39/1.60  thf('14', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_C_3)),
% 1.39/1.60      inference('sup-', [status(thm)], ['11', '13'])).
% 1.39/1.60  thf('15', plain,
% 1.39/1.60      (![X30 : $i, X31 : $i]:
% 1.39/1.60         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.39/1.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.39/1.60  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.39/1.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.39/1.60  thf('17', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.39/1.60      inference('sup+', [status(thm)], ['15', '16'])).
% 1.39/1.60  thf('18', plain,
% 1.39/1.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf(cc4_relset_1, axiom,
% 1.39/1.60    (![A:$i,B:$i]:
% 1.39/1.60     ( ( v1_xboole_0 @ A ) =>
% 1.39/1.60       ( ![C:$i]:
% 1.39/1.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.39/1.60           ( v1_xboole_0 @ C ) ) ) ))).
% 1.39/1.60  thf('19', plain,
% 1.39/1.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.39/1.60         (~ (v1_xboole_0 @ X20)
% 1.39/1.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 1.39/1.60          | (v1_xboole_0 @ X21))),
% 1.39/1.60      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.39/1.60  thf('20', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_2))),
% 1.39/1.60      inference('sup-', [status(thm)], ['18', '19'])).
% 1.39/1.60  thf('21', plain,
% 1.39/1.60      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_D))),
% 1.39/1.60      inference('sup-', [status(thm)], ['17', '20'])).
% 1.39/1.60  thf(t2_tarski, axiom,
% 1.39/1.60    (![A:$i,B:$i]:
% 1.39/1.60     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 1.39/1.60       ( ( A ) = ( B ) ) ))).
% 1.39/1.60  thf('22', plain,
% 1.39/1.60      (![X7 : $i, X8 : $i]:
% 1.39/1.60         (((X8) = (X7))
% 1.39/1.60          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 1.39/1.60          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X8))),
% 1.39/1.60      inference('cnf', [status(esa)], [t2_tarski])).
% 1.39/1.60  thf(d1_xboole_0, axiom,
% 1.39/1.60    (![A:$i]:
% 1.39/1.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.39/1.60  thf('23', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.39/1.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.39/1.60  thf('24', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 1.39/1.60          | ((X1) = (X0))
% 1.39/1.60          | ~ (v1_xboole_0 @ X0))),
% 1.39/1.60      inference('sup-', [status(thm)], ['22', '23'])).
% 1.39/1.60  thf('25', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.39/1.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.39/1.60  thf('26', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 1.39/1.60      inference('sup-', [status(thm)], ['24', '25'])).
% 1.39/1.60  thf('27', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         ((zip_tseitin_0 @ sk_B_2 @ X1)
% 1.39/1.60          | ~ (v1_xboole_0 @ X0)
% 1.39/1.60          | ((X0) = (sk_D)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['21', '26'])).
% 1.39/1.60  thf('28', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('29', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ X0)
% 1.39/1.60          | ~ (v1_xboole_0 @ X0)
% 1.39/1.60          | (zip_tseitin_0 @ sk_B_2 @ X1))),
% 1.39/1.60      inference('sup-', [status(thm)], ['27', '28'])).
% 1.39/1.60  thf('30', plain,
% 1.39/1.60      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | ~ (v1_xboole_0 @ sk_C_3))),
% 1.39/1.60      inference('sup-', [status(thm)], ['14', '29'])).
% 1.39/1.60  thf('31', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.39/1.60      inference('sup+', [status(thm)], ['15', '16'])).
% 1.39/1.60  thf('32', plain,
% 1.39/1.60      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('33', plain,
% 1.39/1.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.39/1.60         (~ (v1_xboole_0 @ X20)
% 1.39/1.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 1.39/1.60          | (v1_xboole_0 @ X21))),
% 1.39/1.60      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.39/1.60  thf('34', plain, (((v1_xboole_0 @ sk_C_3) | ~ (v1_xboole_0 @ sk_B_2))),
% 1.39/1.60      inference('sup-', [status(thm)], ['32', '33'])).
% 1.39/1.60  thf('35', plain,
% 1.39/1.60      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_C_3))),
% 1.39/1.60      inference('sup-', [status(thm)], ['31', '34'])).
% 1.39/1.60  thf('36', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_2 @ X0)),
% 1.39/1.60      inference('clc', [status(thm)], ['30', '35'])).
% 1.39/1.60  thf('37', plain, ((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)),
% 1.39/1.60      inference('demod', [status(thm)], ['10', '36'])).
% 1.39/1.60  thf('38', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.39/1.60      inference('demod', [status(thm)], ['7', '37'])).
% 1.39/1.60  thf('39', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('40', plain,
% 1.39/1.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.39/1.60         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 1.39/1.60          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 1.39/1.60          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.39/1.60  thf('41', plain,
% 1.39/1.60      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A)
% 1.39/1.60        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_3)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['39', '40'])).
% 1.39/1.60  thf('42', plain,
% 1.39/1.60      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('43', plain,
% 1.39/1.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.39/1.60         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.39/1.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.39/1.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.39/1.60  thf('44', plain,
% 1.39/1.60      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 1.39/1.60      inference('sup-', [status(thm)], ['42', '43'])).
% 1.39/1.60  thf('45', plain,
% 1.39/1.60      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A)
% 1.39/1.60        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.39/1.60      inference('demod', [status(thm)], ['41', '44'])).
% 1.39/1.60  thf('46', plain,
% 1.39/1.60      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('47', plain,
% 1.39/1.60      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.39/1.60         (~ (zip_tseitin_0 @ X35 @ X36)
% 1.39/1.60          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 1.39/1.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.39/1.60  thf('48', plain,
% 1.39/1.60      (((zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A)
% 1.39/1.60        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 1.39/1.60      inference('sup-', [status(thm)], ['46', '47'])).
% 1.39/1.60  thf('49', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_2 @ X0)),
% 1.39/1.60      inference('clc', [status(thm)], ['30', '35'])).
% 1.39/1.60  thf('50', plain, ((zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A)),
% 1.39/1.60      inference('demod', [status(thm)], ['48', '49'])).
% 1.39/1.60  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 1.39/1.60      inference('demod', [status(thm)], ['45', '50'])).
% 1.39/1.60  thf(t9_funct_1, axiom,
% 1.39/1.60    (![A:$i]:
% 1.39/1.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.39/1.60       ( ![B:$i]:
% 1.39/1.60         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.39/1.60           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.39/1.60               ( ![C:$i]:
% 1.39/1.60                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.39/1.60                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.39/1.60             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.39/1.60  thf('52', plain,
% 1.39/1.60      (![X12 : $i, X13 : $i]:
% 1.39/1.60         (~ (v1_relat_1 @ X12)
% 1.39/1.60          | ~ (v1_funct_1 @ X12)
% 1.39/1.60          | ((X13) = (X12))
% 1.39/1.60          | (r2_hidden @ (sk_C_2 @ X12 @ X13) @ (k1_relat_1 @ X13))
% 1.39/1.60          | ((k1_relat_1 @ X13) != (k1_relat_1 @ X12))
% 1.39/1.60          | ~ (v1_funct_1 @ X13)
% 1.39/1.60          | ~ (v1_relat_1 @ X13))),
% 1.39/1.60      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.39/1.60  thf('53', plain,
% 1.39/1.60      (![X0 : $i]:
% 1.39/1.60         (((sk_A) != (k1_relat_1 @ X0))
% 1.39/1.60          | ~ (v1_relat_1 @ sk_C_3)
% 1.39/1.60          | ~ (v1_funct_1 @ sk_C_3)
% 1.39/1.60          | (r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ (k1_relat_1 @ sk_C_3))
% 1.39/1.60          | ((sk_C_3) = (X0))
% 1.39/1.60          | ~ (v1_funct_1 @ X0)
% 1.39/1.60          | ~ (v1_relat_1 @ X0))),
% 1.39/1.60      inference('sup-', [status(thm)], ['51', '52'])).
% 1.39/1.60  thf('54', plain,
% 1.39/1.60      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf(cc1_relset_1, axiom,
% 1.39/1.60    (![A:$i,B:$i,C:$i]:
% 1.39/1.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.39/1.60       ( v1_relat_1 @ C ) ))).
% 1.39/1.60  thf('55', plain,
% 1.39/1.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.39/1.60         ((v1_relat_1 @ X14)
% 1.39/1.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.39/1.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.39/1.60  thf('56', plain, ((v1_relat_1 @ sk_C_3)),
% 1.39/1.60      inference('sup-', [status(thm)], ['54', '55'])).
% 1.39/1.60  thf('57', plain, ((v1_funct_1 @ sk_C_3)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 1.39/1.60      inference('demod', [status(thm)], ['45', '50'])).
% 1.39/1.60  thf('59', plain,
% 1.39/1.60      (![X0 : $i]:
% 1.39/1.60         (((sk_A) != (k1_relat_1 @ X0))
% 1.39/1.60          | (r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ sk_A)
% 1.39/1.60          | ((sk_C_3) = (X0))
% 1.39/1.60          | ~ (v1_funct_1 @ X0)
% 1.39/1.60          | ~ (v1_relat_1 @ X0))),
% 1.39/1.60      inference('demod', [status(thm)], ['53', '56', '57', '58'])).
% 1.39/1.60  thf('60', plain,
% 1.39/1.60      ((((sk_A) != (sk_A))
% 1.39/1.60        | ~ (v1_relat_1 @ sk_D)
% 1.39/1.60        | ~ (v1_funct_1 @ sk_D)
% 1.39/1.60        | ((sk_C_3) = (sk_D))
% 1.39/1.60        | (r2_hidden @ (sk_C_2 @ sk_D @ sk_C_3) @ sk_A))),
% 1.39/1.60      inference('sup-', [status(thm)], ['38', '59'])).
% 1.39/1.60  thf('61', plain,
% 1.39/1.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('62', plain,
% 1.39/1.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.39/1.60         ((v1_relat_1 @ X14)
% 1.39/1.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.39/1.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.39/1.60  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 1.39/1.60      inference('sup-', [status(thm)], ['61', '62'])).
% 1.39/1.60  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('65', plain,
% 1.39/1.60      ((((sk_A) != (sk_A))
% 1.39/1.60        | ((sk_C_3) = (sk_D))
% 1.39/1.60        | (r2_hidden @ (sk_C_2 @ sk_D @ sk_C_3) @ sk_A))),
% 1.39/1.60      inference('demod', [status(thm)], ['60', '63', '64'])).
% 1.39/1.60  thf('66', plain,
% 1.39/1.60      (((r2_hidden @ (sk_C_2 @ sk_D @ sk_C_3) @ sk_A) | ((sk_C_3) = (sk_D)))),
% 1.39/1.60      inference('simplify', [status(thm)], ['65'])).
% 1.39/1.60  thf('67', plain,
% 1.39/1.60      (![X38 : $i]:
% 1.39/1.60         (((k1_funct_1 @ sk_C_3 @ X38) = (k1_funct_1 @ sk_D @ X38))
% 1.39/1.60          | ~ (r2_hidden @ X38 @ sk_A))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('68', plain,
% 1.39/1.60      ((((sk_C_3) = (sk_D))
% 1.39/1.60        | ((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 1.39/1.60            = (k1_funct_1 @ sk_D @ (sk_C_2 @ sk_D @ sk_C_3))))),
% 1.39/1.60      inference('sup-', [status(thm)], ['66', '67'])).
% 1.39/1.60  thf('69', plain,
% 1.39/1.60      (((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 1.39/1.60         = (k1_funct_1 @ sk_D @ (sk_C_2 @ sk_D @ sk_C_3)))),
% 1.39/1.60      inference('condensation', [status(thm)], ['68'])).
% 1.39/1.60  thf('70', plain,
% 1.39/1.60      (![X12 : $i, X13 : $i]:
% 1.39/1.60         (~ (v1_relat_1 @ X12)
% 1.39/1.60          | ~ (v1_funct_1 @ X12)
% 1.39/1.60          | ((X13) = (X12))
% 1.39/1.60          | ((k1_funct_1 @ X13 @ (sk_C_2 @ X12 @ X13))
% 1.39/1.60              != (k1_funct_1 @ X12 @ (sk_C_2 @ X12 @ X13)))
% 1.39/1.60          | ((k1_relat_1 @ X13) != (k1_relat_1 @ X12))
% 1.39/1.60          | ~ (v1_funct_1 @ X13)
% 1.39/1.60          | ~ (v1_relat_1 @ X13))),
% 1.39/1.60      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.39/1.60  thf('71', plain,
% 1.39/1.60      ((((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 1.39/1.60          != (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3)))
% 1.39/1.60        | ~ (v1_relat_1 @ sk_C_3)
% 1.39/1.60        | ~ (v1_funct_1 @ sk_C_3)
% 1.39/1.60        | ((k1_relat_1 @ sk_C_3) != (k1_relat_1 @ sk_D))
% 1.39/1.60        | ((sk_C_3) = (sk_D))
% 1.39/1.60        | ~ (v1_funct_1 @ sk_D)
% 1.39/1.60        | ~ (v1_relat_1 @ sk_D))),
% 1.39/1.60      inference('sup-', [status(thm)], ['69', '70'])).
% 1.39/1.60  thf('72', plain, ((v1_relat_1 @ sk_C_3)),
% 1.39/1.60      inference('sup-', [status(thm)], ['54', '55'])).
% 1.39/1.60  thf('73', plain, ((v1_funct_1 @ sk_C_3)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 1.39/1.60      inference('demod', [status(thm)], ['45', '50'])).
% 1.39/1.60  thf('75', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.39/1.60      inference('demod', [status(thm)], ['7', '37'])).
% 1.39/1.60  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 1.39/1.60      inference('sup-', [status(thm)], ['61', '62'])).
% 1.39/1.60  thf('78', plain,
% 1.39/1.60      ((((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 1.39/1.60          != (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3)))
% 1.39/1.60        | ((sk_A) != (sk_A))
% 1.39/1.60        | ((sk_C_3) = (sk_D)))),
% 1.39/1.60      inference('demod', [status(thm)],
% 1.39/1.60                ['71', '72', '73', '74', '75', '76', '77'])).
% 1.39/1.60  thf('79', plain, (((sk_C_3) = (sk_D))),
% 1.39/1.60      inference('simplify', [status(thm)], ['78'])).
% 1.39/1.60  thf('80', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_C_3)),
% 1.39/1.60      inference('sup-', [status(thm)], ['11', '13'])).
% 1.39/1.60  thf('81', plain, ($false),
% 1.39/1.60      inference('demod', [status(thm)], ['0', '79', '80'])).
% 1.39/1.60  
% 1.39/1.60  % SZS output end Refutation
% 1.39/1.60  
% 1.39/1.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
