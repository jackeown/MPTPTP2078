%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A3XfqPbPXz

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:28 EST 2020

% Result     : Theorem 3.80s
% Output     : Refutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 480 expanded)
%              Number of leaves         :   41 ( 159 expanded)
%              Depth                    :   22
%              Number of atoms          :  996 (7097 expanded)
%              Number of equality atoms :   64 ( 268 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
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
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('33',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','32'])).

thf('34',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('46',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

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

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','52','53','54'])).

thf('56',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','59','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('69',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['67','68'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('72',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('77',plain,(
    ! [X37: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X37 )
        = ( k1_funct_1 @ sk_D @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['78'])).

thf('80',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( ( k1_funct_1 @ X12 @ ( sk_C @ X11 @ X12 ) )
       != ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ X12 ) ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('81',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('83',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('85',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','33'])).

thf('86',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('88',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['81','82','83','84','85','86','87'])).

thf('89',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['12'])).

thf('92',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','89','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A3XfqPbPXz
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.80/3.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.80/3.99  % Solved by: fo/fo7.sh
% 3.80/3.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.80/3.99  % done 3771 iterations in 3.511s
% 3.80/3.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.80/3.99  % SZS output start Refutation
% 3.80/3.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.80/3.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.80/3.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.80/3.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.80/3.99  thf(sk_A_type, type, sk_A: $i).
% 3.80/3.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.80/3.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.80/3.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.80/3.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.80/3.99  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.80/3.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.80/3.99  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.80/3.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.80/3.99  thf(sk_B_type, type, sk_B: $i).
% 3.80/3.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.80/3.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.80/3.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.80/3.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.80/3.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.80/3.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.80/3.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.80/3.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.80/3.99  thf(sk_D_type, type, sk_D: $i).
% 3.80/3.99  thf(t113_funct_2, conjecture,
% 3.80/3.99    (![A:$i,B:$i,C:$i]:
% 3.80/3.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.80/3.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/3.99       ( ![D:$i]:
% 3.80/3.99         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.80/3.99             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/3.99           ( ( ![E:$i]:
% 3.80/3.99               ( ( m1_subset_1 @ E @ A ) =>
% 3.80/3.99                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.80/3.99             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.80/3.99  thf(zf_stmt_0, negated_conjecture,
% 3.80/3.99    (~( ![A:$i,B:$i,C:$i]:
% 3.80/3.99        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.80/3.99            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/3.99          ( ![D:$i]:
% 3.80/3.99            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.80/3.99                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/3.99              ( ( ![E:$i]:
% 3.80/3.99                  ( ( m1_subset_1 @ E @ A ) =>
% 3.80/3.99                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.80/3.99                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.80/3.99    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 3.80/3.99  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 3.80/3.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/3.99  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 3.80/3.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/3.99  thf(d1_funct_2, axiom,
% 3.80/3.99    (![A:$i,B:$i,C:$i]:
% 3.80/3.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/3.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.80/3.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.80/4.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.80/4.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.80/4.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.80/4.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.80/4.00  thf(zf_stmt_1, axiom,
% 3.80/4.00    (![C:$i,B:$i,A:$i]:
% 3.80/4.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.80/4.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.80/4.00  thf('2', plain,
% 3.80/4.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.80/4.00         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 3.80/4.00          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 3.80/4.00          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.80/4.00  thf('3', plain,
% 3.80/4.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 3.80/4.00        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 3.80/4.00      inference('sup-', [status(thm)], ['1', '2'])).
% 3.80/4.00  thf('4', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf(redefinition_k1_relset_1, axiom,
% 3.80/4.00    (![A:$i,B:$i,C:$i]:
% 3.80/4.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.80/4.00  thf('5', plain,
% 3.80/4.00      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.80/4.00         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 3.80/4.00          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.80/4.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.80/4.00  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.80/4.00      inference('sup-', [status(thm)], ['4', '5'])).
% 3.80/4.00  thf('7', plain,
% 3.80/4.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.80/4.00      inference('demod', [status(thm)], ['3', '6'])).
% 3.80/4.00  thf('8', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.80/4.00  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.80/4.00  thf(zf_stmt_4, axiom,
% 3.80/4.00    (![B:$i,A:$i]:
% 3.80/4.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.80/4.00       ( zip_tseitin_0 @ B @ A ) ))).
% 3.80/4.00  thf(zf_stmt_5, axiom,
% 3.80/4.00    (![A:$i,B:$i,C:$i]:
% 3.80/4.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.80/4.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.80/4.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.80/4.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.80/4.00  thf('9', plain,
% 3.80/4.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.80/4.00         (~ (zip_tseitin_0 @ X34 @ X35)
% 3.80/4.00          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 3.80/4.00          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.80/4.00  thf('10', plain,
% 3.80/4.00      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.80/4.00      inference('sup-', [status(thm)], ['8', '9'])).
% 3.80/4.00  thf('11', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf(reflexivity_r2_relset_1, axiom,
% 3.80/4.00    (![A:$i,B:$i,C:$i,D:$i]:
% 3.80/4.00     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.80/4.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/4.00       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 3.80/4.00  thf('12', plain,
% 3.80/4.00      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.80/4.00         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 3.80/4.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.80/4.00          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.80/4.00      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 3.80/4.00  thf('13', plain,
% 3.80/4.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.00         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.80/4.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.80/4.00      inference('condensation', [status(thm)], ['12'])).
% 3.80/4.00  thf('14', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 3.80/4.00      inference('sup-', [status(thm)], ['11', '13'])).
% 3.80/4.00  thf('15', plain,
% 3.80/4.00      (![X29 : $i, X30 : $i]:
% 3.80/4.00         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.80/4.00  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.80/4.00  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.80/4.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.80/4.00  thf('17', plain,
% 3.80/4.00      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.80/4.00      inference('sup+', [status(thm)], ['15', '16'])).
% 3.80/4.00  thf('18', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf(cc4_relset_1, axiom,
% 3.80/4.00    (![A:$i,B:$i]:
% 3.80/4.00     ( ( v1_xboole_0 @ A ) =>
% 3.80/4.00       ( ![C:$i]:
% 3.80/4.00         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 3.80/4.00           ( v1_xboole_0 @ C ) ) ) ))).
% 3.80/4.00  thf('19', plain,
% 3.80/4.00      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.80/4.00         (~ (v1_xboole_0 @ X19)
% 3.80/4.00          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 3.80/4.00          | (v1_xboole_0 @ X20))),
% 3.80/4.00      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.80/4.00  thf('20', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B))),
% 3.80/4.00      inference('sup-', [status(thm)], ['18', '19'])).
% 3.80/4.00  thf('21', plain,
% 3.80/4.00      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 3.80/4.00      inference('sup-', [status(thm)], ['17', '20'])).
% 3.80/4.00  thf(t8_boole, axiom,
% 3.80/4.00    (![A:$i,B:$i]:
% 3.80/4.00     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.80/4.00  thf('22', plain,
% 3.80/4.00      (![X0 : $i, X1 : $i]:
% 3.80/4.00         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.80/4.00      inference('cnf', [status(esa)], [t8_boole])).
% 3.80/4.00  thf('23', plain,
% 3.80/4.00      (![X0 : $i, X1 : $i]:
% 3.80/4.00         ((zip_tseitin_0 @ sk_B @ X1)
% 3.80/4.00          | ((sk_C_1) = (X0))
% 3.80/4.00          | ~ (v1_xboole_0 @ X0))),
% 3.80/4.00      inference('sup-', [status(thm)], ['21', '22'])).
% 3.80/4.00  thf('24', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('25', plain,
% 3.80/4.00      (![X0 : $i, X1 : $i]:
% 3.80/4.00         (~ (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 3.80/4.00          | ~ (v1_xboole_0 @ X0)
% 3.80/4.00          | (zip_tseitin_0 @ sk_B @ X1))),
% 3.80/4.00      inference('sup-', [status(thm)], ['23', '24'])).
% 3.80/4.00  thf('26', plain,
% 3.80/4.00      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 3.80/4.00      inference('sup-', [status(thm)], ['14', '25'])).
% 3.80/4.00  thf('27', plain,
% 3.80/4.00      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.80/4.00      inference('sup+', [status(thm)], ['15', '16'])).
% 3.80/4.00  thf('28', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('29', plain,
% 3.80/4.00      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.80/4.00         (~ (v1_xboole_0 @ X19)
% 3.80/4.00          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 3.80/4.00          | (v1_xboole_0 @ X20))),
% 3.80/4.00      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.80/4.00  thf('30', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B))),
% 3.80/4.00      inference('sup-', [status(thm)], ['28', '29'])).
% 3.80/4.00  thf('31', plain,
% 3.80/4.00      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 3.80/4.00      inference('sup-', [status(thm)], ['27', '30'])).
% 3.80/4.00  thf('32', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 3.80/4.00      inference('clc', [status(thm)], ['26', '31'])).
% 3.80/4.00  thf('33', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 3.80/4.00      inference('demod', [status(thm)], ['10', '32'])).
% 3.80/4.00  thf('34', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.80/4.00      inference('demod', [status(thm)], ['7', '33'])).
% 3.80/4.00  thf('35', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('36', plain,
% 3.80/4.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.80/4.00         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 3.80/4.00          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 3.80/4.00          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.80/4.00  thf('37', plain,
% 3.80/4.00      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.80/4.00        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 3.80/4.00      inference('sup-', [status(thm)], ['35', '36'])).
% 3.80/4.00  thf('38', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('39', plain,
% 3.80/4.00      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.80/4.00         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 3.80/4.00          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.80/4.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.80/4.00  thf('40', plain,
% 3.80/4.00      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.80/4.00      inference('sup-', [status(thm)], ['38', '39'])).
% 3.80/4.00  thf('41', plain,
% 3.80/4.00      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.80/4.00        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.80/4.00      inference('demod', [status(thm)], ['37', '40'])).
% 3.80/4.00  thf('42', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('43', plain,
% 3.80/4.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.80/4.00         (~ (zip_tseitin_0 @ X34 @ X35)
% 3.80/4.00          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 3.80/4.00          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.80/4.00  thf('44', plain,
% 3.80/4.00      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.80/4.00        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.80/4.00      inference('sup-', [status(thm)], ['42', '43'])).
% 3.80/4.00  thf('45', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 3.80/4.00      inference('clc', [status(thm)], ['26', '31'])).
% 3.80/4.00  thf('46', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 3.80/4.00      inference('demod', [status(thm)], ['44', '45'])).
% 3.80/4.00  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.80/4.00      inference('demod', [status(thm)], ['41', '46'])).
% 3.80/4.00  thf(t9_funct_1, axiom,
% 3.80/4.00    (![A:$i]:
% 3.80/4.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.80/4.00       ( ![B:$i]:
% 3.80/4.00         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.80/4.00           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.80/4.00               ( ![C:$i]:
% 3.80/4.00                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.80/4.00                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.80/4.00             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.80/4.00  thf('48', plain,
% 3.80/4.00      (![X11 : $i, X12 : $i]:
% 3.80/4.00         (~ (v1_relat_1 @ X11)
% 3.80/4.00          | ~ (v1_funct_1 @ X11)
% 3.80/4.00          | ((X12) = (X11))
% 3.80/4.00          | (r2_hidden @ (sk_C @ X11 @ X12) @ (k1_relat_1 @ X12))
% 3.80/4.00          | ((k1_relat_1 @ X12) != (k1_relat_1 @ X11))
% 3.80/4.00          | ~ (v1_funct_1 @ X12)
% 3.80/4.00          | ~ (v1_relat_1 @ X12))),
% 3.80/4.00      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.80/4.00  thf('49', plain,
% 3.80/4.00      (![X0 : $i]:
% 3.80/4.00         (((sk_A) != (k1_relat_1 @ X0))
% 3.80/4.00          | ~ (v1_relat_1 @ sk_C_1)
% 3.80/4.00          | ~ (v1_funct_1 @ sk_C_1)
% 3.80/4.00          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 3.80/4.00          | ((sk_C_1) = (X0))
% 3.80/4.00          | ~ (v1_funct_1 @ X0)
% 3.80/4.00          | ~ (v1_relat_1 @ X0))),
% 3.80/4.00      inference('sup-', [status(thm)], ['47', '48'])).
% 3.80/4.00  thf('50', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf(cc1_relset_1, axiom,
% 3.80/4.00    (![A:$i,B:$i,C:$i]:
% 3.80/4.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.00       ( v1_relat_1 @ C ) ))).
% 3.80/4.00  thf('51', plain,
% 3.80/4.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.80/4.00         ((v1_relat_1 @ X13)
% 3.80/4.00          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.80/4.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.80/4.00  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 3.80/4.00      inference('sup-', [status(thm)], ['50', '51'])).
% 3.80/4.00  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.80/4.00      inference('demod', [status(thm)], ['41', '46'])).
% 3.80/4.00  thf('55', plain,
% 3.80/4.00      (![X0 : $i]:
% 3.80/4.00         (((sk_A) != (k1_relat_1 @ X0))
% 3.80/4.00          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 3.80/4.00          | ((sk_C_1) = (X0))
% 3.80/4.00          | ~ (v1_funct_1 @ X0)
% 3.80/4.00          | ~ (v1_relat_1 @ X0))),
% 3.80/4.00      inference('demod', [status(thm)], ['49', '52', '53', '54'])).
% 3.80/4.00  thf('56', plain,
% 3.80/4.00      ((((sk_A) != (sk_A))
% 3.80/4.00        | ~ (v1_relat_1 @ sk_D)
% 3.80/4.00        | ~ (v1_funct_1 @ sk_D)
% 3.80/4.00        | ((sk_C_1) = (sk_D))
% 3.80/4.00        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.80/4.00      inference('sup-', [status(thm)], ['34', '55'])).
% 3.80/4.00  thf('57', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('58', plain,
% 3.80/4.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.80/4.00         ((v1_relat_1 @ X13)
% 3.80/4.00          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.80/4.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.80/4.00  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 3.80/4.00      inference('sup-', [status(thm)], ['57', '58'])).
% 3.80/4.00  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('61', plain,
% 3.80/4.00      ((((sk_A) != (sk_A))
% 3.80/4.00        | ((sk_C_1) = (sk_D))
% 3.80/4.00        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.80/4.00      inference('demod', [status(thm)], ['56', '59', '60'])).
% 3.80/4.00  thf('62', plain,
% 3.80/4.00      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 3.80/4.00      inference('simplify', [status(thm)], ['61'])).
% 3.80/4.00  thf('63', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf(cc2_relset_1, axiom,
% 3.80/4.00    (![A:$i,B:$i,C:$i]:
% 3.80/4.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.00       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.80/4.00  thf('64', plain,
% 3.80/4.00      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.80/4.00         ((v4_relat_1 @ X16 @ X17)
% 3.80/4.00          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.80/4.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.80/4.00  thf('65', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 3.80/4.00      inference('sup-', [status(thm)], ['63', '64'])).
% 3.80/4.00  thf(d18_relat_1, axiom,
% 3.80/4.00    (![A:$i,B:$i]:
% 3.80/4.00     ( ( v1_relat_1 @ B ) =>
% 3.80/4.00       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.80/4.00  thf('66', plain,
% 3.80/4.00      (![X9 : $i, X10 : $i]:
% 3.80/4.00         (~ (v4_relat_1 @ X9 @ X10)
% 3.80/4.00          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 3.80/4.00          | ~ (v1_relat_1 @ X9))),
% 3.80/4.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.80/4.00  thf('67', plain,
% 3.80/4.00      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 3.80/4.00      inference('sup-', [status(thm)], ['65', '66'])).
% 3.80/4.00  thf('68', plain, ((v1_relat_1 @ sk_C_1)),
% 3.80/4.00      inference('sup-', [status(thm)], ['50', '51'])).
% 3.80/4.00  thf('69', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 3.80/4.00      inference('demod', [status(thm)], ['67', '68'])).
% 3.80/4.00  thf(t3_subset, axiom,
% 3.80/4.00    (![A:$i,B:$i]:
% 3.80/4.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.80/4.00  thf('70', plain,
% 3.80/4.00      (![X3 : $i, X5 : $i]:
% 3.80/4.00         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 3.80/4.00      inference('cnf', [status(esa)], [t3_subset])).
% 3.80/4.00  thf('71', plain,
% 3.80/4.00      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 3.80/4.00      inference('sup-', [status(thm)], ['69', '70'])).
% 3.80/4.00  thf(t4_subset, axiom,
% 3.80/4.00    (![A:$i,B:$i,C:$i]:
% 3.80/4.00     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 3.80/4.00       ( m1_subset_1 @ A @ C ) ))).
% 3.80/4.00  thf('72', plain,
% 3.80/4.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.80/4.00         (~ (r2_hidden @ X6 @ X7)
% 3.80/4.00          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 3.80/4.00          | (m1_subset_1 @ X6 @ X8))),
% 3.80/4.00      inference('cnf', [status(esa)], [t4_subset])).
% 3.80/4.00  thf('73', plain,
% 3.80/4.00      (![X0 : $i]:
% 3.80/4.00         ((m1_subset_1 @ X0 @ sk_A)
% 3.80/4.00          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 3.80/4.00      inference('sup-', [status(thm)], ['71', '72'])).
% 3.80/4.00  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.80/4.00      inference('demod', [status(thm)], ['41', '46'])).
% 3.80/4.00  thf('75', plain,
% 3.80/4.00      (![X0 : $i]: ((m1_subset_1 @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_A))),
% 3.80/4.00      inference('demod', [status(thm)], ['73', '74'])).
% 3.80/4.00  thf('76', plain,
% 3.80/4.00      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.80/4.00      inference('sup-', [status(thm)], ['62', '75'])).
% 3.80/4.00  thf('77', plain,
% 3.80/4.00      (![X37 : $i]:
% 3.80/4.00         (((k1_funct_1 @ sk_C_1 @ X37) = (k1_funct_1 @ sk_D @ X37))
% 3.80/4.00          | ~ (m1_subset_1 @ X37 @ sk_A))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('78', plain,
% 3.80/4.00      ((((sk_C_1) = (sk_D))
% 3.80/4.00        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.80/4.00            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 3.80/4.00      inference('sup-', [status(thm)], ['76', '77'])).
% 3.80/4.00  thf('79', plain,
% 3.80/4.00      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.80/4.00         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 3.80/4.00      inference('condensation', [status(thm)], ['78'])).
% 3.80/4.00  thf('80', plain,
% 3.80/4.00      (![X11 : $i, X12 : $i]:
% 3.80/4.00         (~ (v1_relat_1 @ X11)
% 3.80/4.00          | ~ (v1_funct_1 @ X11)
% 3.80/4.00          | ((X12) = (X11))
% 3.80/4.00          | ((k1_funct_1 @ X12 @ (sk_C @ X11 @ X12))
% 3.80/4.00              != (k1_funct_1 @ X11 @ (sk_C @ X11 @ X12)))
% 3.80/4.00          | ((k1_relat_1 @ X12) != (k1_relat_1 @ X11))
% 3.80/4.00          | ~ (v1_funct_1 @ X12)
% 3.80/4.00          | ~ (v1_relat_1 @ X12))),
% 3.80/4.00      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.80/4.00  thf('81', plain,
% 3.80/4.00      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.80/4.00          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 3.80/4.00        | ~ (v1_relat_1 @ sk_C_1)
% 3.80/4.00        | ~ (v1_funct_1 @ sk_C_1)
% 3.80/4.00        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 3.80/4.00        | ((sk_C_1) = (sk_D))
% 3.80/4.00        | ~ (v1_funct_1 @ sk_D)
% 3.80/4.00        | ~ (v1_relat_1 @ sk_D))),
% 3.80/4.00      inference('sup-', [status(thm)], ['79', '80'])).
% 3.80/4.00  thf('82', plain, ((v1_relat_1 @ sk_C_1)),
% 3.80/4.00      inference('sup-', [status(thm)], ['50', '51'])).
% 3.80/4.00  thf('83', plain, ((v1_funct_1 @ sk_C_1)),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.80/4.00      inference('demod', [status(thm)], ['41', '46'])).
% 3.80/4.00  thf('85', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.80/4.00      inference('demod', [status(thm)], ['7', '33'])).
% 3.80/4.00  thf('86', plain, ((v1_funct_1 @ sk_D)),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('87', plain, ((v1_relat_1 @ sk_D)),
% 3.80/4.00      inference('sup-', [status(thm)], ['57', '58'])).
% 3.80/4.00  thf('88', plain,
% 3.80/4.00      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.80/4.00          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 3.80/4.00        | ((sk_A) != (sk_A))
% 3.80/4.00        | ((sk_C_1) = (sk_D)))),
% 3.80/4.00      inference('demod', [status(thm)],
% 3.80/4.00                ['81', '82', '83', '84', '85', '86', '87'])).
% 3.80/4.00  thf('89', plain, (((sk_C_1) = (sk_D))),
% 3.80/4.00      inference('simplify', [status(thm)], ['88'])).
% 3.80/4.00  thf('90', plain,
% 3.80/4.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.80/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.00  thf('91', plain,
% 3.80/4.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.00         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.80/4.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.80/4.00      inference('condensation', [status(thm)], ['12'])).
% 3.80/4.00  thf('92', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 3.80/4.00      inference('sup-', [status(thm)], ['90', '91'])).
% 3.80/4.00  thf('93', plain, ($false),
% 3.80/4.00      inference('demod', [status(thm)], ['0', '89', '92'])).
% 3.80/4.00  
% 3.80/4.00  % SZS output end Refutation
% 3.80/4.00  
% 3.80/4.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
