%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B8wMToVAjT

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:23 EST 2020

% Result     : Theorem 14.03s
% Output     : Refutation 14.03s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 738 expanded)
%              Number of leaves         :   51 ( 245 expanded)
%              Depth                    :   24
%              Number of atoms          :  997 (10767 expanded)
%              Number of equality atoms :   42 ( 292 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t191_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ C )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
             => ( ! [E: $i] :
                    ( ( m1_subset_1 @ E @ B )
                   => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
               => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
               => ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ B )
                     => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
                 => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( zip_tseitin_2 @ X40 @ X41 @ X42 @ X43 )
      | ( r2_hidden @ X40 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_2 @ X1 @ X3 @ X2 @ X0 )
      | ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C ),
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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_funct_2,axiom,(
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

thf('22',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ ( sk_D @ X34 @ X35 @ X36 ) @ X35 )
      | ( ( k2_relset_1 @ X36 @ X35 @ X34 )
        = X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t16_funct_2])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_B @ sk_C )
    | ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_2 )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_D_2 )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_D_2 )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( ( k2_relat_1 @ sk_D_2 )
        = sk_C ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C @ sk_A )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('34',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['17','34'])).

thf('36',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['14','35'])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_2 @ D @ C @ B @ A ) )
       => ( zip_tseitin_3 @ C @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k1_relat_1 @ X48 )
       != X47 )
      | ~ ( zip_tseitin_2 @ ( sk_D_1 @ X48 @ X49 @ X47 ) @ X48 @ X49 @ X47 )
      | ( zip_tseitin_3 @ X48 @ X49 @ X47 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('38',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_funct_1 @ X48 )
      | ( zip_tseitin_3 @ X48 @ X49 @ ( k1_relat_1 @ X48 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_1 @ X48 @ X49 @ ( k1_relat_1 @ X48 ) ) @ X48 @ X49 @ ( k1_relat_1 @ X48 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 @ X0 @ ( k1_relat_1 @ sk_D_2 ) )
      | ( zip_tseitin_3 @ sk_D_2 @ X0 @ ( k1_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['14','35'])).

thf('41',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['14','35'])).

thf('42',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('49',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ X31 )
      | ( ( k3_funct_2 @ X31 @ X32 @ X30 @ X33 )
        = ( k1_funct_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ X0 )
        = ( k1_funct_1 @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_funct_2 @ sk_D_2 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ X0 )
        = ( k1_funct_1 @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ X0 )
        = ( k1_funct_1 @ sk_D_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf('58',plain,(
    ! [X50: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ X50 ) @ sk_A )
      | ~ ( m1_subset_1 @ X50 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( zip_tseitin_2 @ X40 @ X41 @ X42 @ X43 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X41 @ X40 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','45'])).

thf('65',plain,
    ( ( zip_tseitin_3 @ sk_D_2 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    zip_tseitin_3 @ sk_D_2 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( zip_tseitin_3 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('68',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_D_2 @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('74',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['4','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B8wMToVAjT
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:31:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 14.03/14.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.03/14.27  % Solved by: fo/fo7.sh
% 14.03/14.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.03/14.27  % done 5834 iterations in 13.801s
% 14.03/14.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.03/14.27  % SZS output start Refutation
% 14.03/14.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.03/14.27  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 14.03/14.27  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 14.03/14.27  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 14.03/14.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 14.03/14.27  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 14.03/14.27  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 14.03/14.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.03/14.27  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 14.03/14.27  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 14.03/14.27  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 14.03/14.27  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 14.03/14.27  thf(sk_A_type, type, sk_A: $i).
% 14.03/14.27  thf(sk_D_2_type, type, sk_D_2: $i).
% 14.03/14.27  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 14.03/14.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.03/14.27  thf(sk_C_type, type, sk_C: $i).
% 14.03/14.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.03/14.27  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 14.03/14.27  thf(sk_B_type, type, sk_B: $i).
% 14.03/14.27  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 14.03/14.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.03/14.27  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 14.03/14.27  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.03/14.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.03/14.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 14.03/14.27  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 14.03/14.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.03/14.27  thf(t191_funct_2, conjecture,
% 14.03/14.27    (![A:$i,B:$i]:
% 14.03/14.27     ( ( ~( v1_xboole_0 @ B ) ) =>
% 14.03/14.27       ( ![C:$i]:
% 14.03/14.27         ( ( ~( v1_xboole_0 @ C ) ) =>
% 14.03/14.27           ( ![D:$i]:
% 14.03/14.27             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 14.03/14.27                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 14.03/14.27               ( ( ![E:$i]:
% 14.03/14.27                   ( ( m1_subset_1 @ E @ B ) =>
% 14.03/14.27                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 14.03/14.27                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 14.03/14.27  thf(zf_stmt_0, negated_conjecture,
% 14.03/14.27    (~( ![A:$i,B:$i]:
% 14.03/14.27        ( ( ~( v1_xboole_0 @ B ) ) =>
% 14.03/14.27          ( ![C:$i]:
% 14.03/14.27            ( ( ~( v1_xboole_0 @ C ) ) =>
% 14.03/14.27              ( ![D:$i]:
% 14.03/14.27                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 14.03/14.27                    ( m1_subset_1 @
% 14.03/14.27                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 14.03/14.27                  ( ( ![E:$i]:
% 14.03/14.27                      ( ( m1_subset_1 @ E @ B ) =>
% 14.03/14.27                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 14.03/14.27                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 14.03/14.27    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 14.03/14.27  thf('0', plain,
% 14.03/14.27      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_2) @ sk_A)),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf('1', plain,
% 14.03/14.27      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf(redefinition_k2_relset_1, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i]:
% 14.03/14.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.27       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 14.03/14.27  thf('2', plain,
% 14.03/14.27      (![X19 : $i, X20 : $i, X21 : $i]:
% 14.03/14.27         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 14.03/14.27          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 14.03/14.27      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 14.03/14.27  thf('3', plain,
% 14.03/14.27      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 14.03/14.27      inference('sup-', [status(thm)], ['1', '2'])).
% 14.03/14.27  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_A)),
% 14.03/14.27      inference('demod', [status(thm)], ['0', '3'])).
% 14.03/14.27  thf(t5_funct_2, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i]:
% 14.03/14.27     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 14.03/14.27       ( ( ( ![D:$i]:
% 14.03/14.27             ( ( r2_hidden @ D @ A ) =>
% 14.03/14.27               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 14.03/14.27           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 14.03/14.27         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 14.03/14.27           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 14.03/14.27  thf(zf_stmt_1, axiom,
% 14.03/14.27    (![D:$i,C:$i,B:$i,A:$i]:
% 14.03/14.27     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 14.03/14.27       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 14.03/14.27  thf('5', plain,
% 14.03/14.27      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 14.03/14.27         ((zip_tseitin_2 @ X40 @ X41 @ X42 @ X43) | (r2_hidden @ X40 @ X43))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.03/14.27  thf(t1_subset, axiom,
% 14.03/14.27    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 14.03/14.27  thf('6', plain,
% 14.03/14.27      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 14.03/14.27      inference('cnf', [status(esa)], [t1_subset])).
% 14.03/14.27  thf('7', plain,
% 14.03/14.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.03/14.27         ((zip_tseitin_2 @ X1 @ X3 @ X2 @ X0) | (m1_subset_1 @ X1 @ X0))),
% 14.03/14.27      inference('sup-', [status(thm)], ['5', '6'])).
% 14.03/14.27  thf('8', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C)),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf(d1_funct_2, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i]:
% 14.03/14.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.27       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.03/14.27           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 14.03/14.27             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 14.03/14.27         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.03/14.27           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 14.03/14.27             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 14.03/14.27  thf(zf_stmt_2, axiom,
% 14.03/14.27    (![C:$i,B:$i,A:$i]:
% 14.03/14.27     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 14.03/14.27       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 14.03/14.27  thf('9', plain,
% 14.03/14.27      (![X24 : $i, X25 : $i, X26 : $i]:
% 14.03/14.27         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 14.03/14.27          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 14.03/14.27          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_2])).
% 14.03/14.27  thf('10', plain,
% 14.03/14.27      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_B)
% 14.03/14.27        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_2)))),
% 14.03/14.27      inference('sup-', [status(thm)], ['8', '9'])).
% 14.03/14.27  thf('11', plain,
% 14.03/14.27      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf(redefinition_k1_relset_1, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i]:
% 14.03/14.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.27       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 14.03/14.27  thf('12', plain,
% 14.03/14.27      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.03/14.27         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 14.03/14.27          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 14.03/14.27      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.03/14.27  thf('13', plain,
% 14.03/14.27      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 14.03/14.27      inference('sup-', [status(thm)], ['11', '12'])).
% 14.03/14.27  thf('14', plain,
% 14.03/14.27      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_B)
% 14.03/14.27        | ((sk_B) = (k1_relat_1 @ sk_D_2)))),
% 14.03/14.27      inference('demod', [status(thm)], ['10', '13'])).
% 14.03/14.27  thf('15', plain,
% 14.03/14.27      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 14.03/14.27  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 14.03/14.27  thf(zf_stmt_5, axiom,
% 14.03/14.27    (![B:$i,A:$i]:
% 14.03/14.27     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.03/14.27       ( zip_tseitin_0 @ B @ A ) ))).
% 14.03/14.27  thf(zf_stmt_6, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i]:
% 14.03/14.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.27       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 14.03/14.27         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.03/14.27           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 14.03/14.27             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 14.03/14.27  thf('16', plain,
% 14.03/14.27      (![X27 : $i, X28 : $i, X29 : $i]:
% 14.03/14.27         (~ (zip_tseitin_0 @ X27 @ X28)
% 14.03/14.27          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 14.03/14.27          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_6])).
% 14.03/14.27  thf('17', plain,
% 14.03/14.27      (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_B)
% 14.03/14.27        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 14.03/14.27      inference('sup-', [status(thm)], ['15', '16'])).
% 14.03/14.27  thf('18', plain,
% 14.03/14.27      (![X22 : $i, X23 : $i]:
% 14.03/14.27         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.03/14.27  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 14.03/14.27  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 14.03/14.27      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.03/14.27  thf('20', plain,
% 14.03/14.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.03/14.27         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 14.03/14.27      inference('sup+', [status(thm)], ['18', '19'])).
% 14.03/14.27  thf('21', plain,
% 14.03/14.27      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf(t16_funct_2, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i]:
% 14.03/14.27     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 14.03/14.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.03/14.27       ( ( ![D:$i]:
% 14.03/14.27           ( ~( ( r2_hidden @ D @ B ) & 
% 14.03/14.27                ( ![E:$i]:
% 14.03/14.27                  ( ~( ( r2_hidden @ E @ A ) & 
% 14.03/14.27                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 14.03/14.27         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 14.03/14.27  thf('22', plain,
% 14.03/14.27      (![X34 : $i, X35 : $i, X36 : $i]:
% 14.03/14.27         ((r2_hidden @ (sk_D @ X34 @ X35 @ X36) @ X35)
% 14.03/14.27          | ((k2_relset_1 @ X36 @ X35 @ X34) = (X35))
% 14.03/14.27          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 14.03/14.27          | ~ (v1_funct_2 @ X34 @ X36 @ X35)
% 14.03/14.27          | ~ (v1_funct_1 @ X34))),
% 14.03/14.27      inference('cnf', [status(esa)], [t16_funct_2])).
% 14.03/14.27  thf('23', plain,
% 14.03/14.27      ((~ (v1_funct_1 @ sk_D_2)
% 14.03/14.27        | ~ (v1_funct_2 @ sk_D_2 @ sk_B @ sk_C)
% 14.03/14.27        | ((k2_relset_1 @ sk_B @ sk_C @ sk_D_2) = (sk_C))
% 14.03/14.27        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_B) @ sk_C))),
% 14.03/14.27      inference('sup-', [status(thm)], ['21', '22'])).
% 14.03/14.27  thf('24', plain, ((v1_funct_1 @ sk_D_2)),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf('25', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C)),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf('26', plain,
% 14.03/14.27      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 14.03/14.27      inference('sup-', [status(thm)], ['1', '2'])).
% 14.03/14.27  thf('27', plain,
% 14.03/14.27      ((((k2_relat_1 @ sk_D_2) = (sk_C))
% 14.03/14.27        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_B) @ sk_C))),
% 14.03/14.27      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 14.03/14.27  thf(t7_ordinal1, axiom,
% 14.03/14.27    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.03/14.27  thf('28', plain,
% 14.03/14.27      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 14.03/14.27      inference('cnf', [status(esa)], [t7_ordinal1])).
% 14.03/14.27  thf('29', plain,
% 14.03/14.27      ((((k2_relat_1 @ sk_D_2) = (sk_C))
% 14.03/14.27        | ~ (r1_tarski @ sk_C @ (sk_D @ sk_D_2 @ sk_C @ sk_B)))),
% 14.03/14.27      inference('sup-', [status(thm)], ['27', '28'])).
% 14.03/14.27  thf('30', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         ((zip_tseitin_0 @ sk_C @ X0) | ((k2_relat_1 @ sk_D_2) = (sk_C)))),
% 14.03/14.27      inference('sup-', [status(thm)], ['20', '29'])).
% 14.03/14.27  thf('31', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_A)),
% 14.03/14.27      inference('demod', [status(thm)], ['0', '3'])).
% 14.03/14.27  thf('32', plain,
% 14.03/14.27      (![X0 : $i]: (~ (r1_tarski @ sk_C @ sk_A) | (zip_tseitin_0 @ sk_C @ X0))),
% 14.03/14.27      inference('sup-', [status(thm)], ['30', '31'])).
% 14.03/14.27  thf('33', plain,
% 14.03/14.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.03/14.27         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 14.03/14.27      inference('sup+', [status(thm)], ['18', '19'])).
% 14.03/14.27  thf('34', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 14.03/14.27      inference('clc', [status(thm)], ['32', '33'])).
% 14.03/14.27  thf('35', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_B)),
% 14.03/14.27      inference('demod', [status(thm)], ['17', '34'])).
% 14.03/14.27  thf('36', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 14.03/14.27      inference('demod', [status(thm)], ['14', '35'])).
% 14.03/14.27  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 14.03/14.27  thf(zf_stmt_8, axiom,
% 14.03/14.27    (![C:$i,B:$i,A:$i]:
% 14.03/14.27     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 14.03/14.27       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 14.03/14.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 14.03/14.27  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 14.03/14.27  thf(zf_stmt_10, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i]:
% 14.03/14.27     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 14.03/14.27       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 14.03/14.27           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 14.03/14.27         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 14.03/14.27  thf('37', plain,
% 14.03/14.27      (![X47 : $i, X48 : $i, X49 : $i]:
% 14.03/14.27         (((k1_relat_1 @ X48) != (X47))
% 14.03/14.27          | ~ (zip_tseitin_2 @ (sk_D_1 @ X48 @ X49 @ X47) @ X48 @ X49 @ X47)
% 14.03/14.27          | (zip_tseitin_3 @ X48 @ X49 @ X47)
% 14.03/14.27          | ~ (v1_funct_1 @ X48)
% 14.03/14.27          | ~ (v1_relat_1 @ X48))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_10])).
% 14.03/14.27  thf('38', plain,
% 14.03/14.27      (![X48 : $i, X49 : $i]:
% 14.03/14.27         (~ (v1_relat_1 @ X48)
% 14.03/14.27          | ~ (v1_funct_1 @ X48)
% 14.03/14.27          | (zip_tseitin_3 @ X48 @ X49 @ (k1_relat_1 @ X48))
% 14.03/14.27          | ~ (zip_tseitin_2 @ (sk_D_1 @ X48 @ X49 @ (k1_relat_1 @ X48)) @ 
% 14.03/14.27               X48 @ X49 @ (k1_relat_1 @ X48)))),
% 14.03/14.27      inference('simplify', [status(thm)], ['37'])).
% 14.03/14.27  thf('39', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         (~ (zip_tseitin_2 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ sk_D_2 @ X0 @ 
% 14.03/14.27             (k1_relat_1 @ sk_D_2))
% 14.03/14.27          | (zip_tseitin_3 @ sk_D_2 @ X0 @ (k1_relat_1 @ sk_D_2))
% 14.03/14.27          | ~ (v1_funct_1 @ sk_D_2)
% 14.03/14.27          | ~ (v1_relat_1 @ sk_D_2))),
% 14.03/14.27      inference('sup-', [status(thm)], ['36', '38'])).
% 14.03/14.27  thf('40', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 14.03/14.27      inference('demod', [status(thm)], ['14', '35'])).
% 14.03/14.27  thf('41', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 14.03/14.27      inference('demod', [status(thm)], ['14', '35'])).
% 14.03/14.27  thf('42', plain, ((v1_funct_1 @ sk_D_2)),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf('43', plain,
% 14.03/14.27      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf(cc1_relset_1, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i]:
% 14.03/14.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.27       ( v1_relat_1 @ C ) ))).
% 14.03/14.27  thf('44', plain,
% 14.03/14.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 14.03/14.27         ((v1_relat_1 @ X10)
% 14.03/14.27          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 14.03/14.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 14.03/14.27  thf('45', plain, ((v1_relat_1 @ sk_D_2)),
% 14.03/14.27      inference('sup-', [status(thm)], ['43', '44'])).
% 14.03/14.27  thf('46', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         (~ (zip_tseitin_2 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ sk_D_2 @ X0 @ sk_B)
% 14.03/14.27          | (zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B))),
% 14.03/14.27      inference('demod', [status(thm)], ['39', '40', '41', '42', '45'])).
% 14.03/14.27  thf('47', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         ((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ sk_B)
% 14.03/14.27          | (zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B))),
% 14.03/14.27      inference('sup-', [status(thm)], ['7', '46'])).
% 14.03/14.27  thf('48', plain,
% 14.03/14.27      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf(redefinition_k3_funct_2, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i,D:$i]:
% 14.03/14.27     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 14.03/14.27         ( v1_funct_2 @ C @ A @ B ) & 
% 14.03/14.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 14.03/14.27         ( m1_subset_1 @ D @ A ) ) =>
% 14.03/14.27       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 14.03/14.27  thf('49', plain,
% 14.03/14.27      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 14.03/14.27         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 14.03/14.27          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 14.03/14.27          | ~ (v1_funct_1 @ X30)
% 14.03/14.27          | (v1_xboole_0 @ X31)
% 14.03/14.27          | ~ (m1_subset_1 @ X33 @ X31)
% 14.03/14.27          | ((k3_funct_2 @ X31 @ X32 @ X30 @ X33) = (k1_funct_1 @ X30 @ X33)))),
% 14.03/14.27      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 14.03/14.27  thf('50', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ X0)
% 14.03/14.27            = (k1_funct_1 @ sk_D_2 @ X0))
% 14.03/14.27          | ~ (m1_subset_1 @ X0 @ sk_B)
% 14.03/14.27          | (v1_xboole_0 @ sk_B)
% 14.03/14.27          | ~ (v1_funct_1 @ sk_D_2)
% 14.03/14.27          | ~ (v1_funct_2 @ sk_D_2 @ sk_B @ sk_C))),
% 14.03/14.27      inference('sup-', [status(thm)], ['48', '49'])).
% 14.03/14.27  thf('51', plain, ((v1_funct_1 @ sk_D_2)),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf('52', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C)),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf('53', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ X0)
% 14.03/14.27            = (k1_funct_1 @ sk_D_2 @ X0))
% 14.03/14.27          | ~ (m1_subset_1 @ X0 @ sk_B)
% 14.03/14.27          | (v1_xboole_0 @ sk_B))),
% 14.03/14.27      inference('demod', [status(thm)], ['50', '51', '52'])).
% 14.03/14.27  thf('54', plain, (~ (v1_xboole_0 @ sk_B)),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf('55', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         (~ (m1_subset_1 @ X0 @ sk_B)
% 14.03/14.27          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ X0)
% 14.03/14.27              = (k1_funct_1 @ sk_D_2 @ X0)))),
% 14.03/14.27      inference('clc', [status(thm)], ['53', '54'])).
% 14.03/14.27  thf('56', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         ((zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B)
% 14.03/14.27          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B))
% 14.03/14.27              = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B))))),
% 14.03/14.27      inference('sup-', [status(thm)], ['47', '55'])).
% 14.03/14.27  thf('57', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         ((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ sk_B)
% 14.03/14.27          | (zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B))),
% 14.03/14.27      inference('sup-', [status(thm)], ['7', '46'])).
% 14.03/14.27  thf('58', plain,
% 14.03/14.27      (![X50 : $i]:
% 14.03/14.27         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ X50) @ sk_A)
% 14.03/14.27          | ~ (m1_subset_1 @ X50 @ sk_B))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.27  thf('59', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         ((zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B)
% 14.03/14.27          | (r2_hidden @ 
% 14.03/14.27             (k3_funct_2 @ sk_B @ sk_C @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B)) @ 
% 14.03/14.27             sk_A))),
% 14.03/14.27      inference('sup-', [status(thm)], ['57', '58'])).
% 14.03/14.27  thf('60', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B)) @ 
% 14.03/14.27           sk_A)
% 14.03/14.27          | (zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B)
% 14.03/14.27          | (zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B))),
% 14.03/14.27      inference('sup+', [status(thm)], ['56', '59'])).
% 14.03/14.27  thf('61', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         ((zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B)
% 14.03/14.27          | (r2_hidden @ 
% 14.03/14.27             (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B)) @ sk_A))),
% 14.03/14.27      inference('simplify', [status(thm)], ['60'])).
% 14.03/14.27  thf('62', plain,
% 14.03/14.27      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 14.03/14.27         ((zip_tseitin_2 @ X40 @ X41 @ X42 @ X43)
% 14.03/14.27          | ~ (r2_hidden @ (k1_funct_1 @ X41 @ X40) @ X42))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.03/14.27  thf('63', plain,
% 14.03/14.27      (![X0 : $i, X1 : $i]:
% 14.03/14.27         ((zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B)
% 14.03/14.27          | (zip_tseitin_2 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ sk_D_2 @ sk_A @ X1))),
% 14.03/14.27      inference('sup-', [status(thm)], ['61', '62'])).
% 14.03/14.27  thf('64', plain,
% 14.03/14.27      (![X0 : $i]:
% 14.03/14.27         (~ (zip_tseitin_2 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ sk_D_2 @ X0 @ sk_B)
% 14.03/14.27          | (zip_tseitin_3 @ sk_D_2 @ X0 @ sk_B))),
% 14.03/14.27      inference('demod', [status(thm)], ['39', '40', '41', '42', '45'])).
% 14.03/14.27  thf('65', plain,
% 14.03/14.27      (((zip_tseitin_3 @ sk_D_2 @ sk_A @ sk_B)
% 14.03/14.27        | (zip_tseitin_3 @ sk_D_2 @ sk_A @ sk_B))),
% 14.03/14.27      inference('sup-', [status(thm)], ['63', '64'])).
% 14.03/14.27  thf('66', plain, ((zip_tseitin_3 @ sk_D_2 @ sk_A @ sk_B)),
% 14.03/14.27      inference('simplify', [status(thm)], ['65'])).
% 14.03/14.27  thf('67', plain,
% 14.03/14.27      (![X44 : $i, X45 : $i, X46 : $i]:
% 14.03/14.27         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 14.03/14.27          | ~ (zip_tseitin_3 @ X44 @ X45 @ X46))),
% 14.03/14.27      inference('cnf', [status(esa)], [zf_stmt_8])).
% 14.03/14.27  thf('68', plain,
% 14.03/14.27      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 14.03/14.27      inference('sup-', [status(thm)], ['66', '67'])).
% 14.03/14.27  thf(cc2_relset_1, axiom,
% 14.03/14.27    (![A:$i,B:$i,C:$i]:
% 14.03/14.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.27       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 14.03/14.27  thf('69', plain,
% 14.03/14.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.03/14.27         ((v5_relat_1 @ X13 @ X15)
% 14.03/14.27          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 14.03/14.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 14.03/14.27  thf('70', plain, ((v5_relat_1 @ sk_D_2 @ sk_A)),
% 14.03/14.27      inference('sup-', [status(thm)], ['68', '69'])).
% 14.03/14.27  thf(d19_relat_1, axiom,
% 14.03/14.27    (![A:$i,B:$i]:
% 14.03/14.27     ( ( v1_relat_1 @ B ) =>
% 14.03/14.27       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 14.03/14.27  thf('71', plain,
% 14.03/14.27      (![X6 : $i, X7 : $i]:
% 14.03/14.27         (~ (v5_relat_1 @ X6 @ X7)
% 14.03/14.27          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 14.03/14.27          | ~ (v1_relat_1 @ X6))),
% 14.03/14.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 14.03/14.27  thf('72', plain,
% 14.03/14.27      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_A))),
% 14.03/14.27      inference('sup-', [status(thm)], ['70', '71'])).
% 14.03/14.27  thf('73', plain, ((v1_relat_1 @ sk_D_2)),
% 14.03/14.27      inference('sup-', [status(thm)], ['43', '44'])).
% 14.03/14.27  thf('74', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_A)),
% 14.03/14.27      inference('demod', [status(thm)], ['72', '73'])).
% 14.03/14.27  thf('75', plain, ($false), inference('demod', [status(thm)], ['4', '74'])).
% 14.03/14.27  
% 14.03/14.27  % SZS output end Refutation
% 14.03/14.27  
% 14.03/14.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
