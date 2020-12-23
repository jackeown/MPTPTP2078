%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Sfs4Hhba2y

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 140 expanded)
%              Number of leaves         :   40 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  602 (1536 expanded)
%              Number of equality atoms :   42 (  80 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 ) @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_1 ),
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

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v5_relat_1 @ sk_D_2 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( v5_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v5_relat_1 @ sk_D_2 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_2 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','25'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ X3 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('30',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['10','31','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('38',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B ),
    inference(demod,[status(thm)],['7','35','36','37'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('40',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X36: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_2 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('44',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( X13
        = ( k1_funct_1 @ X10 @ ( sk_D_1 @ X13 @ X10 ) ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('45',plain,(
    ! [X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X10 ) )
      | ( X13
        = ( k1_funct_1 @ X10 @ ( sk_D_1 @ X13 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('49',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Sfs4Hhba2y
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:22:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 114 iterations in 0.079s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.53  thf(t190_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.53       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.21/0.53            ( ![E:$i]:
% 0.21/0.53              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.53            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.53          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.21/0.53               ( ![E:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ E @ B ) =>
% 0.21/0.53                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.53         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.53  thf(d5_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.53               ( ?[D:$i]:
% 0.21/0.53                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.53                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (((X12) != (k2_relat_1 @ X10))
% 0.21/0.53          | (r2_hidden @ (sk_D_1 @ X13 @ X10) @ (k1_relat_1 @ X10))
% 0.21/0.53          | ~ (r2_hidden @ X13 @ X12)
% 0.21/0.53          | ~ (v1_funct_1 @ X10)
% 0.21/0.53          | ~ (v1_relat_1 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X10 : $i, X13 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X10)
% 0.21/0.53          | ~ (v1_funct_1 @ X10)
% 0.21/0.53          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X10))
% 0.21/0.53          | (r2_hidden @ (sk_D_1 @ X13 @ X10) @ (k1_relat_1 @ X10)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.21/0.53        | ~ (v1_funct_1 @ sk_D_2)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.53  thf('8', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d1_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_1, axiom,
% 0.21/0.53    (![C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.53         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.21/0.53          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.21/0.53          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.21/0.53        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf(zf_stmt_2, axiom,
% 0.21/0.53    (![B:$i,A:$i]:
% 0.21/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_5, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.53         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.21/0.53          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.21/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.21/0.53        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         ((v5_relat_1 @ X19 @ X21)
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.53  thf('18', plain, ((v5_relat_1 @ sk_D_2 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.53  thf(t202_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X6 @ (k2_relat_1 @ X7))
% 0.21/0.53          | (r2_hidden @ X6 @ X8)
% 0.21/0.53          | ~ (v5_relat_1 @ X7 @ X8)
% 0.21/0.53          | ~ (v1_relat_1 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ sk_D_2)
% 0.21/0.53          | ~ (v5_relat_1 @ sk_D_2 @ X0)
% 0.21/0.53          | (r2_hidden @ sk_A @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( v1_relat_1 @ C ) ))).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         ((v1_relat_1 @ X16)
% 0.21/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.53  thf('24', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i]: (~ (v5_relat_1 @ sk_D_2 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '24'])).
% 0.21/0.53  thf('26', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '25'])).
% 0.21/0.53  thf(l22_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.53       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k2_xboole_0 @ (k1_tarski @ X1) @ X0) = (X0))
% 0.21/0.53          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.21/0.53  thf('28', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf(t49_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k1_tarski @ X2) @ X3) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.53  thf('30', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['15', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.53         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.21/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (((k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '31', '34'])).
% 0.21/0.53  thf('36', plain, ((v1_funct_1 @ sk_D_2)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('38', plain, ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '35', '36', '37'])).
% 0.21/0.53  thf(t1_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.53  thf('40', plain, ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X36 : $i]:
% 0.21/0.53         (((sk_A) != (k1_funct_1 @ sk_D_2 @ X36))
% 0.21/0.53          | ~ (m1_subset_1 @ X36 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (((sk_A) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.53  thf('43', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (((X12) != (k2_relat_1 @ X10))
% 0.21/0.53          | ((X13) = (k1_funct_1 @ X10 @ (sk_D_1 @ X13 @ X10)))
% 0.21/0.53          | ~ (r2_hidden @ X13 @ X12)
% 0.21/0.53          | ~ (v1_funct_1 @ X10)
% 0.21/0.53          | ~ (v1_relat_1 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X10 : $i, X13 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X10)
% 0.21/0.53          | ~ (v1_funct_1 @ X10)
% 0.21/0.53          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X10))
% 0.21/0.53          | ((X13) = (k1_funct_1 @ X10 @ (sk_D_1 @ X13 @ X10))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      ((((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))
% 0.21/0.53        | ~ (v1_funct_1 @ sk_D_2)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '45'])).
% 0.21/0.53  thf('47', plain, ((v1_funct_1 @ sk_D_2)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('48', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.21/0.53      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.53  thf('50', plain, (((sk_A) != (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['42', '49'])).
% 0.21/0.53  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
