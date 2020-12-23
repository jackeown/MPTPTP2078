%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RtiVclt7EN

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:15 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 139 expanded)
%              Number of leaves         :   39 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  586 (1520 expanded)
%              Number of equality atoms :   35 (  73 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v5_relat_1 @ sk_D_2 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_relat_1 @ X4 ) )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( v5_relat_1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v5_relat_1 @ sk_D_2 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_2 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','26'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('29',plain,(
    ~ ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['13','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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
    inference('sup-',[status(thm)],['23','24'])).

thf('38',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B ),
    inference(demod,[status(thm)],['7','35','36','37'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('40',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X35: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_2 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('44',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('45',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) ) ) ),
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
    inference('sup-',[status(thm)],['23','24'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RtiVclt7EN
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 116 iterations in 0.166s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.42/0.62  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(t190_funct_2, conjecture,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.42/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.42/0.62       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.42/0.62            ( ![E:$i]:
% 0.42/0.62              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.42/0.62            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.42/0.62          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.42/0.62               ( ![E:$i]:
% 0.42/0.62                 ( ( m1_subset_1 @ E @ B ) =>
% 0.42/0.62                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.42/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.42/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.62  thf(d5_funct_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.42/0.62           ( ![C:$i]:
% 0.42/0.62             ( ( r2_hidden @ C @ B ) <=>
% 0.42/0.62               ( ?[D:$i]:
% 0.42/0.62                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.42/0.62                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.42/0.62         (((X9) != (k2_relat_1 @ X7))
% 0.42/0.62          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7))
% 0.42/0.62          | ~ (r2_hidden @ X10 @ X9)
% 0.42/0.62          | ~ (v1_funct_1 @ X7)
% 0.42/0.62          | ~ (v1_relat_1 @ X7))),
% 0.42/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X7 : $i, X10 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X7)
% 0.42/0.62          | ~ (v1_funct_1 @ X7)
% 0.42/0.62          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 0.42/0.62          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['5'])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_D_2)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_D_2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '6'])).
% 0.42/0.62  thf('8', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(d1_funct_2, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_1, axiom,
% 0.42/0.62    (![C:$i,B:$i,A:$i]:
% 0.42/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.42/0.62         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.42/0.62          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.42/0.62          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.42/0.62        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_4, axiom,
% 0.42/0.62    (![B:$i,A:$i]:
% 0.42/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.62  thf(zf_stmt_5, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.42/0.62         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.42/0.62          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.42/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.42/0.62        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X27 : $i, X28 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.42/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.62  thf('15', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.42/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc2_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.62         ((v5_relat_1 @ X18 @ X20)
% 0.42/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.62  thf('19', plain, ((v5_relat_1 @ sk_D_2 @ sk_C_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf('20', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.42/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.62  thf(t202_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X3 @ (k2_relat_1 @ X4))
% 0.42/0.62          | (r2_hidden @ X3 @ X5)
% 0.42/0.62          | ~ (v5_relat_1 @ X4 @ X5)
% 0.42/0.62          | ~ (v1_relat_1 @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ sk_D_2)
% 0.42/0.62          | ~ (v5_relat_1 @ sk_D_2 @ X0)
% 0.42/0.62          | (r2_hidden @ sk_A @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc1_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( v1_relat_1 @ C ) ))).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         ((v1_relat_1 @ X15)
% 0.42/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.62  thf('25', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X0 : $i]: (~ (v5_relat_1 @ sk_D_2 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['22', '25'])).
% 0.42/0.62  thf('27', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '26'])).
% 0.42/0.62  thf(t7_ordinal1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X13 : $i, X14 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.62  thf('29', plain, (~ (r1_tarski @ sk_C_1 @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.62  thf('30', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '29'])).
% 0.42/0.62  thf('31', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B)),
% 0.42/0.62      inference('demod', [status(thm)], ['13', '30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.62         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.42/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (((k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.62  thf('35', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 0.42/0.62      inference('demod', [status(thm)], ['10', '31', '34'])).
% 0.42/0.62  thf('36', plain, ((v1_funct_1 @ sk_D_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('37', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.62  thf('38', plain, ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B)),
% 0.42/0.62      inference('demod', [status(thm)], ['7', '35', '36', '37'])).
% 0.42/0.62  thf(t1_subset, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.42/0.62  thf('40', plain, ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B)),
% 0.42/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (![X35 : $i]:
% 0.42/0.62         (((sk_A) != (k1_funct_1 @ sk_D_2 @ X35))
% 0.42/0.62          | ~ (m1_subset_1 @ X35 @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (((sk_A) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.42/0.62  thf('43', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.42/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.42/0.62         (((X9) != (k2_relat_1 @ X7))
% 0.42/0.62          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7)))
% 0.42/0.62          | ~ (r2_hidden @ X10 @ X9)
% 0.42/0.62          | ~ (v1_funct_1 @ X7)
% 0.42/0.62          | ~ (v1_relat_1 @ X7))),
% 0.42/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (![X7 : $i, X10 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X7)
% 0.42/0.62          | ~ (v1_funct_1 @ X7)
% 0.42/0.62          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 0.42/0.62          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['44'])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      ((((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_D_2)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_D_2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['43', '45'])).
% 0.42/0.62  thf('47', plain, ((v1_funct_1 @ sk_D_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('48', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.42/0.62      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.42/0.62  thf('50', plain, (((sk_A) != (sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['42', '49'])).
% 0.42/0.62  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
