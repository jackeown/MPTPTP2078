%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cmNFMSBKGT

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:22 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 108 expanded)
%              Number of leaves         :   39 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  634 (1006 expanded)
%              Number of equality atoms :   51 (  71 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('3',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X1: $i,X4: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X4 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X14: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X16
       != ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X14 ) )
      | ( X18
       != ( k1_funct_1 @ X14 @ X19 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('24',plain,(
    ! [X14: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X19 ) @ ( k2_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X25 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('34',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X1: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ( X5 = X4 )
      | ( X5 = X1 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('44',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ( X5 = X1 )
      | ( X5 = X4 )
      | ~ ( r2_hidden @ X5 @ ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cmNFMSBKGT
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 99 iterations in 0.053s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.34/0.52  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.34/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.34/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.34/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.34/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.34/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.52  thf(t65_funct_2, conjecture,
% 0.34/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.34/0.52         ( m1_subset_1 @
% 0.34/0.52           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.34/0.52       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.34/0.52            ( m1_subset_1 @
% 0.34/0.52              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.34/0.52          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.34/0.52  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(d1_funct_2, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.34/0.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.34/0.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.34/0.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.34/0.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_1, axiom,
% 0.34/0.52    (![B:$i,A:$i]:
% 0.34/0.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.52       ( zip_tseitin_0 @ B @ A ) ))).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X34 : $i, X35 : $i]:
% 0.34/0.52         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_D_3 @ 
% 0.34/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.34/0.52  thf(zf_stmt_3, axiom,
% 0.34/0.52    (![C:$i,B:$i,A:$i]:
% 0.34/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.34/0.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.34/0.52  thf(zf_stmt_5, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.34/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.34/0.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.34/0.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.34/0.52         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.34/0.52          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.34/0.52          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.34/0.52        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.34/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.34/0.52        | (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.34/0.52      inference('sup-', [status(thm)], ['1', '4'])).
% 0.34/0.52  thf('6', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ (k1_tarski @ sk_B))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.34/0.52         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.34/0.52          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.34/0.52          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.34/0.52        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_D_3 @ 
% 0.34/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.34/0.52         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.34/0.52          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.34/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)
% 0.34/0.52         = (k1_relat_1 @ sk_D_3))),
% 0.34/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.34/0.52        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.34/0.52      inference('demod', [status(thm)], ['8', '11'])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['5', '12'])).
% 0.34/0.52  thf(t69_enumset1, axiom,
% 0.34/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.34/0.52  thf('14', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.34/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.52  thf(d2_tarski, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.34/0.52       ( ![D:$i]:
% 0.34/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.34/0.52  thf('15', plain,
% 0.34/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.34/0.52         (((X2) != (X1))
% 0.34/0.52          | (r2_hidden @ X2 @ X3)
% 0.34/0.52          | ((X3) != (k2_tarski @ X4 @ X1)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X1 : $i, X4 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X4 @ X1))),
% 0.34/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.34/0.52  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.34/0.52      inference('sup+', [status(thm)], ['14', '16'])).
% 0.34/0.52  thf(t7_ordinal1, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (![X20 : $i, X21 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.34/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.34/0.52  thf('19', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.34/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      ((~ (r1_tarski @ k1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['13', '19'])).
% 0.34/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.34/0.52  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.34/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.34/0.52  thf('22', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.34/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.52  thf(d5_funct_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.34/0.52           ( ![C:$i]:
% 0.34/0.52             ( ( r2_hidden @ C @ B ) <=>
% 0.34/0.52               ( ?[D:$i]:
% 0.34/0.52                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.34/0.52                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.34/0.52  thf('23', plain,
% 0.34/0.52      (![X14 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.34/0.52         (((X16) != (k2_relat_1 @ X14))
% 0.34/0.52          | (r2_hidden @ X18 @ X16)
% 0.34/0.52          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X14))
% 0.34/0.52          | ((X18) != (k1_funct_1 @ X14 @ X19))
% 0.34/0.52          | ~ (v1_funct_1 @ X14)
% 0.34/0.52          | ~ (v1_relat_1 @ X14))),
% 0.34/0.52      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      (![X14 : $i, X19 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X14)
% 0.34/0.52          | ~ (v1_funct_1 @ X14)
% 0.34/0.52          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X14))
% 0.34/0.52          | (r2_hidden @ (k1_funct_1 @ X14 @ X19) @ (k2_relat_1 @ X14)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X0 @ sk_A)
% 0.34/0.52          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3))
% 0.34/0.52          | ~ (v1_funct_1 @ sk_D_3)
% 0.34/0.52          | ~ (v1_relat_1 @ sk_D_3))),
% 0.34/0.52      inference('sup-', [status(thm)], ['22', '24'])).
% 0.34/0.52  thf('26', plain, ((v1_funct_1 @ sk_D_3)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_D_3 @ 
% 0.34/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(cc1_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( v1_relat_1 @ C ) ))).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.52         ((v1_relat_1 @ X22)
% 0.34/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.34/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.34/0.52  thf('29', plain, ((v1_relat_1 @ sk_D_3)),
% 0.34/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X0 @ sk_A)
% 0.34/0.52          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3)))),
% 0.34/0.52      inference('demod', [status(thm)], ['25', '26', '29'])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k2_relat_1 @ sk_D_3))),
% 0.34/0.52      inference('sup-', [status(thm)], ['0', '30'])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_D_3 @ 
% 0.34/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(dt_k2_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.52         ((m1_subset_1 @ (k2_relset_1 @ X25 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))
% 0.34/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.34/0.52      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3) @ 
% 0.34/0.52        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_D_3 @ 
% 0.34/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.34/0.52         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.34/0.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.34/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.34/0.52  thf('37', plain,
% 0.34/0.52      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)
% 0.34/0.52         = (k2_relat_1 @ sk_D_3))),
% 0.34/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      ((m1_subset_1 @ (k2_relat_1 @ sk_D_3) @ 
% 0.34/0.52        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['34', '37'])).
% 0.34/0.52  thf(l3_subset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.34/0.52  thf('39', plain,
% 0.34/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X10 @ X11)
% 0.34/0.52          | (r2_hidden @ X10 @ X12)
% 0.34/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.34/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.34/0.52  thf('40', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.34/0.52          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.34/0.52  thf('41', plain,
% 0.34/0.52      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['31', '40'])).
% 0.34/0.52  thf('42', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.34/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.52  thf('43', plain,
% 0.34/0.52      (![X1 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X5 @ X3)
% 0.34/0.52          | ((X5) = (X4))
% 0.34/0.52          | ((X5) = (X1))
% 0.34/0.52          | ((X3) != (k2_tarski @ X4 @ X1)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.34/0.52  thf('44', plain,
% 0.34/0.52      (![X1 : $i, X4 : $i, X5 : $i]:
% 0.34/0.52         (((X5) = (X1))
% 0.34/0.52          | ((X5) = (X4))
% 0.34/0.52          | ~ (r2_hidden @ X5 @ (k2_tarski @ X4 @ X1)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.34/0.52  thf('45', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['42', '44'])).
% 0.34/0.52  thf('46', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.34/0.52  thf('47', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) = (sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['41', '46'])).
% 0.34/0.52  thf('48', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) != (sk_B))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('49', plain, ($false),
% 0.34/0.52      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
