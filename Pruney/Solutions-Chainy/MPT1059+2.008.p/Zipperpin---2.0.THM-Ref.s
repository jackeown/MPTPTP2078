%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VMMP7j777W

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:50 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 119 expanded)
%              Number of leaves         :   40 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  617 (1429 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t176_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( k7_partfun1 @ B @ C @ D )
                    = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( k7_partfun1 @ B @ C @ D )
                      = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','23','26'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) )
      | ( ( k7_partfun1 @ X33 @ X32 @ X31 )
        = ( k1_funct_1 @ X32 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','34'])).

thf('36',plain,
    ( ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','35'])).

thf('37',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('40',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X34 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ X35 )
      | ( ( k3_funct_2 @ X35 @ X36 @ X34 @ X37 )
        = ( k1_funct_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['37','47'])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VMMP7j777W
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 386 iterations in 0.433s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.88  thf(sk_B_type, type, sk_B: $i > $i).
% 0.69/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.69/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.88  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.69/0.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.69/0.88  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.69/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.88  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.69/0.88  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.69/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.88  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.69/0.88  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.69/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.69/0.88  thf(t176_funct_2, conjecture,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.69/0.88           ( ![C:$i]:
% 0.69/0.88             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.88                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88               ( ![D:$i]:
% 0.69/0.88                 ( ( m1_subset_1 @ D @ A ) =>
% 0.69/0.88                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.69/0.88                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i]:
% 0.69/0.88        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.88          ( ![B:$i]:
% 0.69/0.88            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.69/0.88              ( ![C:$i]:
% 0.69/0.88                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.88                    ( m1_subset_1 @
% 0.69/0.88                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88                  ( ![D:$i]:
% 0.69/0.88                    ( ( m1_subset_1 @ D @ A ) =>
% 0.69/0.88                      ( ( k7_partfun1 @ B @ C @ D ) =
% 0.69/0.88                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 0.69/0.88  thf('0', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(cc2_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.69/0.88  thf('1', plain,
% 0.69/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.88         ((v5_relat_1 @ X17 @ X19)
% 0.69/0.88          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.69/0.88  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.69/0.88      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.88  thf('3', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(t2_subset, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ A @ B ) =>
% 0.69/0.88       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.69/0.88  thf('4', plain,
% 0.69/0.88      (![X7 : $i, X8 : $i]:
% 0.69/0.88         ((r2_hidden @ X7 @ X8)
% 0.69/0.88          | (v1_xboole_0 @ X8)
% 0.69/0.88          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.69/0.88      inference('cnf', [status(esa)], [t2_subset])).
% 0.69/0.88  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_D @ sk_A))),
% 0.69/0.88      inference('sup-', [status(thm)], ['3', '4'])).
% 0.69/0.88  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('7', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.69/0.88      inference('clc', [status(thm)], ['5', '6'])).
% 0.69/0.88  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(d1_funct_2, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.69/0.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.69/0.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.69/0.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_1, axiom,
% 0.69/0.88    (![C:$i,B:$i,A:$i]:
% 0.69/0.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.69/0.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.69/0.88  thf('9', plain,
% 0.69/0.88      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.69/0.88         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.69/0.88          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.69/0.88          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.88  thf('10', plain,
% 0.69/0.88      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.69/0.88        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.88  thf('11', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_4, axiom,
% 0.69/0.88    (![B:$i,A:$i]:
% 0.69/0.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.88       ( zip_tseitin_0 @ B @ A ) ))).
% 0.69/0.88  thf(zf_stmt_5, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.69/0.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.69/0.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.69/0.88  thf('12', plain,
% 0.69/0.88      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.88         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.69/0.88          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.69/0.88          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.69/0.88        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.69/0.88      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.88  thf('14', plain,
% 0.69/0.88      (![X23 : $i, X24 : $i]:
% 0.69/0.88         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.69/0.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.69/0.88  thf('15', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.69/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.69/0.88      inference('sup+', [status(thm)], ['14', '15'])).
% 0.69/0.88  thf(d1_xboole_0, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.69/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.69/0.88  thf(t7_ordinal1, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.88  thf('18', plain,
% 0.69/0.88      (![X12 : $i, X13 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.69/0.88      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.69/0.88  thf('19', plain,
% 0.69/0.88      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['17', '18'])).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['16', '19'])).
% 0.69/0.88  thf('21', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('22', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.69/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.69/0.88  thf('23', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.69/0.88      inference('demod', [status(thm)], ['13', '22'])).
% 0.69/0.88  thf('24', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.69/0.88  thf('25', plain,
% 0.69/0.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.69/0.88         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.69/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.88  thf('26', plain,
% 0.69/0.88      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.88  thf('27', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.69/0.88      inference('demod', [status(thm)], ['10', '23', '26'])).
% 0.69/0.88  thf(d8_partfun1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.88       ( ![C:$i]:
% 0.69/0.88         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.69/0.88           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.69/0.88  thf('28', plain,
% 0.69/0.88      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X31 @ (k1_relat_1 @ X32))
% 0.69/0.88          | ((k7_partfun1 @ X33 @ X32 @ X31) = (k1_funct_1 @ X32 @ X31))
% 0.69/0.88          | ~ (v1_funct_1 @ X32)
% 0.69/0.88          | ~ (v5_relat_1 @ X32 @ X33)
% 0.69/0.88          | ~ (v1_relat_1 @ X32))),
% 0.69/0.88      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.69/0.88  thf('29', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X0 @ sk_A)
% 0.69/0.88          | ~ (v1_relat_1 @ sk_C)
% 0.69/0.88          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.69/0.88          | ~ (v1_funct_1 @ sk_C)
% 0.69/0.88          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.88  thf('30', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(cc1_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( v1_relat_1 @ C ) ))).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.88         ((v1_relat_1 @ X14)
% 0.69/0.88          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.69/0.88  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('34', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X0 @ sk_A)
% 0.69/0.88          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.69/0.88          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.69/0.88  thf('35', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 0.69/0.88          | ~ (v5_relat_1 @ sk_C @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['7', '34'])).
% 0.69/0.88  thf('36', plain,
% 0.69/0.88      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['2', '35'])).
% 0.69/0.88  thf('37', plain,
% 0.69/0.88      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D)
% 0.69/0.88         != (k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('38', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('39', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(redefinition_k3_funct_2, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.69/0.88         ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.88         ( m1_subset_1 @ D @ A ) ) =>
% 0.69/0.88       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.69/0.88  thf('40', plain,
% 0.69/0.88      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.69/0.88          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.69/0.88          | ~ (v1_funct_1 @ X34)
% 0.69/0.88          | (v1_xboole_0 @ X35)
% 0.69/0.88          | ~ (m1_subset_1 @ X37 @ X35)
% 0.69/0.88          | ((k3_funct_2 @ X35 @ X36 @ X34 @ X37) = (k1_funct_1 @ X34 @ X37)))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.69/0.88  thf('41', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.88          | (v1_xboole_0 @ sk_A)
% 0.69/0.88          | ~ (v1_funct_1 @ sk_C)
% 0.69/0.88          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.69/0.88      inference('sup-', [status(thm)], ['39', '40'])).
% 0.69/0.88  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('44', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.88          | (v1_xboole_0 @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.69/0.88  thf('45', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('46', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.88          | ((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0)
% 0.69/0.88              = (k1_funct_1 @ sk_C @ X0)))),
% 0.69/0.88      inference('clc', [status(thm)], ['44', '45'])).
% 0.69/0.88  thf('47', plain,
% 0.69/0.88      (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['38', '46'])).
% 0.69/0.88  thf('48', plain,
% 0.69/0.88      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['37', '47'])).
% 0.69/0.88  thf('49', plain, ($false),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['36', '48'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
