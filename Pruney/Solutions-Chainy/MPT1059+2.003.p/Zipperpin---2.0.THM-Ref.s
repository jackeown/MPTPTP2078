%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I1F0jP3ndz

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:49 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 121 expanded)
%              Number of leaves         :   40 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  624 (1436 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
    | ( r2_hidden @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_D @ sk_A_1 ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('15',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A_1
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X34 ) )
      | ( ( k7_partfun1 @ X35 @ X34 @ X33 )
        = ( k1_funct_1 @ X34 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v5_relat_1 @ X34 @ X35 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A_1 )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','36'])).

thf('38',plain,
    ( ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','37'])).

thf('39',plain,(
    ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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

thf('42',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ X37 )
      | ( ( k3_funct_2 @ X37 @ X38 @ X36 @ X39 )
        = ( k1_funct_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
 != ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['39','49'])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I1F0jP3ndz
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 253 iterations in 0.187s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.64  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.47/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.64  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.47/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.64  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(t176_funct_2, conjecture,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.64           ( ![C:$i]:
% 0.47/0.64             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.64                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64               ( ![D:$i]:
% 0.47/0.64                 ( ( m1_subset_1 @ D @ A ) =>
% 0.47/0.64                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.47/0.64                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i]:
% 0.47/0.64        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.64          ( ![B:$i]:
% 0.47/0.64            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.64              ( ![C:$i]:
% 0.47/0.64                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.64                    ( m1_subset_1 @
% 0.47/0.64                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64                  ( ![D:$i]:
% 0.47/0.64                    ( ( m1_subset_1 @ D @ A ) =>
% 0.47/0.64                      ( ( k7_partfun1 @ B @ C @ D ) =
% 0.47/0.64                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 0.47/0.64  thf('0', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(cc2_relset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.64         ((v5_relat_1 @ X16 @ X18)
% 0.47/0.64          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.64  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.64  thf('3', plain, ((m1_subset_1 @ sk_D @ sk_A_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t2_subset, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ A @ B ) =>
% 0.47/0.64       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (![X6 : $i, X7 : $i]:
% 0.47/0.64         ((r2_hidden @ X6 @ X7)
% 0.47/0.64          | (v1_xboole_0 @ X7)
% 0.47/0.64          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_subset])).
% 0.47/0.64  thf('5', plain, (((v1_xboole_0 @ sk_A_1) | (r2_hidden @ sk_D @ sk_A_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.64  thf('6', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('7', plain, ((r2_hidden @ sk_D @ sk_A_1)),
% 0.47/0.64      inference('clc', [status(thm)], ['5', '6'])).
% 0.47/0.64  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(d1_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.64           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.64             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.64           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.64             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_1, axiom,
% 0.47/0.64    (![C:$i,B:$i,A:$i]:
% 0.47/0.64     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.64       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.64         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.47/0.64          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.47/0.64          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 0.47/0.64        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.64  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.64  thf(zf_stmt_4, axiom,
% 0.47/0.64    (![B:$i,A:$i]:
% 0.47/0.64     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.64       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.64  thf(zf_stmt_5, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.64       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.64         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.64           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.64             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.64  thf('12', plain,
% 0.47/0.64      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.47/0.64         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.47/0.64          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.47/0.64          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 0.47/0.64        | ~ (zip_tseitin_0 @ sk_B @ sk_A_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X25 : $i, X26 : $i]:
% 0.47/0.64         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.47/0.64  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.47/0.64  thf('15', plain, ((v1_xboole_0 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.47/0.64  thf(t4_subset_1, axiom,
% 0.47/0.64    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.47/0.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.64  thf(cc1_subset_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_xboole_0 @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (![X4 : $i, X5 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.47/0.64          | (v1_xboole_0 @ X4)
% 0.47/0.64          | ~ (v1_xboole_0 @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.64  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('sup-', [status(thm)], ['15', '18'])).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['14', '19'])).
% 0.47/0.64  thf('21', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('22', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.47/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.64  thf('23', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)),
% 0.47/0.64      inference('demod', [status(thm)], ['13', '22'])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.64         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.47/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      (((k1_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.64  thf('27', plain, (((sk_A_1) = (k1_relat_1 @ sk_C))),
% 0.47/0.64      inference('demod', [status(thm)], ['10', '23', '26'])).
% 0.47/0.64  thf(d8_partfun1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.64       ( ![C:$i]:
% 0.47/0.64         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.64           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.47/0.64  thf('28', plain,
% 0.47/0.64      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X33 @ (k1_relat_1 @ X34))
% 0.47/0.64          | ((k7_partfun1 @ X35 @ X34 @ X33) = (k1_funct_1 @ X34 @ X33))
% 0.47/0.64          | ~ (v1_funct_1 @ X34)
% 0.47/0.64          | ~ (v5_relat_1 @ X34 @ X35)
% 0.47/0.64          | ~ (v1_relat_1 @ X34))),
% 0.47/0.64      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ sk_A_1)
% 0.47/0.64          | ~ (v1_relat_1 @ sk_C)
% 0.47/0.64          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(cc2_relat_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.47/0.64          | (v1_relat_1 @ X11)
% 0.47/0.64          | ~ (v1_relat_1 @ X12))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.64  thf(fc6_relat_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.64  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.64  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ sk_A_1)
% 0.47/0.64          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.47/0.64          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['29', '34', '35'])).
% 0.47/0.64  thf('37', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 0.47/0.64          | ~ (v5_relat_1 @ sk_C @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['7', '36'])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (((k7_partfun1 @ sk_B @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.47/0.64      inference('sup-', [status(thm)], ['2', '37'])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      (((k7_partfun1 @ sk_B @ sk_C @ sk_D)
% 0.47/0.64         != (k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ sk_D))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('40', plain, ((m1_subset_1 @ sk_D @ sk_A_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(redefinition_k3_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.47/0.64         ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.64         ( m1_subset_1 @ D @ A ) ) =>
% 0.47/0.64       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.47/0.64          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.47/0.64          | ~ (v1_funct_1 @ X36)
% 0.47/0.64          | (v1_xboole_0 @ X37)
% 0.47/0.64          | ~ (m1_subset_1 @ X39 @ X37)
% 0.47/0.64          | ((k3_funct_2 @ X37 @ X38 @ X36 @ X39) = (k1_funct_1 @ X36 @ X39)))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.47/0.64          | (v1_xboole_0 @ sk_A_1)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.64  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('45', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.47/0.64          | (v1_xboole_0 @ sk_A_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.47/0.64  thf('47', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.47/0.64          | ((k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0)
% 0.47/0.64              = (k1_funct_1 @ sk_C @ X0)))),
% 0.47/0.64      inference('clc', [status(thm)], ['46', '47'])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      (((k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.47/0.64      inference('sup-', [status(thm)], ['40', '48'])).
% 0.47/0.64  thf('50', plain,
% 0.47/0.64      (((k7_partfun1 @ sk_B @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))),
% 0.47/0.64      inference('demod', [status(thm)], ['39', '49'])).
% 0.47/0.64  thf('51', plain, ($false),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['38', '50'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
