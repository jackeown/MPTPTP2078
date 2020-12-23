%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4X3eXikT7L

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:25 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 699 expanded)
%              Number of leaves         :   37 ( 214 expanded)
%              Depth                    :   22
%              Number of atoms          :  940 (10848 expanded)
%              Number of equality atoms :   72 ( 785 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(t16_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
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
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( sk_D @ X21 @ X19 ) @ X19 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X21 )
        = X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('9',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X32: $i] :
      ( ~ ( r2_hidden @ X32 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X32 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf('16',plain,(
    ! [X32: $i] :
      ( ~ ( r2_hidden @ X32 @ sk_B )
      | ( X32
        = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( X9 = k1_xboole_0 )
      | ( X9
       != ( k1_funct_1 @ X8 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ X8 @ X7 )
        = k1_xboole_0 )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X10 ) @ X8 )
      | ( X10
       != ( k1_funct_1 @ X8 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( k1_funct_1 @ X8 @ X7 ) ) @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( sk_D @ sk_C @ sk_B ) ) @ sk_C )
    | ( ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( sk_D @ sk_C @ sk_B ) ) @ sk_C )
    | ( ( sk_D @ sk_C @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26','31'])).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ ( sk_D @ X21 @ X19 ) ) @ X21 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X21 )
        = X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ sk_C @ sk_B )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( ( sk_D @ sk_C @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','34'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( ( sk_D @ sk_C @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','35'])).

thf('37',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('38',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_E_1 @ k1_xboole_0 ) @ sk_A ),
    inference(demod,[status(thm)],['12','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('48',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('53',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_D @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('57',plain,(
    ~ ( r1_tarski @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['49','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','60'])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( k1_funct_1 @ X8 @ X7 ) ) @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ sk_C @ ( sk_E_1 @ k1_xboole_0 ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['39','66'])).

thf('68',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('69',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('70',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('71',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ sk_C ),
    inference(demod,[status(thm)],['67','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('75',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ ( sk_D @ X21 @ X19 ) ) @ X21 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X21 )
        = X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ k1_xboole_0 ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
        = sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ k1_xboole_0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C )
        = sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ k1_xboole_0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('81',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X0 @ k1_xboole_0 ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference('sup-',[status(thm)],['72','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4X3eXikT7L
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.70/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.93  % Solved by: fo/fo7.sh
% 0.70/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.93  % done 345 iterations in 0.474s
% 0.70/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.93  % SZS output start Refutation
% 0.70/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.70/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.93  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.70/0.93  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.70/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.93  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.70/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.70/0.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.70/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.70/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.70/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.93  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 0.70/0.93  thf(t16_funct_2, conjecture,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.70/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.93       ( ( ![D:$i]:
% 0.70/0.93           ( ~( ( r2_hidden @ D @ B ) & 
% 0.70/0.93                ( ![E:$i]:
% 0.70/0.93                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.70/0.93                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.70/0.93         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.70/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.93    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.93        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.70/0.93            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.93          ( ( ![D:$i]:
% 0.70/0.93              ( ~( ( r2_hidden @ D @ B ) & 
% 0.70/0.93                   ( ![E:$i]:
% 0.70/0.93                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.70/0.93                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.70/0.93            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.70/0.93    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.70/0.93  thf('0', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(t23_relset_1, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.93       ( ( ![D:$i]:
% 0.70/0.93           ( ~( ( r2_hidden @ D @ B ) & 
% 0.70/0.93                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.70/0.93         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.70/0.93  thf('1', plain,
% 0.70/0.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.70/0.93         ((r2_hidden @ (sk_D @ X21 @ X19) @ X19)
% 0.70/0.93          | ((k2_relset_1 @ X20 @ X19 @ X21) = (X19))
% 0.70/0.93          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.70/0.93      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.70/0.93  thf('2', plain,
% 0.70/0.93      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.70/0.93        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 0.70/0.93      inference('sup-', [status(thm)], ['0', '1'])).
% 0.70/0.93  thf('3', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(redefinition_k2_relset_1, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.93       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.70/0.93  thf('4', plain,
% 0.70/0.93      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.70/0.93         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.70/0.93          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.70/0.93  thf('5', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.93  thf('6', plain,
% 0.70/0.93      ((((k2_relat_1 @ sk_C) = (sk_B))
% 0.70/0.93        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 0.70/0.93      inference('demod', [status(thm)], ['2', '5'])).
% 0.70/0.93  thf('7', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.93  thf('9', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.70/0.93      inference('demod', [status(thm)], ['7', '8'])).
% 0.70/0.93  thf('10', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['6', '9'])).
% 0.70/0.93  thf('11', plain,
% 0.70/0.93      (![X32 : $i]:
% 0.70/0.93         (~ (r2_hidden @ X32 @ sk_B) | (r2_hidden @ (sk_E_1 @ X32) @ sk_A))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('12', plain, ((r2_hidden @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ sk_A)),
% 0.70/0.93      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.93  thf('13', plain,
% 0.70/0.93      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.93  thf('14', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('15', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['6', '9'])).
% 0.70/0.93  thf('16', plain,
% 0.70/0.93      (![X32 : $i]:
% 0.70/0.93         (~ (r2_hidden @ X32 @ sk_B)
% 0.70/0.93          | ((X32) = (k1_funct_1 @ sk_C @ (sk_E_1 @ X32))))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('17', plain,
% 0.70/0.93      (((sk_D @ sk_C @ sk_B)
% 0.70/0.93         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.93  thf(d4_funct_1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.93       ( ![B:$i,C:$i]:
% 0.70/0.93         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.70/0.93             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.70/0.93               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.70/0.93           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.70/0.93             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.70/0.93               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.70/0.93  thf('18', plain,
% 0.70/0.93      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.70/0.93         ((r2_hidden @ X7 @ (k1_relat_1 @ X8))
% 0.70/0.93          | ((X9) = (k1_xboole_0))
% 0.70/0.93          | ((X9) != (k1_funct_1 @ X8 @ X7))
% 0.70/0.93          | ~ (v1_funct_1 @ X8)
% 0.70/0.93          | ~ (v1_relat_1 @ X8))),
% 0.70/0.93      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.70/0.93  thf('19', plain,
% 0.70/0.93      (![X7 : $i, X8 : $i]:
% 0.70/0.93         (~ (v1_relat_1 @ X8)
% 0.70/0.93          | ~ (v1_funct_1 @ X8)
% 0.70/0.93          | ((k1_funct_1 @ X8 @ X7) = (k1_xboole_0))
% 0.70/0.93          | (r2_hidden @ X7 @ (k1_relat_1 @ X8)))),
% 0.70/0.93      inference('simplify', [status(thm)], ['18'])).
% 0.70/0.93  thf('20', plain,
% 0.70/0.93      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.70/0.93         (~ (r2_hidden @ X7 @ (k1_relat_1 @ X8))
% 0.70/0.93          | (r2_hidden @ (k4_tarski @ X7 @ X10) @ X8)
% 0.70/0.93          | ((X10) != (k1_funct_1 @ X8 @ X7))
% 0.70/0.93          | ~ (v1_funct_1 @ X8)
% 0.70/0.93          | ~ (v1_relat_1 @ X8))),
% 0.70/0.93      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.70/0.93  thf('21', plain,
% 0.70/0.93      (![X7 : $i, X8 : $i]:
% 0.70/0.93         (~ (v1_relat_1 @ X8)
% 0.70/0.93          | ~ (v1_funct_1 @ X8)
% 0.70/0.93          | (r2_hidden @ (k4_tarski @ X7 @ (k1_funct_1 @ X8 @ X7)) @ X8)
% 0.70/0.93          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X8)))),
% 0.70/0.93      inference('simplify', [status(thm)], ['20'])).
% 0.70/0.93  thf('22', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i]:
% 0.70/0.93         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.70/0.93          | ~ (v1_funct_1 @ X0)
% 0.70/0.93          | ~ (v1_relat_1 @ X0)
% 0.70/0.93          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.70/0.93          | ~ (v1_funct_1 @ X0)
% 0.70/0.93          | ~ (v1_relat_1 @ X0))),
% 0.70/0.93      inference('sup-', [status(thm)], ['19', '21'])).
% 0.70/0.93  thf('23', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i]:
% 0.70/0.93         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.70/0.93          | ~ (v1_relat_1 @ X0)
% 0.70/0.93          | ~ (v1_funct_1 @ X0)
% 0.70/0.93          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.70/0.93      inference('simplify', [status(thm)], ['22'])).
% 0.70/0.93  thf('24', plain,
% 0.70/0.93      (((r2_hidden @ 
% 0.70/0.93         (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ (sk_D @ sk_C @ sk_B)) @ 
% 0.70/0.93         sk_C)
% 0.70/0.93        | ((k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)))
% 0.70/0.93            = (k1_xboole_0))
% 0.70/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.70/0.93        | ~ (v1_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup+', [status(thm)], ['17', '23'])).
% 0.70/0.93  thf('25', plain,
% 0.70/0.93      (((sk_D @ sk_C @ sk_B)
% 0.70/0.93         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.93  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('27', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(cc2_relat_1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( v1_relat_1 @ A ) =>
% 0.70/0.93       ( ![B:$i]:
% 0.70/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.70/0.93  thf('28', plain,
% 0.70/0.93      (![X3 : $i, X4 : $i]:
% 0.70/0.93         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.70/0.93          | (v1_relat_1 @ X3)
% 0.70/0.93          | ~ (v1_relat_1 @ X4))),
% 0.70/0.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.70/0.93  thf('29', plain,
% 0.70/0.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['27', '28'])).
% 0.70/0.93  thf(fc6_relat_1, axiom,
% 0.70/0.93    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.70/0.93  thf('30', plain,
% 0.70/0.93      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.70/0.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.70/0.93  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.70/0.93      inference('demod', [status(thm)], ['29', '30'])).
% 0.70/0.93  thf('32', plain,
% 0.70/0.93      (((r2_hidden @ 
% 0.70/0.93         (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ (sk_D @ sk_C @ sk_B)) @ 
% 0.70/0.93         sk_C)
% 0.70/0.93        | ((sk_D @ sk_C @ sk_B) = (k1_xboole_0)))),
% 0.70/0.93      inference('demod', [status(thm)], ['24', '25', '26', '31'])).
% 0.70/0.93  thf('33', plain,
% 0.70/0.93      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.70/0.93         (~ (r2_hidden @ (k4_tarski @ X23 @ (sk_D @ X21 @ X19)) @ X21)
% 0.70/0.93          | ((k2_relset_1 @ X20 @ X19 @ X21) = (X19))
% 0.70/0.93          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.70/0.93      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.70/0.93  thf('34', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (((sk_D @ sk_C @ sk_B) = (k1_xboole_0))
% 0.70/0.93          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.70/0.93          | ((k2_relset_1 @ X0 @ sk_B @ sk_C) = (sk_B)))),
% 0.70/0.93      inference('sup-', [status(thm)], ['32', '33'])).
% 0.70/0.93  thf('35', plain,
% 0.70/0.93      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.70/0.93        | ((sk_D @ sk_C @ sk_B) = (k1_xboole_0)))),
% 0.70/0.93      inference('sup-', [status(thm)], ['14', '34'])).
% 0.70/0.93  thf('36', plain,
% 0.70/0.93      ((((k2_relat_1 @ sk_C) = (sk_B)) | ((sk_D @ sk_C @ sk_B) = (k1_xboole_0)))),
% 0.70/0.93      inference('sup+', [status(thm)], ['13', '35'])).
% 0.70/0.93  thf('37', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.70/0.93      inference('demod', [status(thm)], ['7', '8'])).
% 0.70/0.93  thf('38', plain, (((sk_D @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.70/0.93  thf('39', plain, ((r2_hidden @ (sk_E_1 @ k1_xboole_0) @ sk_A)),
% 0.70/0.93      inference('demod', [status(thm)], ['12', '38'])).
% 0.70/0.93  thf('40', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(d1_funct_2, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.70/0.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.70/0.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.70/0.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.70/0.93  thf(zf_stmt_1, axiom,
% 0.70/0.93    (![C:$i,B:$i,A:$i]:
% 0.70/0.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.70/0.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.70/0.93  thf('41', plain,
% 0.70/0.93      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.70/0.93         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.70/0.93          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.70/0.93          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.70/0.93  thf('42', plain,
% 0.70/0.93      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.70/0.93        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.70/0.93      inference('sup-', [status(thm)], ['40', '41'])).
% 0.70/0.93  thf('43', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(redefinition_k1_relset_1, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.70/0.93  thf('44', plain,
% 0.70/0.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.70/0.93         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.70/0.93          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.93  thf('45', plain,
% 0.70/0.93      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['43', '44'])).
% 0.70/0.93  thf('46', plain,
% 0.70/0.93      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.70/0.93      inference('demod', [status(thm)], ['42', '45'])).
% 0.70/0.93  thf('47', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.70/0.93  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.70/0.93  thf(zf_stmt_4, axiom,
% 0.70/0.93    (![B:$i,A:$i]:
% 0.70/0.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.93       ( zip_tseitin_0 @ B @ A ) ))).
% 0.70/0.93  thf(zf_stmt_5, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.70/0.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.70/0.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.70/0.93  thf('48', plain,
% 0.70/0.93      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.70/0.93         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.70/0.93          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.70/0.93          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.70/0.93  thf('49', plain,
% 0.70/0.93      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.70/0.93      inference('sup-', [status(thm)], ['47', '48'])).
% 0.70/0.93  thf(d10_xboole_0, axiom,
% 0.70/0.93    (![A:$i,B:$i]:
% 0.70/0.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.93  thf('50', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.70/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.93  thf('51', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.70/0.93      inference('simplify', [status(thm)], ['50'])).
% 0.70/0.93  thf('52', plain,
% 0.70/0.93      (![X24 : $i, X25 : $i]:
% 0.70/0.93         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.70/0.93  thf('53', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['6', '9'])).
% 0.70/0.93  thf(t7_ordinal1, axiom,
% 0.70/0.93    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.93  thf('54', plain,
% 0.70/0.93      (![X11 : $i, X12 : $i]:
% 0.70/0.93         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.70/0.93      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.70/0.93  thf('55', plain, (~ (r1_tarski @ sk_B @ (sk_D @ sk_C @ sk_B))),
% 0.70/0.93      inference('sup-', [status(thm)], ['53', '54'])).
% 0.70/0.93  thf('56', plain, (((sk_D @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.70/0.93  thf('57', plain, (~ (r1_tarski @ sk_B @ k1_xboole_0)),
% 0.70/0.93      inference('demod', [status(thm)], ['55', '56'])).
% 0.70/0.93  thf('58', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i]:
% 0.70/0.93         (~ (r1_tarski @ sk_B @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.70/0.93      inference('sup-', [status(thm)], ['52', '57'])).
% 0.70/0.93  thf('59', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.70/0.93      inference('sup-', [status(thm)], ['51', '58'])).
% 0.70/0.93  thf('60', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.70/0.93      inference('demod', [status(thm)], ['49', '59'])).
% 0.70/0.93  thf('61', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.70/0.93      inference('demod', [status(thm)], ['46', '60'])).
% 0.70/0.93  thf('62', plain,
% 0.70/0.93      (![X7 : $i, X8 : $i]:
% 0.70/0.93         (~ (v1_relat_1 @ X8)
% 0.70/0.93          | ~ (v1_funct_1 @ X8)
% 0.70/0.93          | (r2_hidden @ (k4_tarski @ X7 @ (k1_funct_1 @ X8 @ X7)) @ X8)
% 0.70/0.93          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X8)))),
% 0.70/0.93      inference('simplify', [status(thm)], ['20'])).
% 0.70/0.93  thf('63', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (~ (r2_hidden @ X0 @ sk_A)
% 0.70/0.93          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C)
% 0.70/0.93          | ~ (v1_funct_1 @ sk_C)
% 0.70/0.93          | ~ (v1_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['61', '62'])).
% 0.70/0.93  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.70/0.93      inference('demod', [status(thm)], ['29', '30'])).
% 0.70/0.93  thf('66', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (~ (r2_hidden @ X0 @ sk_A)
% 0.70/0.93          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C))),
% 0.70/0.93      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.70/0.93  thf('67', plain,
% 0.70/0.93      ((r2_hidden @ 
% 0.70/0.93        (k4_tarski @ (sk_E_1 @ k1_xboole_0) @ 
% 0.70/0.93         (k1_funct_1 @ sk_C @ (sk_E_1 @ k1_xboole_0))) @ 
% 0.70/0.93        sk_C)),
% 0.70/0.93      inference('sup-', [status(thm)], ['39', '66'])).
% 0.70/0.93  thf('68', plain,
% 0.70/0.93      (((sk_D @ sk_C @ sk_B)
% 0.70/0.93         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.93  thf('69', plain, (((sk_D @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.70/0.93  thf('70', plain, (((sk_D @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.70/0.93  thf('71', plain,
% 0.70/0.93      (((k1_xboole_0) = (k1_funct_1 @ sk_C @ (sk_E_1 @ k1_xboole_0)))),
% 0.70/0.93      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.70/0.93  thf('72', plain,
% 0.70/0.93      ((r2_hidden @ (k4_tarski @ (sk_E_1 @ k1_xboole_0) @ k1_xboole_0) @ sk_C)),
% 0.70/0.93      inference('demod', [status(thm)], ['67', '71'])).
% 0.70/0.93  thf('73', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('74', plain, (((sk_D @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.70/0.93  thf('75', plain,
% 0.70/0.93      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.70/0.93         (~ (r2_hidden @ (k4_tarski @ X23 @ (sk_D @ X21 @ X19)) @ X21)
% 0.70/0.93          | ((k2_relset_1 @ X20 @ X19 @ X21) = (X19))
% 0.70/0.93          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.70/0.93      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.70/0.93  thf('76', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i]:
% 0.70/0.93         (~ (r2_hidden @ (k4_tarski @ X0 @ k1_xboole_0) @ sk_C)
% 0.70/0.93          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.70/0.93          | ((k2_relset_1 @ X1 @ sk_B @ sk_C) = (sk_B)))),
% 0.70/0.93      inference('sup-', [status(thm)], ['74', '75'])).
% 0.70/0.93  thf('77', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.70/0.93          | ~ (r2_hidden @ (k4_tarski @ X0 @ k1_xboole_0) @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['73', '76'])).
% 0.70/0.93  thf('78', plain,
% 0.70/0.93      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.93  thf('79', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (((k2_relat_1 @ sk_C) = (sk_B))
% 0.70/0.93          | ~ (r2_hidden @ (k4_tarski @ X0 @ k1_xboole_0) @ sk_C))),
% 0.70/0.93      inference('demod', [status(thm)], ['77', '78'])).
% 0.70/0.93  thf('80', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.70/0.93      inference('demod', [status(thm)], ['7', '8'])).
% 0.70/0.93  thf('81', plain,
% 0.70/0.93      (![X0 : $i]: ~ (r2_hidden @ (k4_tarski @ X0 @ k1_xboole_0) @ sk_C)),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.70/0.93  thf('82', plain, ($false), inference('sup-', [status(thm)], ['72', '81'])).
% 0.70/0.93  
% 0.70/0.93  % SZS output end Refutation
% 0.70/0.93  
% 0.77/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
