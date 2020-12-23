%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j8A3wq8xLH

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:18 EST 2020

% Result     : Theorem 5.84s
% Output     : Refutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  127 (1347 expanded)
%              Number of leaves         :   40 ( 397 expanded)
%              Depth                    :   25
%              Number of atoms          : 1028 (20133 expanded)
%              Number of equality atoms :   70 (1283 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( ( sk_C_1 @ X7 @ X8 )
        = ( k1_funct_1 @ X8 @ ( sk_D @ X7 @ X8 ) ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X8: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( X12
       != ( k1_funct_1 @ X8 @ X13 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X8: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X13 ) @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['12','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

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

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('32',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('44',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B )
      | ( X34
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_1 @ sk_B @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( ( sk_C_1 @ X7 @ X8 )
       != ( k1_funct_1 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['24','27'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_C_2 )
     != ( sk_C_1 @ sk_B @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','55'])).

thf('57',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('58',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X34 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','59'])).

thf('62',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','60','61'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('63',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('68',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('71',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('72',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ k1_xboole_0 @ sk_C_2 )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('75',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','59'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ k1_xboole_0 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_C_2 )
     != ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('79',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_C_2 )
     != ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['69','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('84',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['82','83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j8A3wq8xLH
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 5.84/6.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.84/6.09  % Solved by: fo/fo7.sh
% 5.84/6.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.84/6.09  % done 1848 iterations in 5.646s
% 5.84/6.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.84/6.09  % SZS output start Refutation
% 5.84/6.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.84/6.09  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 5.84/6.09  thf(sk_E_type, type, sk_E: $i > $i).
% 5.84/6.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.84/6.09  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.84/6.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.84/6.09  thf(sk_A_type, type, sk_A: $i).
% 5.84/6.09  thf(sk_B_type, type, sk_B: $i).
% 5.84/6.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.84/6.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.84/6.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.84/6.09  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 5.84/6.09  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.84/6.09  thf(sk_C_2_type, type, sk_C_2: $i).
% 5.84/6.09  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.84/6.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.84/6.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.84/6.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.84/6.09  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.84/6.09  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.84/6.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.84/6.09  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.84/6.09  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 5.84/6.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.84/6.09  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.84/6.09  thf(d5_funct_1, axiom,
% 5.84/6.09    (![A:$i]:
% 5.84/6.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.84/6.09       ( ![B:$i]:
% 5.84/6.09         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 5.84/6.09           ( ![C:$i]:
% 5.84/6.09             ( ( r2_hidden @ C @ B ) <=>
% 5.84/6.09               ( ?[D:$i]:
% 5.84/6.09                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 5.84/6.09                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 5.84/6.09  thf('0', plain,
% 5.84/6.09      (![X7 : $i, X8 : $i]:
% 5.84/6.09         ((r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 5.84/6.09          | ((sk_C_1 @ X7 @ X8) = (k1_funct_1 @ X8 @ (sk_D @ X7 @ X8)))
% 5.84/6.09          | ((X7) = (k2_relat_1 @ X8))
% 5.84/6.09          | ~ (v1_funct_1 @ X8)
% 5.84/6.09          | ~ (v1_relat_1 @ X8))),
% 5.84/6.09      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.84/6.09  thf('1', plain,
% 5.84/6.09      (![X7 : $i, X8 : $i]:
% 5.84/6.09         ((r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 5.84/6.09          | (r2_hidden @ (sk_D @ X7 @ X8) @ (k1_relat_1 @ X8))
% 5.84/6.09          | ((X7) = (k2_relat_1 @ X8))
% 5.84/6.09          | ~ (v1_funct_1 @ X8)
% 5.84/6.09          | ~ (v1_relat_1 @ X8))),
% 5.84/6.09      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.84/6.09  thf('2', plain,
% 5.84/6.09      (![X8 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 5.84/6.09         (((X10) != (k2_relat_1 @ X8))
% 5.84/6.09          | (r2_hidden @ X12 @ X10)
% 5.84/6.09          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 5.84/6.09          | ((X12) != (k1_funct_1 @ X8 @ X13))
% 5.84/6.09          | ~ (v1_funct_1 @ X8)
% 5.84/6.09          | ~ (v1_relat_1 @ X8))),
% 5.84/6.09      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.84/6.09  thf('3', plain,
% 5.84/6.09      (![X8 : $i, X13 : $i]:
% 5.84/6.09         (~ (v1_relat_1 @ X8)
% 5.84/6.09          | ~ (v1_funct_1 @ X8)
% 5.84/6.09          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 5.84/6.09          | (r2_hidden @ (k1_funct_1 @ X8 @ X13) @ (k2_relat_1 @ X8)))),
% 5.84/6.09      inference('simplify', [status(thm)], ['2'])).
% 5.84/6.09  thf('4', plain,
% 5.84/6.09      (![X0 : $i, X1 : $i]:
% 5.84/6.09         (~ (v1_relat_1 @ X0)
% 5.84/6.09          | ~ (v1_funct_1 @ X0)
% 5.84/6.09          | ((X1) = (k2_relat_1 @ X0))
% 5.84/6.09          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 5.84/6.09          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 5.84/6.09             (k2_relat_1 @ X0))
% 5.84/6.09          | ~ (v1_funct_1 @ X0)
% 5.84/6.09          | ~ (v1_relat_1 @ X0))),
% 5.84/6.09      inference('sup-', [status(thm)], ['1', '3'])).
% 5.84/6.09  thf('5', plain,
% 5.84/6.09      (![X0 : $i, X1 : $i]:
% 5.84/6.09         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 5.84/6.09          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 5.84/6.09          | ((X1) = (k2_relat_1 @ X0))
% 5.84/6.09          | ~ (v1_funct_1 @ X0)
% 5.84/6.09          | ~ (v1_relat_1 @ X0))),
% 5.84/6.09      inference('simplify', [status(thm)], ['4'])).
% 5.84/6.09  thf('6', plain,
% 5.84/6.09      (![X0 : $i, X1 : $i]:
% 5.84/6.09         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 5.84/6.09          | ~ (v1_relat_1 @ X0)
% 5.84/6.09          | ~ (v1_funct_1 @ X0)
% 5.84/6.09          | ((X1) = (k2_relat_1 @ X0))
% 5.84/6.09          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 5.84/6.09          | ~ (v1_relat_1 @ X0)
% 5.84/6.09          | ~ (v1_funct_1 @ X0)
% 5.84/6.09          | ((X1) = (k2_relat_1 @ X0))
% 5.84/6.09          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 5.84/6.09      inference('sup+', [status(thm)], ['0', '5'])).
% 5.84/6.09  thf('7', plain,
% 5.84/6.09      (![X0 : $i, X1 : $i]:
% 5.84/6.09         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 5.84/6.09          | ((X1) = (k2_relat_1 @ X0))
% 5.84/6.09          | ~ (v1_funct_1 @ X0)
% 5.84/6.09          | ~ (v1_relat_1 @ X0)
% 5.84/6.09          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 5.84/6.09      inference('simplify', [status(thm)], ['6'])).
% 5.84/6.09  thf(t16_funct_2, conjecture,
% 5.84/6.09    (![A:$i,B:$i,C:$i]:
% 5.84/6.09     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.84/6.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.84/6.09       ( ( ![D:$i]:
% 5.84/6.09           ( ~( ( r2_hidden @ D @ B ) & 
% 5.84/6.09                ( ![E:$i]:
% 5.84/6.09                  ( ~( ( r2_hidden @ E @ A ) & 
% 5.84/6.09                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 5.84/6.09         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 5.84/6.09  thf(zf_stmt_0, negated_conjecture,
% 5.84/6.09    (~( ![A:$i,B:$i,C:$i]:
% 5.84/6.09        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.84/6.09            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.84/6.09          ( ( ![D:$i]:
% 5.84/6.09              ( ~( ( r2_hidden @ D @ B ) & 
% 5.84/6.09                   ( ![E:$i]:
% 5.84/6.09                     ( ~( ( r2_hidden @ E @ A ) & 
% 5.84/6.09                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 5.84/6.09            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 5.84/6.09    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 5.84/6.09  thf('8', plain,
% 5.84/6.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf(cc2_relset_1, axiom,
% 5.84/6.09    (![A:$i,B:$i,C:$i]:
% 5.84/6.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.84/6.09       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.84/6.09  thf('9', plain,
% 5.84/6.09      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.84/6.09         ((v5_relat_1 @ X17 @ X19)
% 5.84/6.09          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.84/6.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.84/6.09  thf('10', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 5.84/6.09      inference('sup-', [status(thm)], ['8', '9'])).
% 5.84/6.09  thf(d19_relat_1, axiom,
% 5.84/6.09    (![A:$i,B:$i]:
% 5.84/6.09     ( ( v1_relat_1 @ B ) =>
% 5.84/6.09       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 5.84/6.09  thf('11', plain,
% 5.84/6.09      (![X5 : $i, X6 : $i]:
% 5.84/6.09         (~ (v5_relat_1 @ X5 @ X6)
% 5.84/6.09          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 5.84/6.09          | ~ (v1_relat_1 @ X5))),
% 5.84/6.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.84/6.09  thf('12', plain,
% 5.84/6.09      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 5.84/6.09      inference('sup-', [status(thm)], ['10', '11'])).
% 5.84/6.09  thf('13', plain,
% 5.84/6.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf(cc1_relset_1, axiom,
% 5.84/6.09    (![A:$i,B:$i,C:$i]:
% 5.84/6.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.84/6.09       ( v1_relat_1 @ C ) ))).
% 5.84/6.09  thf('14', plain,
% 5.84/6.09      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.84/6.09         ((v1_relat_1 @ X14)
% 5.84/6.09          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 5.84/6.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.84/6.09  thf('15', plain, ((v1_relat_1 @ sk_C_2)),
% 5.84/6.09      inference('sup-', [status(thm)], ['13', '14'])).
% 5.84/6.09  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 5.84/6.09      inference('demod', [status(thm)], ['12', '15'])).
% 5.84/6.09  thf(d3_tarski, axiom,
% 5.84/6.09    (![A:$i,B:$i]:
% 5.84/6.09     ( ( r1_tarski @ A @ B ) <=>
% 5.84/6.09       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.84/6.09  thf('17', plain,
% 5.84/6.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.84/6.09         (~ (r2_hidden @ X0 @ X1)
% 5.84/6.09          | (r2_hidden @ X0 @ X2)
% 5.84/6.09          | ~ (r1_tarski @ X1 @ X2))),
% 5.84/6.09      inference('cnf', [status(esa)], [d3_tarski])).
% 5.84/6.09  thf('18', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 5.84/6.09      inference('sup-', [status(thm)], ['16', '17'])).
% 5.84/6.09  thf('19', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         (~ (v1_relat_1 @ sk_C_2)
% 5.84/6.09          | ~ (v1_funct_1 @ sk_C_2)
% 5.84/6.09          | ((X0) = (k2_relat_1 @ sk_C_2))
% 5.84/6.09          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 5.84/6.09          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 5.84/6.09      inference('sup-', [status(thm)], ['7', '18'])).
% 5.84/6.09  thf('20', plain, ((v1_relat_1 @ sk_C_2)),
% 5.84/6.09      inference('sup-', [status(thm)], ['13', '14'])).
% 5.84/6.09  thf('21', plain, ((v1_funct_1 @ sk_C_2)),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf('22', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         (((X0) = (k2_relat_1 @ sk_C_2))
% 5.84/6.09          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 5.84/6.09          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 5.84/6.09      inference('demod', [status(thm)], ['19', '20', '21'])).
% 5.84/6.09  thf('23', plain,
% 5.84/6.09      (((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 5.84/6.09        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 5.84/6.09      inference('eq_fact', [status(thm)], ['22'])).
% 5.84/6.09  thf('24', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf('25', plain,
% 5.84/6.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf(redefinition_k2_relset_1, axiom,
% 5.84/6.09    (![A:$i,B:$i,C:$i]:
% 5.84/6.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.84/6.09       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.84/6.09  thf('26', plain,
% 5.84/6.09      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.84/6.09         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 5.84/6.09          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 5.84/6.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.84/6.09  thf('27', plain,
% 5.84/6.09      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 5.84/6.09      inference('sup-', [status(thm)], ['25', '26'])).
% 5.84/6.09  thf('28', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 5.84/6.09      inference('demod', [status(thm)], ['24', '27'])).
% 5.84/6.09  thf('29', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 5.84/6.09      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 5.84/6.09  thf(d1_funct_2, axiom,
% 5.84/6.09    (![A:$i,B:$i,C:$i]:
% 5.84/6.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.84/6.09       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.84/6.09           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.84/6.09             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.84/6.09         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.84/6.09           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.84/6.09             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.84/6.09  thf(zf_stmt_1, axiom,
% 5.84/6.09    (![B:$i,A:$i]:
% 5.84/6.09     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.84/6.09       ( zip_tseitin_0 @ B @ A ) ))).
% 5.84/6.09  thf('30', plain,
% 5.84/6.09      (![X26 : $i, X27 : $i]:
% 5.84/6.09         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.84/6.09  thf('31', plain,
% 5.84/6.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.84/6.09  thf(zf_stmt_3, axiom,
% 5.84/6.09    (![C:$i,B:$i,A:$i]:
% 5.84/6.09     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.84/6.09       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.84/6.09  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.84/6.09  thf(zf_stmt_5, axiom,
% 5.84/6.09    (![A:$i,B:$i,C:$i]:
% 5.84/6.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.84/6.09       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.84/6.09         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.84/6.09           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.84/6.09             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.84/6.09  thf('32', plain,
% 5.84/6.09      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.84/6.09         (~ (zip_tseitin_0 @ X31 @ X32)
% 5.84/6.09          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 5.84/6.09          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.84/6.09  thf('33', plain,
% 5.84/6.09      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 5.84/6.09        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.84/6.09      inference('sup-', [status(thm)], ['31', '32'])).
% 5.84/6.09  thf('34', plain,
% 5.84/6.09      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 5.84/6.09      inference('sup-', [status(thm)], ['30', '33'])).
% 5.84/6.09  thf('35', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf('36', plain,
% 5.84/6.09      (![X28 : $i, X29 : $i, X30 : $i]:
% 5.84/6.09         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 5.84/6.09          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 5.84/6.09          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.84/6.09  thf('37', plain,
% 5.84/6.09      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 5.84/6.09        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 5.84/6.09      inference('sup-', [status(thm)], ['35', '36'])).
% 5.84/6.09  thf('38', plain,
% 5.84/6.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf(redefinition_k1_relset_1, axiom,
% 5.84/6.09    (![A:$i,B:$i,C:$i]:
% 5.84/6.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.84/6.09       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.84/6.09  thf('39', plain,
% 5.84/6.09      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.84/6.09         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 5.84/6.09          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.84/6.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.84/6.09  thf('40', plain,
% 5.84/6.09      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 5.84/6.09      inference('sup-', [status(thm)], ['38', '39'])).
% 5.84/6.09  thf('41', plain,
% 5.84/6.09      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 5.84/6.09        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 5.84/6.09      inference('demod', [status(thm)], ['37', '40'])).
% 5.84/6.09  thf('42', plain,
% 5.84/6.09      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 5.84/6.09      inference('sup-', [status(thm)], ['34', '41'])).
% 5.84/6.09  thf('43', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 5.84/6.09      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 5.84/6.09  thf('44', plain,
% 5.84/6.09      (![X34 : $i]:
% 5.84/6.09         (~ (r2_hidden @ X34 @ sk_B)
% 5.84/6.09          | ((X34) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X34))))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf('45', plain,
% 5.84/6.09      (((sk_C_1 @ sk_B @ sk_C_2)
% 5.84/6.09         = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2))))),
% 5.84/6.09      inference('sup-', [status(thm)], ['43', '44'])).
% 5.84/6.09  thf('46', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 5.84/6.09      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 5.84/6.09  thf('47', plain,
% 5.84/6.09      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.84/6.09         (~ (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 5.84/6.09          | ((sk_C_1 @ X7 @ X8) != (k1_funct_1 @ X8 @ X9))
% 5.84/6.09          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 5.84/6.09          | ((X7) = (k2_relat_1 @ X8))
% 5.84/6.09          | ~ (v1_funct_1 @ X8)
% 5.84/6.09          | ~ (v1_relat_1 @ X8))),
% 5.84/6.09      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.84/6.09  thf('48', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         (~ (v1_relat_1 @ sk_C_2)
% 5.84/6.09          | ~ (v1_funct_1 @ sk_C_2)
% 5.84/6.09          | ((sk_B) = (k2_relat_1 @ sk_C_2))
% 5.84/6.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 5.84/6.09          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 5.84/6.09      inference('sup-', [status(thm)], ['46', '47'])).
% 5.84/6.09  thf('49', plain, ((v1_relat_1 @ sk_C_2)),
% 5.84/6.09      inference('sup-', [status(thm)], ['13', '14'])).
% 5.84/6.09  thf('50', plain, ((v1_funct_1 @ sk_C_2)),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf('51', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         (((sk_B) = (k2_relat_1 @ sk_C_2))
% 5.84/6.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 5.84/6.09          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 5.84/6.09      inference('demod', [status(thm)], ['48', '49', '50'])).
% 5.84/6.09  thf('52', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 5.84/6.09      inference('demod', [status(thm)], ['24', '27'])).
% 5.84/6.09  thf('53', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 5.84/6.09          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 5.84/6.09      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 5.84/6.09  thf('54', plain,
% 5.84/6.09      ((((sk_C_1 @ sk_B @ sk_C_2) != (sk_C_1 @ sk_B @ sk_C_2))
% 5.84/6.09        | ~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 5.84/6.09             (k1_relat_1 @ sk_C_2)))),
% 5.84/6.09      inference('sup-', [status(thm)], ['45', '53'])).
% 5.84/6.09  thf('55', plain,
% 5.84/6.09      (~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ (k1_relat_1 @ sk_C_2))),
% 5.84/6.09      inference('simplify', [status(thm)], ['54'])).
% 5.84/6.09  thf('56', plain,
% 5.84/6.09      ((~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A)
% 5.84/6.09        | ((sk_B) = (k1_xboole_0)))),
% 5.84/6.09      inference('sup-', [status(thm)], ['42', '55'])).
% 5.84/6.09  thf('57', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 5.84/6.09      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 5.84/6.09  thf('58', plain,
% 5.84/6.09      (![X34 : $i]:
% 5.84/6.09         (~ (r2_hidden @ X34 @ sk_B) | (r2_hidden @ (sk_E @ X34) @ sk_A))),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf('59', plain, ((r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A)),
% 5.84/6.09      inference('sup-', [status(thm)], ['57', '58'])).
% 5.84/6.09  thf('60', plain, (((sk_B) = (k1_xboole_0))),
% 5.84/6.09      inference('demod', [status(thm)], ['56', '59'])).
% 5.84/6.09  thf('61', plain, (((sk_B) = (k1_xboole_0))),
% 5.84/6.09      inference('demod', [status(thm)], ['56', '59'])).
% 5.84/6.09  thf('62', plain,
% 5.84/6.09      ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ k1_xboole_0)),
% 5.84/6.09      inference('demod', [status(thm)], ['29', '60', '61'])).
% 5.84/6.09  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.84/6.09  thf('63', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 5.84/6.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.84/6.09  thf('64', plain,
% 5.84/6.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.84/6.09         (~ (r2_hidden @ X0 @ X1)
% 5.84/6.09          | (r2_hidden @ X0 @ X2)
% 5.84/6.09          | ~ (r1_tarski @ X1 @ X2))),
% 5.84/6.09      inference('cnf', [status(esa)], [d3_tarski])).
% 5.84/6.09  thf('65', plain,
% 5.84/6.09      (![X0 : $i, X1 : $i]:
% 5.84/6.09         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.84/6.09      inference('sup-', [status(thm)], ['63', '64'])).
% 5.84/6.09  thf('66', plain,
% 5.84/6.09      (![X0 : $i]: (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ X0)),
% 5.84/6.09      inference('sup-', [status(thm)], ['62', '65'])).
% 5.84/6.09  thf('67', plain,
% 5.84/6.09      (![X8 : $i, X10 : $i, X11 : $i]:
% 5.84/6.09         (((X10) != (k2_relat_1 @ X8))
% 5.84/6.09          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8))
% 5.84/6.09          | ~ (r2_hidden @ X11 @ X10)
% 5.84/6.09          | ~ (v1_funct_1 @ X8)
% 5.84/6.09          | ~ (v1_relat_1 @ X8))),
% 5.84/6.09      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.84/6.09  thf('68', plain,
% 5.84/6.09      (![X8 : $i, X11 : $i]:
% 5.84/6.09         (~ (v1_relat_1 @ X8)
% 5.84/6.09          | ~ (v1_funct_1 @ X8)
% 5.84/6.09          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 5.84/6.09          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8)))),
% 5.84/6.09      inference('simplify', [status(thm)], ['67'])).
% 5.84/6.09  thf('69', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ X0) @ 
% 5.84/6.09           (k1_relat_1 @ X0))
% 5.84/6.09          | ~ (v1_funct_1 @ X0)
% 5.84/6.09          | ~ (v1_relat_1 @ X0))),
% 5.84/6.09      inference('sup-', [status(thm)], ['66', '68'])).
% 5.84/6.09  thf('70', plain,
% 5.84/6.09      (![X0 : $i]: (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ X0)),
% 5.84/6.09      inference('sup-', [status(thm)], ['62', '65'])).
% 5.84/6.09  thf('71', plain,
% 5.84/6.09      (![X8 : $i, X10 : $i, X11 : $i]:
% 5.84/6.09         (((X10) != (k2_relat_1 @ X8))
% 5.84/6.09          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8)))
% 5.84/6.09          | ~ (r2_hidden @ X11 @ X10)
% 5.84/6.09          | ~ (v1_funct_1 @ X8)
% 5.84/6.09          | ~ (v1_relat_1 @ X8))),
% 5.84/6.09      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.84/6.09  thf('72', plain,
% 5.84/6.09      (![X8 : $i, X11 : $i]:
% 5.84/6.09         (~ (v1_relat_1 @ X8)
% 5.84/6.09          | ~ (v1_funct_1 @ X8)
% 5.84/6.09          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 5.84/6.09          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 5.84/6.09      inference('simplify', [status(thm)], ['71'])).
% 5.84/6.09  thf('73', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         (((sk_C_1 @ k1_xboole_0 @ sk_C_2)
% 5.84/6.09            = (k1_funct_1 @ X0 @ 
% 5.84/6.09               (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ X0)))
% 5.84/6.09          | ~ (v1_funct_1 @ X0)
% 5.84/6.09          | ~ (v1_relat_1 @ X0))),
% 5.84/6.09      inference('sup-', [status(thm)], ['70', '72'])).
% 5.84/6.09  thf('74', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 5.84/6.09          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 5.84/6.09      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 5.84/6.09  thf('75', plain, (((sk_B) = (k1_xboole_0))),
% 5.84/6.09      inference('demod', [status(thm)], ['56', '59'])).
% 5.84/6.09  thf('76', plain,
% 5.84/6.09      (![X0 : $i]:
% 5.84/6.09         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 5.84/6.09          | ((sk_C_1 @ k1_xboole_0 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 5.84/6.09      inference('demod', [status(thm)], ['74', '75'])).
% 5.84/6.09  thf('77', plain,
% 5.84/6.09      ((((sk_C_1 @ k1_xboole_0 @ sk_C_2) != (sk_C_1 @ k1_xboole_0 @ sk_C_2))
% 5.84/6.09        | ~ (v1_relat_1 @ sk_C_2)
% 5.84/6.09        | ~ (v1_funct_1 @ sk_C_2)
% 5.84/6.09        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ sk_C_2) @ 
% 5.84/6.09             (k1_relat_1 @ sk_C_2)))),
% 5.84/6.09      inference('sup-', [status(thm)], ['73', '76'])).
% 5.84/6.09  thf('78', plain, ((v1_relat_1 @ sk_C_2)),
% 5.84/6.09      inference('sup-', [status(thm)], ['13', '14'])).
% 5.84/6.09  thf('79', plain, ((v1_funct_1 @ sk_C_2)),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf('80', plain,
% 5.84/6.09      ((((sk_C_1 @ k1_xboole_0 @ sk_C_2) != (sk_C_1 @ k1_xboole_0 @ sk_C_2))
% 5.84/6.09        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ sk_C_2) @ 
% 5.84/6.09             (k1_relat_1 @ sk_C_2)))),
% 5.84/6.09      inference('demod', [status(thm)], ['77', '78', '79'])).
% 5.84/6.09  thf('81', plain,
% 5.84/6.09      (~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ sk_C_2) @ 
% 5.84/6.09          (k1_relat_1 @ sk_C_2))),
% 5.84/6.09      inference('simplify', [status(thm)], ['80'])).
% 5.84/6.09  thf('82', plain, ((~ (v1_relat_1 @ sk_C_2) | ~ (v1_funct_1 @ sk_C_2))),
% 5.84/6.09      inference('sup-', [status(thm)], ['69', '81'])).
% 5.84/6.09  thf('83', plain, ((v1_relat_1 @ sk_C_2)),
% 5.84/6.09      inference('sup-', [status(thm)], ['13', '14'])).
% 5.84/6.09  thf('84', plain, ((v1_funct_1 @ sk_C_2)),
% 5.84/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.09  thf('85', plain, ($false),
% 5.84/6.09      inference('demod', [status(thm)], ['82', '83', '84'])).
% 5.84/6.09  
% 5.84/6.09  % SZS output end Refutation
% 5.84/6.09  
% 5.96/6.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
