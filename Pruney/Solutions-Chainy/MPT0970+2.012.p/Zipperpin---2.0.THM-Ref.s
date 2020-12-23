%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IGAfG9BFHY

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:18 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 305 expanded)
%              Number of leaves         :   41 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          :  835 (4205 expanded)
%              Number of equality atoms :   59 ( 269 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( ( sk_C_1 @ X9 @ X10 )
        = ( k1_funct_1 @ X10 @ ( sk_D @ X9 @ X10 ) ) )
      | ( X9
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X9 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ( X9
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X10: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X10 ) )
      | ( X14
       != ( k1_funct_1 @ X10 @ X15 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X10: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X10 @ X15 ) @ ( k2_relat_1 @ X10 ) ) ) ),
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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['12','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B_1 ) ) ),
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
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

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

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('34',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('46',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ sk_B_1 )
      | ( X36
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( ( sk_C_1 @ X9 @ X10 )
       != ( k1_funct_1 @ X10 @ X11 ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X10 ) )
      | ( X9
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B_1
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B_1 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B_1 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['24','27'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B_1 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( sk_C_1 @ sk_B_1 @ sk_C_2 )
     != ( sk_C_1 @ sk_B_1 @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','57'])).

thf('59',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('60',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ sk_B_1 )
      | ( r2_hidden @ ( sk_E @ X36 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','61'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['31','62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IGAfG9BFHY
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.65/2.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.65/2.87  % Solved by: fo/fo7.sh
% 2.65/2.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.65/2.87  % done 1750 iterations in 2.404s
% 2.65/2.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.65/2.87  % SZS output start Refutation
% 2.65/2.87  thf(sk_A_type, type, sk_A: $i).
% 2.65/2.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.65/2.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.65/2.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.65/2.87  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.65/2.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.65/2.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.65/2.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.65/2.87  thf(sk_E_type, type, sk_E: $i > $i).
% 2.65/2.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.65/2.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.65/2.87  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 2.65/2.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.65/2.87  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.65/2.87  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.65/2.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.65/2.87  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.65/2.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.65/2.87  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.65/2.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.65/2.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.65/2.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.65/2.87  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.65/2.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.65/2.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.65/2.87  thf(d5_funct_1, axiom,
% 2.65/2.87    (![A:$i]:
% 2.65/2.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.65/2.87       ( ![B:$i]:
% 2.65/2.87         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.65/2.87           ( ![C:$i]:
% 2.65/2.87             ( ( r2_hidden @ C @ B ) <=>
% 2.65/2.87               ( ?[D:$i]:
% 2.65/2.87                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 2.65/2.87                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 2.65/2.87  thf('0', plain,
% 2.65/2.87      (![X9 : $i, X10 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 2.65/2.87          | ((sk_C_1 @ X9 @ X10) = (k1_funct_1 @ X10 @ (sk_D @ X9 @ X10)))
% 2.65/2.87          | ((X9) = (k2_relat_1 @ X10))
% 2.65/2.87          | ~ (v1_funct_1 @ X10)
% 2.65/2.87          | ~ (v1_relat_1 @ X10))),
% 2.65/2.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.65/2.87  thf('1', plain,
% 2.65/2.87      (![X9 : $i, X10 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 2.65/2.87          | (r2_hidden @ (sk_D @ X9 @ X10) @ (k1_relat_1 @ X10))
% 2.65/2.87          | ((X9) = (k2_relat_1 @ X10))
% 2.65/2.87          | ~ (v1_funct_1 @ X10)
% 2.65/2.87          | ~ (v1_relat_1 @ X10))),
% 2.65/2.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.65/2.87  thf('2', plain,
% 2.65/2.87      (![X10 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 2.65/2.87         (((X12) != (k2_relat_1 @ X10))
% 2.65/2.87          | (r2_hidden @ X14 @ X12)
% 2.65/2.87          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X10))
% 2.65/2.87          | ((X14) != (k1_funct_1 @ X10 @ X15))
% 2.65/2.87          | ~ (v1_funct_1 @ X10)
% 2.65/2.87          | ~ (v1_relat_1 @ X10))),
% 2.65/2.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.65/2.87  thf('3', plain,
% 2.65/2.87      (![X10 : $i, X15 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X10)
% 2.65/2.87          | ~ (v1_funct_1 @ X10)
% 2.65/2.87          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X10))
% 2.65/2.87          | (r2_hidden @ (k1_funct_1 @ X10 @ X15) @ (k2_relat_1 @ X10)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['2'])).
% 2.65/2.87  thf('4', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X0)
% 2.65/2.87          | ~ (v1_funct_1 @ X0)
% 2.65/2.87          | ((X1) = (k2_relat_1 @ X0))
% 2.65/2.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 2.65/2.87          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 2.65/2.87             (k2_relat_1 @ X0))
% 2.65/2.87          | ~ (v1_funct_1 @ X0)
% 2.65/2.87          | ~ (v1_relat_1 @ X0))),
% 2.65/2.87      inference('sup-', [status(thm)], ['1', '3'])).
% 2.65/2.87  thf('5', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 2.65/2.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 2.65/2.87          | ((X1) = (k2_relat_1 @ X0))
% 2.65/2.87          | ~ (v1_funct_1 @ X0)
% 2.65/2.87          | ~ (v1_relat_1 @ X0))),
% 2.65/2.87      inference('simplify', [status(thm)], ['4'])).
% 2.65/2.87  thf('6', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 2.65/2.87          | ~ (v1_relat_1 @ X0)
% 2.65/2.87          | ~ (v1_funct_1 @ X0)
% 2.65/2.87          | ((X1) = (k2_relat_1 @ X0))
% 2.65/2.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 2.65/2.87          | ~ (v1_relat_1 @ X0)
% 2.65/2.87          | ~ (v1_funct_1 @ X0)
% 2.65/2.87          | ((X1) = (k2_relat_1 @ X0))
% 2.65/2.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 2.65/2.87      inference('sup+', [status(thm)], ['0', '5'])).
% 2.65/2.87  thf('7', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 2.65/2.87          | ((X1) = (k2_relat_1 @ X0))
% 2.65/2.87          | ~ (v1_funct_1 @ X0)
% 2.65/2.87          | ~ (v1_relat_1 @ X0)
% 2.65/2.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['6'])).
% 2.65/2.87  thf(t16_funct_2, conjecture,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.65/2.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.65/2.87       ( ( ![D:$i]:
% 2.65/2.87           ( ~( ( r2_hidden @ D @ B ) & 
% 2.65/2.87                ( ![E:$i]:
% 2.65/2.87                  ( ~( ( r2_hidden @ E @ A ) & 
% 2.65/2.87                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 2.65/2.87         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 2.65/2.87  thf(zf_stmt_0, negated_conjecture,
% 2.65/2.87    (~( ![A:$i,B:$i,C:$i]:
% 2.65/2.87        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.65/2.87            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.65/2.87          ( ( ![D:$i]:
% 2.65/2.87              ( ~( ( r2_hidden @ D @ B ) & 
% 2.65/2.87                   ( ![E:$i]:
% 2.65/2.87                     ( ~( ( r2_hidden @ E @ A ) & 
% 2.65/2.87                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 2.65/2.87            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 2.65/2.87    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 2.65/2.87  thf('8', plain,
% 2.65/2.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf(cc2_relset_1, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.65/2.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.65/2.87  thf('9', plain,
% 2.65/2.87      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.65/2.87         ((v5_relat_1 @ X19 @ X21)
% 2.65/2.87          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.65/2.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.65/2.87  thf('10', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 2.65/2.87      inference('sup-', [status(thm)], ['8', '9'])).
% 2.65/2.87  thf(d19_relat_1, axiom,
% 2.65/2.87    (![A:$i,B:$i]:
% 2.65/2.87     ( ( v1_relat_1 @ B ) =>
% 2.65/2.87       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.65/2.87  thf('11', plain,
% 2.65/2.87      (![X7 : $i, X8 : $i]:
% 2.65/2.87         (~ (v5_relat_1 @ X7 @ X8)
% 2.65/2.87          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 2.65/2.87          | ~ (v1_relat_1 @ X7))),
% 2.65/2.87      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.65/2.87  thf('12', plain,
% 2.65/2.87      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 2.65/2.87      inference('sup-', [status(thm)], ['10', '11'])).
% 2.65/2.87  thf('13', plain,
% 2.65/2.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf(cc1_relset_1, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.65/2.87       ( v1_relat_1 @ C ) ))).
% 2.65/2.87  thf('14', plain,
% 2.65/2.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.65/2.87         ((v1_relat_1 @ X16)
% 2.65/2.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.65/2.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.65/2.87  thf('15', plain, ((v1_relat_1 @ sk_C_2)),
% 2.65/2.87      inference('sup-', [status(thm)], ['13', '14'])).
% 2.65/2.87  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 2.65/2.87      inference('demod', [status(thm)], ['12', '15'])).
% 2.65/2.87  thf(d3_tarski, axiom,
% 2.65/2.87    (![A:$i,B:$i]:
% 2.65/2.87     ( ( r1_tarski @ A @ B ) <=>
% 2.65/2.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.65/2.87  thf('17', plain,
% 2.65/2.87      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.65/2.87         (~ (r2_hidden @ X3 @ X4)
% 2.65/2.87          | (r2_hidden @ X3 @ X5)
% 2.65/2.87          | ~ (r1_tarski @ X4 @ X5))),
% 2.65/2.87      inference('cnf', [status(esa)], [d3_tarski])).
% 2.65/2.87  thf('18', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         ((r2_hidden @ X0 @ sk_B_1)
% 2.65/2.87          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['16', '17'])).
% 2.65/2.87  thf('19', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ sk_C_2)
% 2.65/2.87          | ~ (v1_funct_1 @ sk_C_2)
% 2.65/2.87          | ((X0) = (k2_relat_1 @ sk_C_2))
% 2.65/2.87          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 2.65/2.87          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B_1))),
% 2.65/2.87      inference('sup-', [status(thm)], ['7', '18'])).
% 2.65/2.87  thf('20', plain, ((v1_relat_1 @ sk_C_2)),
% 2.65/2.87      inference('sup-', [status(thm)], ['13', '14'])).
% 2.65/2.87  thf('21', plain, ((v1_funct_1 @ sk_C_2)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('22', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (((X0) = (k2_relat_1 @ sk_C_2))
% 2.65/2.87          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 2.65/2.87          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B_1))),
% 2.65/2.87      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.65/2.87  thf('23', plain,
% 2.65/2.87      (((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_B_1)
% 2.65/2.87        | ((sk_B_1) = (k2_relat_1 @ sk_C_2)))),
% 2.65/2.87      inference('eq_fact', [status(thm)], ['22'])).
% 2.65/2.87  thf('24', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) != (sk_B_1))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('25', plain,
% 2.65/2.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf(redefinition_k2_relset_1, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.65/2.87       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.65/2.87  thf('26', plain,
% 2.65/2.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.65/2.87         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 2.65/2.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 2.65/2.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.65/2.87  thf('27', plain,
% 2.65/2.87      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 2.65/2.87      inference('sup-', [status(thm)], ['25', '26'])).
% 2.65/2.87  thf('28', plain, (((k2_relat_1 @ sk_C_2) != (sk_B_1))),
% 2.65/2.87      inference('demod', [status(thm)], ['24', '27'])).
% 2.65/2.87  thf('29', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_B_1)),
% 2.65/2.87      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 2.65/2.87  thf(d1_xboole_0, axiom,
% 2.65/2.87    (![A:$i]:
% 2.65/2.87     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.65/2.87  thf('30', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.65/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.65/2.87  thf('31', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.65/2.87      inference('sup-', [status(thm)], ['29', '30'])).
% 2.65/2.87  thf(d1_funct_2, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.65/2.87       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.65/2.87           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.65/2.87             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.65/2.87         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.65/2.87           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.65/2.87             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.65/2.87  thf(zf_stmt_1, axiom,
% 2.65/2.87    (![B:$i,A:$i]:
% 2.65/2.87     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.65/2.87       ( zip_tseitin_0 @ B @ A ) ))).
% 2.65/2.87  thf('32', plain,
% 2.65/2.87      (![X28 : $i, X29 : $i]:
% 2.65/2.87         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.65/2.87  thf('33', plain,
% 2.65/2.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.65/2.87  thf(zf_stmt_3, axiom,
% 2.65/2.87    (![C:$i,B:$i,A:$i]:
% 2.65/2.87     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.65/2.87       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.65/2.87  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.65/2.87  thf(zf_stmt_5, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.65/2.87       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.65/2.87         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.65/2.87           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.65/2.87             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.65/2.87  thf('34', plain,
% 2.65/2.87      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.65/2.87         (~ (zip_tseitin_0 @ X33 @ X34)
% 2.65/2.87          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 2.65/2.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.65/2.87  thf('35', plain,
% 2.65/2.87      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.65/2.87        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.65/2.87      inference('sup-', [status(thm)], ['33', '34'])).
% 2.65/2.87  thf('36', plain,
% 2.65/2.87      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 2.65/2.87      inference('sup-', [status(thm)], ['32', '35'])).
% 2.65/2.87  thf('37', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('38', plain,
% 2.65/2.87      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.65/2.87         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 2.65/2.87          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 2.65/2.87          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.65/2.87  thf('39', plain,
% 2.65/2.87      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.65/2.87        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['37', '38'])).
% 2.65/2.87  thf('40', plain,
% 2.65/2.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf(redefinition_k1_relset_1, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.65/2.87       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.65/2.87  thf('41', plain,
% 2.65/2.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.65/2.87         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 2.65/2.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.65/2.87      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.65/2.87  thf('42', plain,
% 2.65/2.87      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 2.65/2.87      inference('sup-', [status(thm)], ['40', '41'])).
% 2.65/2.87  thf('43', plain,
% 2.65/2.87      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.65/2.87        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.65/2.87      inference('demod', [status(thm)], ['39', '42'])).
% 2.65/2.87  thf('44', plain,
% 2.65/2.87      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['36', '43'])).
% 2.65/2.87  thf('45', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_B_1)),
% 2.65/2.87      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 2.65/2.87  thf('46', plain,
% 2.65/2.87      (![X36 : $i]:
% 2.65/2.87         (~ (r2_hidden @ X36 @ sk_B_1)
% 2.65/2.87          | ((X36) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X36))))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('47', plain,
% 2.65/2.87      (((sk_C_1 @ sk_B_1 @ sk_C_2)
% 2.65/2.87         = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_B_1 @ sk_C_2))))),
% 2.65/2.87      inference('sup-', [status(thm)], ['45', '46'])).
% 2.65/2.87  thf('48', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_B_1)),
% 2.65/2.87      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 2.65/2.87  thf('49', plain,
% 2.65/2.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.65/2.87         (~ (r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 2.65/2.87          | ((sk_C_1 @ X9 @ X10) != (k1_funct_1 @ X10 @ X11))
% 2.65/2.87          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X10))
% 2.65/2.87          | ((X9) = (k2_relat_1 @ X10))
% 2.65/2.87          | ~ (v1_funct_1 @ X10)
% 2.65/2.87          | ~ (v1_relat_1 @ X10))),
% 2.65/2.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.65/2.87  thf('50', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ sk_C_2)
% 2.65/2.87          | ~ (v1_funct_1 @ sk_C_2)
% 2.65/2.87          | ((sk_B_1) = (k2_relat_1 @ sk_C_2))
% 2.65/2.87          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 2.65/2.87          | ((sk_C_1 @ sk_B_1 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['48', '49'])).
% 2.65/2.87  thf('51', plain, ((v1_relat_1 @ sk_C_2)),
% 2.65/2.87      inference('sup-', [status(thm)], ['13', '14'])).
% 2.65/2.87  thf('52', plain, ((v1_funct_1 @ sk_C_2)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('53', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (((sk_B_1) = (k2_relat_1 @ sk_C_2))
% 2.65/2.87          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 2.65/2.87          | ((sk_C_1 @ sk_B_1 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 2.65/2.87      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.65/2.87  thf('54', plain, (((k2_relat_1 @ sk_C_2) != (sk_B_1))),
% 2.65/2.87      inference('demod', [status(thm)], ['24', '27'])).
% 2.65/2.87  thf('55', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 2.65/2.87          | ((sk_C_1 @ sk_B_1 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 2.65/2.87      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 2.65/2.87  thf('56', plain,
% 2.65/2.87      ((((sk_C_1 @ sk_B_1 @ sk_C_2) != (sk_C_1 @ sk_B_1 @ sk_C_2))
% 2.65/2.87        | ~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B_1 @ sk_C_2)) @ 
% 2.65/2.87             (k1_relat_1 @ sk_C_2)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['47', '55'])).
% 2.65/2.87  thf('57', plain,
% 2.65/2.87      (~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B_1 @ sk_C_2)) @ 
% 2.65/2.87          (k1_relat_1 @ sk_C_2))),
% 2.65/2.87      inference('simplify', [status(thm)], ['56'])).
% 2.65/2.87  thf('58', plain,
% 2.65/2.87      ((~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B_1 @ sk_C_2)) @ sk_A)
% 2.65/2.87        | ((sk_B_1) = (k1_xboole_0)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['44', '57'])).
% 2.65/2.87  thf('59', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_B_1)),
% 2.65/2.87      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 2.65/2.87  thf('60', plain,
% 2.65/2.87      (![X36 : $i]:
% 2.65/2.87         (~ (r2_hidden @ X36 @ sk_B_1) | (r2_hidden @ (sk_E @ X36) @ sk_A))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('61', plain, ((r2_hidden @ (sk_E @ (sk_C_1 @ sk_B_1 @ sk_C_2)) @ sk_A)),
% 2.65/2.87      inference('sup-', [status(thm)], ['59', '60'])).
% 2.65/2.87  thf('62', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.65/2.87      inference('demod', [status(thm)], ['58', '61'])).
% 2.65/2.87  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.65/2.87  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.65/2.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.65/2.87  thf('64', plain, ($false),
% 2.65/2.87      inference('demod', [status(thm)], ['31', '62', '63'])).
% 2.65/2.87  
% 2.65/2.87  % SZS output end Refutation
% 2.65/2.87  
% 2.65/2.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
