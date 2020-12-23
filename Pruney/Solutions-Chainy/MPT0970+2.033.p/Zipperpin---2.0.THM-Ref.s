%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5qlDMPUsdb

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:21 EST 2020

% Result     : Theorem 4.48s
% Output     : Refutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 305 expanded)
%              Number of leaves         :   39 ( 105 expanded)
%              Depth                    :   16
%              Number of atoms          :  967 (4291 expanded)
%              Number of equality atoms :   70 ( 289 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X6 )
      | ( ( sk_C_1 @ X6 @ X7 )
        = ( k1_funct_1 @ X7 @ ( sk_D @ X6 @ X7 ) ) )
      | ( X6
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X6 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( X6
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X7 ) )
      | ( X11
       != ( k1_funct_1 @ X7 @ X12 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X7: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X12 ) @ ( k2_relat_1 @ X7 ) ) ) ),
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

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X18 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('26',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B )
      | ( X35
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_C_1 @ sk_B @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['23','26'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X6 )
      | ( ( sk_C_1 @ X6 @ X7 )
       != ( k1_funct_1 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ( X6
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
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

thf('36',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('42',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('43',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X0 = X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
      | ( sk_B = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('50',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
      | ( sk_B = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
      | ( sk_B = X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('60',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['37','60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','64'])).

thf('66',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_C_2 )
     != ( sk_C_1 @ sk_B @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','67'])).

thf('69',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['23','26'])).

thf('70',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X35 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ( sk_C_1 @ sk_B @ sk_C_2 )
 != ( sk_C_1 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5qlDMPUsdb
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.48/4.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.48/4.69  % Solved by: fo/fo7.sh
% 4.48/4.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.48/4.69  % done 2440 iterations in 4.239s
% 4.48/4.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.48/4.69  % SZS output start Refutation
% 4.48/4.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.48/4.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.48/4.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.48/4.69  thf(sk_E_type, type, sk_E: $i > $i).
% 4.48/4.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.48/4.69  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 4.48/4.69  thf(sk_A_type, type, sk_A: $i).
% 4.48/4.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.48/4.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.48/4.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.48/4.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.48/4.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.48/4.69  thf(sk_B_type, type, sk_B: $i).
% 4.48/4.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.48/4.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.48/4.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.48/4.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.48/4.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.48/4.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.48/4.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.48/4.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.48/4.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.48/4.69  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.48/4.69  thf(d5_funct_1, axiom,
% 4.48/4.69    (![A:$i]:
% 4.48/4.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.48/4.69       ( ![B:$i]:
% 4.48/4.69         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 4.48/4.69           ( ![C:$i]:
% 4.48/4.69             ( ( r2_hidden @ C @ B ) <=>
% 4.48/4.69               ( ?[D:$i]:
% 4.48/4.69                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 4.48/4.69                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 4.48/4.69  thf('0', plain,
% 4.48/4.69      (![X6 : $i, X7 : $i]:
% 4.48/4.69         ((r2_hidden @ (sk_C_1 @ X6 @ X7) @ X6)
% 4.48/4.69          | ((sk_C_1 @ X6 @ X7) = (k1_funct_1 @ X7 @ (sk_D @ X6 @ X7)))
% 4.48/4.69          | ((X6) = (k2_relat_1 @ X7))
% 4.48/4.69          | ~ (v1_funct_1 @ X7)
% 4.48/4.69          | ~ (v1_relat_1 @ X7))),
% 4.48/4.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.48/4.69  thf('1', plain,
% 4.48/4.69      (![X6 : $i, X7 : $i]:
% 4.48/4.69         ((r2_hidden @ (sk_C_1 @ X6 @ X7) @ X6)
% 4.48/4.69          | (r2_hidden @ (sk_D @ X6 @ X7) @ (k1_relat_1 @ X7))
% 4.48/4.69          | ((X6) = (k2_relat_1 @ X7))
% 4.48/4.69          | ~ (v1_funct_1 @ X7)
% 4.48/4.69          | ~ (v1_relat_1 @ X7))),
% 4.48/4.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.48/4.69  thf('2', plain,
% 4.48/4.69      (![X7 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 4.48/4.69         (((X9) != (k2_relat_1 @ X7))
% 4.48/4.69          | (r2_hidden @ X11 @ X9)
% 4.48/4.69          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X7))
% 4.48/4.69          | ((X11) != (k1_funct_1 @ X7 @ X12))
% 4.48/4.69          | ~ (v1_funct_1 @ X7)
% 4.48/4.69          | ~ (v1_relat_1 @ X7))),
% 4.48/4.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.48/4.69  thf('3', plain,
% 4.48/4.69      (![X7 : $i, X12 : $i]:
% 4.48/4.69         (~ (v1_relat_1 @ X7)
% 4.48/4.69          | ~ (v1_funct_1 @ X7)
% 4.48/4.69          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X7))
% 4.48/4.69          | (r2_hidden @ (k1_funct_1 @ X7 @ X12) @ (k2_relat_1 @ X7)))),
% 4.48/4.69      inference('simplify', [status(thm)], ['2'])).
% 4.48/4.69  thf('4', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         (~ (v1_relat_1 @ X0)
% 4.48/4.69          | ~ (v1_funct_1 @ X0)
% 4.48/4.69          | ((X1) = (k2_relat_1 @ X0))
% 4.48/4.69          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 4.48/4.69          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 4.48/4.69             (k2_relat_1 @ X0))
% 4.48/4.69          | ~ (v1_funct_1 @ X0)
% 4.48/4.69          | ~ (v1_relat_1 @ X0))),
% 4.48/4.69      inference('sup-', [status(thm)], ['1', '3'])).
% 4.48/4.69  thf('5', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 4.48/4.69          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 4.48/4.69          | ((X1) = (k2_relat_1 @ X0))
% 4.48/4.69          | ~ (v1_funct_1 @ X0)
% 4.48/4.69          | ~ (v1_relat_1 @ X0))),
% 4.48/4.69      inference('simplify', [status(thm)], ['4'])).
% 4.48/4.69  thf('6', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 4.48/4.69          | ~ (v1_relat_1 @ X0)
% 4.48/4.69          | ~ (v1_funct_1 @ X0)
% 4.48/4.69          | ((X1) = (k2_relat_1 @ X0))
% 4.48/4.69          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 4.48/4.69          | ~ (v1_relat_1 @ X0)
% 4.48/4.69          | ~ (v1_funct_1 @ X0)
% 4.48/4.69          | ((X1) = (k2_relat_1 @ X0))
% 4.48/4.69          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 4.48/4.69      inference('sup+', [status(thm)], ['0', '5'])).
% 4.48/4.69  thf('7', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 4.48/4.69          | ((X1) = (k2_relat_1 @ X0))
% 4.48/4.69          | ~ (v1_funct_1 @ X0)
% 4.48/4.69          | ~ (v1_relat_1 @ X0)
% 4.48/4.69          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 4.48/4.69      inference('simplify', [status(thm)], ['6'])).
% 4.48/4.69  thf(t16_funct_2, conjecture,
% 4.48/4.69    (![A:$i,B:$i,C:$i]:
% 4.48/4.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.48/4.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.48/4.69       ( ( ![D:$i]:
% 4.48/4.69           ( ~( ( r2_hidden @ D @ B ) & 
% 4.48/4.69                ( ![E:$i]:
% 4.48/4.69                  ( ~( ( r2_hidden @ E @ A ) & 
% 4.48/4.69                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 4.48/4.69         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 4.48/4.69  thf(zf_stmt_0, negated_conjecture,
% 4.48/4.69    (~( ![A:$i,B:$i,C:$i]:
% 4.48/4.69        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.48/4.69            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.48/4.69          ( ( ![D:$i]:
% 4.48/4.69              ( ~( ( r2_hidden @ D @ B ) & 
% 4.48/4.69                   ( ![E:$i]:
% 4.48/4.69                     ( ~( ( r2_hidden @ E @ A ) & 
% 4.48/4.69                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 4.48/4.69            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 4.48/4.69    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 4.48/4.69  thf('8', plain,
% 4.48/4.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf(dt_k2_relset_1, axiom,
% 4.48/4.69    (![A:$i,B:$i,C:$i]:
% 4.48/4.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.48/4.69       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 4.48/4.69  thf('9', plain,
% 4.48/4.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.48/4.69         ((m1_subset_1 @ (k2_relset_1 @ X18 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 4.48/4.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.48/4.69      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 4.48/4.69  thf('10', plain,
% 4.48/4.69      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 4.48/4.69        (k1_zfmisc_1 @ sk_B))),
% 4.48/4.69      inference('sup-', [status(thm)], ['8', '9'])).
% 4.48/4.69  thf('11', plain,
% 4.48/4.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf(redefinition_k2_relset_1, axiom,
% 4.48/4.69    (![A:$i,B:$i,C:$i]:
% 4.48/4.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.48/4.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.48/4.69  thf('12', plain,
% 4.48/4.69      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.48/4.69         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 4.48/4.69          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.48/4.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.48/4.69  thf('13', plain,
% 4.48/4.69      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 4.48/4.69      inference('sup-', [status(thm)], ['11', '12'])).
% 4.48/4.69  thf('14', plain,
% 4.48/4.69      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 4.48/4.69      inference('demod', [status(thm)], ['10', '13'])).
% 4.48/4.69  thf(l3_subset_1, axiom,
% 4.48/4.69    (![A:$i,B:$i]:
% 4.48/4.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.48/4.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 4.48/4.69  thf('15', plain,
% 4.48/4.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 4.48/4.69         (~ (r2_hidden @ X3 @ X4)
% 4.48/4.69          | (r2_hidden @ X3 @ X5)
% 4.48/4.69          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 4.48/4.69      inference('cnf', [status(esa)], [l3_subset_1])).
% 4.48/4.69  thf('16', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['14', '15'])).
% 4.48/4.69  thf('17', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (~ (v1_relat_1 @ sk_C_2)
% 4.48/4.69          | ~ (v1_funct_1 @ sk_C_2)
% 4.48/4.69          | ((X0) = (k2_relat_1 @ sk_C_2))
% 4.48/4.69          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 4.48/4.69          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 4.48/4.69      inference('sup-', [status(thm)], ['7', '16'])).
% 4.48/4.69  thf('18', plain,
% 4.48/4.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf(cc1_relset_1, axiom,
% 4.48/4.69    (![A:$i,B:$i,C:$i]:
% 4.48/4.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.48/4.69       ( v1_relat_1 @ C ) ))).
% 4.48/4.69  thf('19', plain,
% 4.48/4.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.48/4.69         ((v1_relat_1 @ X15)
% 4.48/4.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 4.48/4.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.48/4.69  thf('20', plain, ((v1_relat_1 @ sk_C_2)),
% 4.48/4.69      inference('sup-', [status(thm)], ['18', '19'])).
% 4.48/4.69  thf('21', plain, ((v1_funct_1 @ sk_C_2)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('22', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (((X0) = (k2_relat_1 @ sk_C_2))
% 4.48/4.69          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 4.48/4.69          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 4.48/4.69      inference('demod', [status(thm)], ['17', '20', '21'])).
% 4.48/4.69  thf('23', plain,
% 4.48/4.69      (((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 4.48/4.69        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 4.48/4.69      inference('eq_fact', [status(thm)], ['22'])).
% 4.48/4.69  thf('24', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('25', plain,
% 4.48/4.69      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 4.48/4.69      inference('sup-', [status(thm)], ['11', '12'])).
% 4.48/4.69  thf('26', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 4.48/4.69      inference('demod', [status(thm)], ['24', '25'])).
% 4.48/4.69  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 4.48/4.69      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 4.48/4.69  thf('28', plain,
% 4.48/4.69      (![X35 : $i]:
% 4.48/4.69         (~ (r2_hidden @ X35 @ sk_B)
% 4.48/4.69          | ((X35) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X35))))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('29', plain,
% 4.48/4.69      (((sk_C_1 @ sk_B @ sk_C_2)
% 4.48/4.69         = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['27', '28'])).
% 4.48/4.69  thf('30', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 4.48/4.69      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 4.48/4.69  thf('31', plain,
% 4.48/4.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.48/4.69         (~ (r2_hidden @ (sk_C_1 @ X6 @ X7) @ X6)
% 4.48/4.69          | ((sk_C_1 @ X6 @ X7) != (k1_funct_1 @ X7 @ X8))
% 4.48/4.69          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 4.48/4.69          | ((X6) = (k2_relat_1 @ X7))
% 4.48/4.69          | ~ (v1_funct_1 @ X7)
% 4.48/4.69          | ~ (v1_relat_1 @ X7))),
% 4.48/4.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.48/4.69  thf('32', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (~ (v1_relat_1 @ sk_C_2)
% 4.48/4.69          | ~ (v1_funct_1 @ sk_C_2)
% 4.48/4.69          | ((sk_B) = (k2_relat_1 @ sk_C_2))
% 4.48/4.69          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 4.48/4.69          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['30', '31'])).
% 4.48/4.69  thf('33', plain, ((v1_relat_1 @ sk_C_2)),
% 4.48/4.69      inference('sup-', [status(thm)], ['18', '19'])).
% 4.48/4.69  thf('34', plain, ((v1_funct_1 @ sk_C_2)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('35', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf(d1_funct_2, axiom,
% 4.48/4.69    (![A:$i,B:$i,C:$i]:
% 4.48/4.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.48/4.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.48/4.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.48/4.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.48/4.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.48/4.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.48/4.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.48/4.69  thf(zf_stmt_1, axiom,
% 4.48/4.69    (![C:$i,B:$i,A:$i]:
% 4.48/4.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.48/4.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.48/4.69  thf('36', plain,
% 4.48/4.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.48/4.69         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 4.48/4.69          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 4.48/4.69          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.48/4.69  thf('37', plain,
% 4.48/4.69      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 4.48/4.69        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['35', '36'])).
% 4.48/4.69  thf(zf_stmt_2, axiom,
% 4.48/4.69    (![B:$i,A:$i]:
% 4.48/4.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.48/4.69       ( zip_tseitin_0 @ B @ A ) ))).
% 4.48/4.69  thf('38', plain,
% 4.48/4.69      (![X27 : $i, X28 : $i]:
% 4.48/4.69         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.48/4.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.48/4.69  thf('39', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 4.48/4.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.48/4.69  thf('40', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.69         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 4.48/4.69      inference('sup+', [status(thm)], ['38', '39'])).
% 4.48/4.69  thf('41', plain,
% 4.48/4.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.48/4.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.48/4.69  thf(zf_stmt_5, axiom,
% 4.48/4.69    (![A:$i,B:$i,C:$i]:
% 4.48/4.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.48/4.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.48/4.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.48/4.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.48/4.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.48/4.69  thf('42', plain,
% 4.48/4.69      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.48/4.69         (~ (zip_tseitin_0 @ X32 @ X33)
% 4.48/4.69          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 4.48/4.69          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.48/4.69  thf('43', plain,
% 4.48/4.69      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 4.48/4.69        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.48/4.69      inference('sup-', [status(thm)], ['41', '42'])).
% 4.48/4.69  thf('44', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 4.48/4.69      inference('sup-', [status(thm)], ['40', '43'])).
% 4.48/4.69  thf(t2_tarski, axiom,
% 4.48/4.69    (![A:$i,B:$i]:
% 4.48/4.69     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 4.48/4.69       ( ( A ) = ( B ) ) ))).
% 4.48/4.69  thf('45', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         (((X1) = (X0))
% 4.48/4.69          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 4.48/4.69          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 4.48/4.69      inference('cnf', [status(esa)], [t2_tarski])).
% 4.48/4.69  thf(t7_ordinal1, axiom,
% 4.48/4.69    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.48/4.69  thf('46', plain,
% 4.48/4.69      (![X13 : $i, X14 : $i]:
% 4.48/4.69         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 4.48/4.69      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.48/4.69  thf('47', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 4.48/4.69          | ((X0) = (X1))
% 4.48/4.69          | ~ (r1_tarski @ X0 @ (sk_C @ X1 @ X0)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['45', '46'])).
% 4.48/4.69  thf('48', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 4.48/4.69          | ((sk_B) = (X0))
% 4.48/4.69          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ X0))),
% 4.48/4.69      inference('sup-', [status(thm)], ['44', '47'])).
% 4.48/4.69  thf('49', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['14', '15'])).
% 4.48/4.69  thf('50', plain,
% 4.48/4.69      ((((sk_B) = (k2_relat_1 @ sk_C_2))
% 4.48/4.69        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 4.48/4.69        | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B))),
% 4.48/4.69      inference('sup-', [status(thm)], ['48', '49'])).
% 4.48/4.69  thf('51', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 4.48/4.69      inference('demod', [status(thm)], ['24', '25'])).
% 4.48/4.69  thf('52', plain,
% 4.48/4.69      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 4.48/4.69        | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B))),
% 4.48/4.69      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 4.48/4.69  thf('53', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 4.48/4.69          | ((sk_B) = (X0))
% 4.48/4.69          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ X0))),
% 4.48/4.69      inference('sup-', [status(thm)], ['44', '47'])).
% 4.48/4.69  thf('54', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         (((X1) = (X0))
% 4.48/4.69          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 4.48/4.69          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 4.48/4.69      inference('cnf', [status(esa)], [t2_tarski])).
% 4.48/4.69  thf('55', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (((sk_B) = (X0))
% 4.48/4.69          | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 4.48/4.69          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)
% 4.48/4.69          | ((sk_B) = (X0)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['53', '54'])).
% 4.48/4.69  thf('56', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)
% 4.48/4.69          | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 4.48/4.69          | ((sk_B) = (X0)))),
% 4.48/4.69      inference('simplify', [status(thm)], ['55'])).
% 4.48/4.69  thf('57', plain,
% 4.48/4.69      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 4.48/4.69        | ((sk_B) = (k2_relat_1 @ sk_C_2))
% 4.48/4.69        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 4.48/4.69      inference('sup-', [status(thm)], ['52', '56'])).
% 4.48/4.69  thf('58', plain,
% 4.48/4.69      ((((sk_B) = (k2_relat_1 @ sk_C_2))
% 4.48/4.69        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 4.48/4.69      inference('simplify', [status(thm)], ['57'])).
% 4.48/4.69  thf('59', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 4.48/4.69      inference('demod', [status(thm)], ['24', '25'])).
% 4.48/4.69  thf('60', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 4.48/4.69      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 4.48/4.69  thf('61', plain,
% 4.48/4.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf(redefinition_k1_relset_1, axiom,
% 4.48/4.69    (![A:$i,B:$i,C:$i]:
% 4.48/4.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.48/4.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.48/4.69  thf('62', plain,
% 4.48/4.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.48/4.69         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 4.48/4.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.48/4.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.48/4.69  thf('63', plain,
% 4.48/4.69      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 4.48/4.69      inference('sup-', [status(thm)], ['61', '62'])).
% 4.48/4.69  thf('64', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 4.48/4.69      inference('demod', [status(thm)], ['37', '60', '63'])).
% 4.48/4.69  thf('65', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (((sk_B) = (k2_relat_1 @ sk_C_2))
% 4.48/4.69          | ~ (r2_hidden @ X0 @ sk_A)
% 4.48/4.69          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 4.48/4.69      inference('demod', [status(thm)], ['32', '33', '34', '64'])).
% 4.48/4.69  thf('66', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 4.48/4.69      inference('demod', [status(thm)], ['24', '25'])).
% 4.48/4.69  thf('67', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (~ (r2_hidden @ X0 @ sk_A)
% 4.48/4.69          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 4.48/4.69      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 4.48/4.69  thf('68', plain,
% 4.48/4.69      ((((sk_C_1 @ sk_B @ sk_C_2) != (sk_C_1 @ sk_B @ sk_C_2))
% 4.48/4.69        | ~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A))),
% 4.48/4.69      inference('sup-', [status(thm)], ['29', '67'])).
% 4.48/4.69  thf('69', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 4.48/4.69      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 4.48/4.69  thf('70', plain,
% 4.48/4.69      (![X35 : $i]:
% 4.48/4.69         (~ (r2_hidden @ X35 @ sk_B) | (r2_hidden @ (sk_E @ X35) @ sk_A))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('71', plain, ((r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A)),
% 4.48/4.69      inference('sup-', [status(thm)], ['69', '70'])).
% 4.48/4.69  thf('72', plain, (((sk_C_1 @ sk_B @ sk_C_2) != (sk_C_1 @ sk_B @ sk_C_2))),
% 4.48/4.69      inference('demod', [status(thm)], ['68', '71'])).
% 4.48/4.69  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 4.48/4.69  
% 4.48/4.69  % SZS output end Refutation
% 4.48/4.69  
% 4.48/4.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
