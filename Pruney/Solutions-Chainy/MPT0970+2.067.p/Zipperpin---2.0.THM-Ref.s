%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1ooDeOeKOB

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:26 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 340 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          : 1147 (4711 expanded)
%              Number of equality atoms :   85 ( 317 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( ( sk_C @ X8 @ X9 )
        = ( k1_funct_1 @ X9 @ ( sk_D @ X8 @ X9 ) ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( X13
       != ( k1_funct_1 @ X9 @ X14 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('28',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B )
      | ( X34
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C @ sk_B @ sk_C_1 )
    = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( ( sk_C @ X8 @ X9 )
       != ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( ( sk_C @ sk_B @ sk_C_1 )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
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

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('41',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('42',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('49',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( ( sk_C @ X8 @ X9 )
        = ( k1_funct_1 @ X9 @ ( sk_D @ X8 @ X9 ) ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ k1_xboole_0 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('70',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('73',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( r1_tarski @ sk_B @ ( sk_C @ k1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','73'])).

thf('75',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('76',plain,
    ( ( k1_xboole_0 != sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_C_1 )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','82'])).

thf('84',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_C_1 )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( sk_C @ sk_B @ sk_C_1 )
     != ( sk_C @ sk_B @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_C @ sk_B @ sk_C_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','85'])).

thf('87',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

thf('88',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X34 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    r2_hidden @ ( sk_E @ ( sk_C @ sk_B @ sk_C_1 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ( sk_C @ sk_B @ sk_C_1 )
 != ( sk_C @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1ooDeOeKOB
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.18/1.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.44  % Solved by: fo/fo7.sh
% 1.18/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.44  % done 1141 iterations in 0.988s
% 1.18/1.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.44  % SZS output start Refutation
% 1.18/1.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.18/1.44  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.18/1.44  thf(sk_E_type, type, sk_E: $i > $i).
% 1.18/1.44  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.18/1.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.18/1.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.18/1.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.18/1.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.18/1.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.44  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.18/1.44  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.18/1.44  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.18/1.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.18/1.44  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.44  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.18/1.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.18/1.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.18/1.44  thf(d5_funct_1, axiom,
% 1.18/1.44    (![A:$i]:
% 1.18/1.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.44       ( ![B:$i]:
% 1.18/1.44         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.18/1.44           ( ![C:$i]:
% 1.18/1.44             ( ( r2_hidden @ C @ B ) <=>
% 1.18/1.44               ( ?[D:$i]:
% 1.18/1.44                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.18/1.44                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.18/1.44  thf('0', plain,
% 1.18/1.44      (![X8 : $i, X9 : $i]:
% 1.18/1.44         ((r2_hidden @ (sk_C @ X8 @ X9) @ X8)
% 1.18/1.44          | ((sk_C @ X8 @ X9) = (k1_funct_1 @ X9 @ (sk_D @ X8 @ X9)))
% 1.18/1.44          | ((X8) = (k2_relat_1 @ X9))
% 1.18/1.44          | ~ (v1_funct_1 @ X9)
% 1.18/1.44          | ~ (v1_relat_1 @ X9))),
% 1.18/1.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.18/1.44  thf('1', plain,
% 1.18/1.44      (![X8 : $i, X9 : $i]:
% 1.18/1.44         ((r2_hidden @ (sk_C @ X8 @ X9) @ X8)
% 1.18/1.44          | (r2_hidden @ (sk_D @ X8 @ X9) @ (k1_relat_1 @ X9))
% 1.18/1.44          | ((X8) = (k2_relat_1 @ X9))
% 1.18/1.44          | ~ (v1_funct_1 @ X9)
% 1.18/1.44          | ~ (v1_relat_1 @ X9))),
% 1.18/1.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.18/1.44  thf('2', plain,
% 1.18/1.44      (![X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 1.18/1.44         (((X11) != (k2_relat_1 @ X9))
% 1.18/1.44          | (r2_hidden @ X13 @ X11)
% 1.18/1.44          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 1.18/1.44          | ((X13) != (k1_funct_1 @ X9 @ X14))
% 1.18/1.44          | ~ (v1_funct_1 @ X9)
% 1.18/1.44          | ~ (v1_relat_1 @ X9))),
% 1.18/1.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.18/1.44  thf('3', plain,
% 1.18/1.44      (![X9 : $i, X14 : $i]:
% 1.18/1.44         (~ (v1_relat_1 @ X9)
% 1.18/1.44          | ~ (v1_funct_1 @ X9)
% 1.18/1.44          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 1.18/1.44          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 1.18/1.44      inference('simplify', [status(thm)], ['2'])).
% 1.18/1.44  thf('4', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         (~ (v1_relat_1 @ X0)
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ((X1) = (k2_relat_1 @ X0))
% 1.18/1.44          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 1.18/1.44          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 1.18/1.44             (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ~ (v1_relat_1 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['1', '3'])).
% 1.18/1.44  thf('5', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 1.18/1.44          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 1.18/1.44          | ((X1) = (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ~ (v1_relat_1 @ X0))),
% 1.18/1.44      inference('simplify', [status(thm)], ['4'])).
% 1.18/1.44  thf('6', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_relat_1 @ X0)
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ((X1) = (k2_relat_1 @ X0))
% 1.18/1.44          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 1.18/1.44          | ~ (v1_relat_1 @ X0)
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ((X1) = (k2_relat_1 @ X0))
% 1.18/1.44          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.18/1.44      inference('sup+', [status(thm)], ['0', '5'])).
% 1.18/1.44  thf('7', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 1.18/1.44          | ((X1) = (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ~ (v1_relat_1 @ X0)
% 1.18/1.44          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.18/1.44      inference('simplify', [status(thm)], ['6'])).
% 1.18/1.44  thf(t16_funct_2, conjecture,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.18/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.44       ( ( ![D:$i]:
% 1.18/1.44           ( ~( ( r2_hidden @ D @ B ) & 
% 1.18/1.44                ( ![E:$i]:
% 1.18/1.44                  ( ~( ( r2_hidden @ E @ A ) & 
% 1.18/1.44                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.18/1.44         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 1.18/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.44    (~( ![A:$i,B:$i,C:$i]:
% 1.18/1.44        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.18/1.44            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.44          ( ( ![D:$i]:
% 1.18/1.44              ( ~( ( r2_hidden @ D @ B ) & 
% 1.18/1.44                   ( ![E:$i]:
% 1.18/1.44                     ( ~( ( r2_hidden @ E @ A ) & 
% 1.18/1.44                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.18/1.44            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 1.18/1.44    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 1.18/1.44  thf('8', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(dt_k2_relset_1, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.44       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.18/1.44  thf('9', plain,
% 1.18/1.44      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.18/1.44         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 1.18/1.44          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.18/1.44  thf('10', plain,
% 1.18/1.44      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 1.18/1.44        (k1_zfmisc_1 @ sk_B))),
% 1.18/1.44      inference('sup-', [status(thm)], ['8', '9'])).
% 1.18/1.44  thf('11', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(redefinition_k2_relset_1, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.44       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.18/1.44  thf('12', plain,
% 1.18/1.44      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.18/1.44         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 1.18/1.44          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.18/1.44      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.18/1.44  thf('13', plain,
% 1.18/1.44      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.18/1.44      inference('sup-', [status(thm)], ['11', '12'])).
% 1.18/1.44  thf('14', plain,
% 1.18/1.44      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 1.18/1.44      inference('demod', [status(thm)], ['10', '13'])).
% 1.18/1.44  thf(l3_subset_1, axiom,
% 1.18/1.44    (![A:$i,B:$i]:
% 1.18/1.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.18/1.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.18/1.44  thf('15', plain,
% 1.18/1.44      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.18/1.44         (~ (r2_hidden @ X1 @ X2)
% 1.18/1.44          | (r2_hidden @ X1 @ X3)
% 1.18/1.44          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 1.18/1.44      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.18/1.44  thf('16', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.44  thf('17', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (v1_relat_1 @ sk_C_1)
% 1.18/1.44          | ~ (v1_funct_1 @ sk_C_1)
% 1.18/1.44          | ((X0) = (k2_relat_1 @ sk_C_1))
% 1.18/1.44          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 1.18/1.44          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B))),
% 1.18/1.44      inference('sup-', [status(thm)], ['7', '16'])).
% 1.18/1.44  thf('18', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(cc2_relat_1, axiom,
% 1.18/1.44    (![A:$i]:
% 1.18/1.44     ( ( v1_relat_1 @ A ) =>
% 1.18/1.44       ( ![B:$i]:
% 1.18/1.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.18/1.44  thf('19', plain,
% 1.18/1.44      (![X4 : $i, X5 : $i]:
% 1.18/1.44         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.18/1.44          | (v1_relat_1 @ X4)
% 1.18/1.44          | ~ (v1_relat_1 @ X5))),
% 1.18/1.44      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.18/1.44  thf('20', plain,
% 1.18/1.44      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 1.18/1.44      inference('sup-', [status(thm)], ['18', '19'])).
% 1.18/1.44  thf(fc6_relat_1, axiom,
% 1.18/1.44    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.18/1.44  thf('21', plain,
% 1.18/1.44      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 1.18/1.44      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.18/1.44  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.44      inference('demod', [status(thm)], ['20', '21'])).
% 1.18/1.44  thf('23', plain, ((v1_funct_1 @ sk_C_1)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('24', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (((X0) = (k2_relat_1 @ sk_C_1))
% 1.18/1.44          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 1.18/1.44          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B))),
% 1.18/1.44      inference('demod', [status(thm)], ['17', '22', '23'])).
% 1.18/1.44  thf('25', plain,
% 1.18/1.44      (((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 1.18/1.44        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 1.18/1.44      inference('eq_fact', [status(thm)], ['24'])).
% 1.18/1.44  thf('26', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('27', plain,
% 1.18/1.44      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.18/1.44      inference('sup-', [status(thm)], ['11', '12'])).
% 1.18/1.44  thf('28', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 1.18/1.44      inference('demod', [status(thm)], ['26', '27'])).
% 1.18/1.44  thf('29', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 1.18/1.44      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 1.18/1.44  thf('30', plain,
% 1.18/1.44      (![X34 : $i]:
% 1.18/1.44         (~ (r2_hidden @ X34 @ sk_B)
% 1.18/1.44          | ((X34) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X34))))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('31', plain,
% 1.18/1.44      (((sk_C @ sk_B @ sk_C_1)
% 1.18/1.44         = (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ sk_B @ sk_C_1))))),
% 1.18/1.44      inference('sup-', [status(thm)], ['29', '30'])).
% 1.18/1.44  thf('32', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 1.18/1.44      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 1.18/1.44  thf('33', plain,
% 1.18/1.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.18/1.44         (~ (r2_hidden @ (sk_C @ X8 @ X9) @ X8)
% 1.18/1.44          | ((sk_C @ X8 @ X9) != (k1_funct_1 @ X9 @ X10))
% 1.18/1.44          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 1.18/1.44          | ((X8) = (k2_relat_1 @ X9))
% 1.18/1.44          | ~ (v1_funct_1 @ X9)
% 1.18/1.44          | ~ (v1_relat_1 @ X9))),
% 1.18/1.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.18/1.44  thf('34', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (v1_relat_1 @ sk_C_1)
% 1.18/1.44          | ~ (v1_funct_1 @ sk_C_1)
% 1.18/1.44          | ((sk_B) = (k2_relat_1 @ sk_C_1))
% 1.18/1.44          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 1.18/1.44          | ((sk_C @ sk_B @ sk_C_1) != (k1_funct_1 @ sk_C_1 @ X0)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['32', '33'])).
% 1.18/1.44  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.44      inference('demod', [status(thm)], ['20', '21'])).
% 1.18/1.44  thf('36', plain, ((v1_funct_1 @ sk_C_1)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(d1_funct_2, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.44       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.44           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.18/1.44             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.18/1.44         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.44           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.18/1.44             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.18/1.44  thf(zf_stmt_1, axiom,
% 1.18/1.44    (![B:$i,A:$i]:
% 1.18/1.44     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.44       ( zip_tseitin_0 @ B @ A ) ))).
% 1.18/1.44  thf('37', plain,
% 1.18/1.44      (![X26 : $i, X27 : $i]:
% 1.18/1.44         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.44  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.18/1.44  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.18/1.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.18/1.44  thf('39', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.44         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.18/1.44      inference('sup+', [status(thm)], ['37', '38'])).
% 1.18/1.44  thf('40', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.18/1.44  thf(zf_stmt_3, axiom,
% 1.18/1.44    (![C:$i,B:$i,A:$i]:
% 1.18/1.44     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.18/1.44       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.18/1.44  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.18/1.44  thf(zf_stmt_5, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.44       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.18/1.44         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.44           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.18/1.44             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.18/1.44  thf('41', plain,
% 1.18/1.44      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.18/1.44         (~ (zip_tseitin_0 @ X31 @ X32)
% 1.18/1.44          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 1.18/1.44          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.18/1.44  thf('42', plain,
% 1.18/1.44      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.18/1.44        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.18/1.44      inference('sup-', [status(thm)], ['40', '41'])).
% 1.18/1.44  thf('43', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.18/1.44      inference('sup-', [status(thm)], ['39', '42'])).
% 1.18/1.44  thf('44', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('45', plain,
% 1.18/1.44      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.18/1.44         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 1.18/1.44          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 1.18/1.44          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.18/1.44  thf('46', plain,
% 1.18/1.44      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.18/1.44        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['44', '45'])).
% 1.18/1.44  thf('47', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(redefinition_k1_relset_1, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.44       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.18/1.44  thf('48', plain,
% 1.18/1.44      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.44         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.18/1.44          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.18/1.44      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.18/1.44  thf('49', plain,
% 1.18/1.44      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.18/1.44      inference('sup-', [status(thm)], ['47', '48'])).
% 1.18/1.44  thf('50', plain,
% 1.18/1.44      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.18/1.44        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['46', '49'])).
% 1.18/1.44  thf('51', plain,
% 1.18/1.44      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['43', '50'])).
% 1.18/1.44  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.18/1.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.18/1.44  thf('53', plain,
% 1.18/1.44      (![X8 : $i, X9 : $i]:
% 1.18/1.44         ((r2_hidden @ (sk_C @ X8 @ X9) @ X8)
% 1.18/1.44          | ((sk_C @ X8 @ X9) = (k1_funct_1 @ X9 @ (sk_D @ X8 @ X9)))
% 1.18/1.44          | ((X8) = (k2_relat_1 @ X9))
% 1.18/1.44          | ~ (v1_funct_1 @ X9)
% 1.18/1.44          | ~ (v1_relat_1 @ X9))),
% 1.18/1.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.18/1.44  thf(t7_ordinal1, axiom,
% 1.18/1.44    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.18/1.44  thf('54', plain,
% 1.18/1.44      (![X15 : $i, X16 : $i]:
% 1.18/1.44         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.18/1.44  thf('55', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         (~ (v1_relat_1 @ X1)
% 1.18/1.44          | ~ (v1_funct_1 @ X1)
% 1.18/1.44          | ((X0) = (k2_relat_1 @ X1))
% 1.18/1.44          | ((sk_C @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_D @ X0 @ X1)))
% 1.18/1.44          | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['53', '54'])).
% 1.18/1.44  thf('56', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (((sk_C @ k1_xboole_0 @ X0)
% 1.18/1.44            = (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0)))
% 1.18/1.44          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ~ (v1_relat_1 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['52', '55'])).
% 1.18/1.44  thf('57', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.18/1.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.18/1.44  thf('58', plain,
% 1.18/1.44      (![X8 : $i, X9 : $i]:
% 1.18/1.44         ((r2_hidden @ (sk_C @ X8 @ X9) @ X8)
% 1.18/1.44          | (r2_hidden @ (sk_D @ X8 @ X9) @ (k1_relat_1 @ X9))
% 1.18/1.44          | ((X8) = (k2_relat_1 @ X9))
% 1.18/1.44          | ~ (v1_funct_1 @ X9)
% 1.18/1.44          | ~ (v1_relat_1 @ X9))),
% 1.18/1.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.18/1.44  thf('59', plain,
% 1.18/1.44      (![X15 : $i, X16 : $i]:
% 1.18/1.44         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.18/1.44  thf('60', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         (~ (v1_relat_1 @ X1)
% 1.18/1.44          | ~ (v1_funct_1 @ X1)
% 1.18/1.44          | ((X0) = (k2_relat_1 @ X1))
% 1.18/1.44          | (r2_hidden @ (sk_D @ X0 @ X1) @ (k1_relat_1 @ X1))
% 1.18/1.44          | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['58', '59'])).
% 1.18/1.44  thf('61', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0) @ (k1_relat_1 @ X0))
% 1.18/1.44          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ~ (v1_relat_1 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['57', '60'])).
% 1.18/1.44  thf('62', plain,
% 1.18/1.44      (![X9 : $i, X14 : $i]:
% 1.18/1.44         (~ (v1_relat_1 @ X9)
% 1.18/1.44          | ~ (v1_funct_1 @ X9)
% 1.18/1.44          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 1.18/1.44          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 1.18/1.44      inference('simplify', [status(thm)], ['2'])).
% 1.18/1.44  thf('63', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (v1_relat_1 @ X0)
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.18/1.44          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0)) @ 
% 1.18/1.44             (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ~ (v1_relat_1 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['61', '62'])).
% 1.18/1.44  thf('64', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0)) @ 
% 1.18/1.44           (k2_relat_1 @ X0))
% 1.18/1.44          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ~ (v1_relat_1 @ X0))),
% 1.18/1.44      inference('simplify', [status(thm)], ['63'])).
% 1.18/1.44  thf('65', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_relat_1 @ X0)
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_relat_1 @ X0)
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ((k1_xboole_0) = (k2_relat_1 @ X0)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['56', '64'])).
% 1.18/1.44  thf('66', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.18/1.44          | ~ (v1_funct_1 @ X0)
% 1.18/1.44          | ~ (v1_relat_1 @ X0)
% 1.18/1.44          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ (k2_relat_1 @ X0)))),
% 1.18/1.44      inference('simplify', [status(thm)], ['65'])).
% 1.18/1.44  thf('67', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.44  thf('68', plain,
% 1.18/1.44      ((~ (v1_relat_1 @ sk_C_1)
% 1.18/1.44        | ~ (v1_funct_1 @ sk_C_1)
% 1.18/1.44        | ((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 1.18/1.44        | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_C_1) @ sk_B))),
% 1.18/1.44      inference('sup-', [status(thm)], ['66', '67'])).
% 1.18/1.44  thf('69', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.44      inference('demod', [status(thm)], ['20', '21'])).
% 1.18/1.44  thf('70', plain, ((v1_funct_1 @ sk_C_1)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('71', plain,
% 1.18/1.44      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 1.18/1.44        | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_C_1) @ sk_B))),
% 1.18/1.44      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.18/1.44  thf('72', plain,
% 1.18/1.44      (![X15 : $i, X16 : $i]:
% 1.18/1.44         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.18/1.44  thf('73', plain,
% 1.18/1.44      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 1.18/1.44        | ~ (r1_tarski @ sk_B @ (sk_C @ k1_xboole_0 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['71', '72'])).
% 1.18/1.44  thf('74', plain,
% 1.18/1.44      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 1.18/1.44        | ((k1_xboole_0) = (k2_relat_1 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['51', '73'])).
% 1.18/1.44  thf('75', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 1.18/1.44      inference('demod', [status(thm)], ['26', '27'])).
% 1.18/1.44  thf('76', plain,
% 1.18/1.44      ((((k1_xboole_0) != (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['74', '75'])).
% 1.18/1.44  thf('77', plain,
% 1.18/1.44      (![X26 : $i, X27 : $i]:
% 1.18/1.44         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.44  thf('78', plain,
% 1.18/1.44      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.18/1.44        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.18/1.44      inference('sup-', [status(thm)], ['40', '41'])).
% 1.18/1.44  thf('79', plain,
% 1.18/1.44      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.18/1.44      inference('sup-', [status(thm)], ['77', '78'])).
% 1.18/1.44  thf('80', plain,
% 1.18/1.44      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.18/1.44        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['46', '49'])).
% 1.18/1.44  thf('81', plain,
% 1.18/1.44      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['79', '80'])).
% 1.18/1.44  thf('82', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.18/1.44      inference('clc', [status(thm)], ['76', '81'])).
% 1.18/1.44  thf('83', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (((sk_B) = (k2_relat_1 @ sk_C_1))
% 1.18/1.44          | ~ (r2_hidden @ X0 @ sk_A)
% 1.18/1.44          | ((sk_C @ sk_B @ sk_C_1) != (k1_funct_1 @ sk_C_1 @ X0)))),
% 1.18/1.44      inference('demod', [status(thm)], ['34', '35', '36', '82'])).
% 1.18/1.44  thf('84', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 1.18/1.44      inference('demod', [status(thm)], ['26', '27'])).
% 1.18/1.44  thf('85', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (r2_hidden @ X0 @ sk_A)
% 1.18/1.44          | ((sk_C @ sk_B @ sk_C_1) != (k1_funct_1 @ sk_C_1 @ X0)))),
% 1.18/1.44      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 1.18/1.44  thf('86', plain,
% 1.18/1.44      ((((sk_C @ sk_B @ sk_C_1) != (sk_C @ sk_B @ sk_C_1))
% 1.18/1.44        | ~ (r2_hidden @ (sk_E @ (sk_C @ sk_B @ sk_C_1)) @ sk_A))),
% 1.18/1.44      inference('sup-', [status(thm)], ['31', '85'])).
% 1.18/1.44  thf('87', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 1.18/1.44      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 1.18/1.44  thf('88', plain,
% 1.18/1.44      (![X34 : $i]:
% 1.18/1.44         (~ (r2_hidden @ X34 @ sk_B) | (r2_hidden @ (sk_E @ X34) @ sk_A))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('89', plain, ((r2_hidden @ (sk_E @ (sk_C @ sk_B @ sk_C_1)) @ sk_A)),
% 1.18/1.44      inference('sup-', [status(thm)], ['87', '88'])).
% 1.18/1.44  thf('90', plain, (((sk_C @ sk_B @ sk_C_1) != (sk_C @ sk_B @ sk_C_1))),
% 1.18/1.44      inference('demod', [status(thm)], ['86', '89'])).
% 1.18/1.44  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 1.18/1.44  
% 1.18/1.44  % SZS output end Refutation
% 1.18/1.44  
% 1.18/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
