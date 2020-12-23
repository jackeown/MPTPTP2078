%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.psVfdg1qgJ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:23 EST 2020

% Result     : Theorem 19.71s
% Output     : Refutation 19.71s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 210 expanded)
%              Number of leaves         :   43 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  822 (2340 expanded)
%              Number of equality atoms :   65 ( 150 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('6',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ X0 )
      | ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('9',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('10',plain,(
    ! [X19: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('12',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ X0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( sk_D_1 @ ( sk_B @ X0 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

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

thf('26',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X26 ) @ X24 )
      | ( X26
       != ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( k1_funct_1 @ X24 @ X23 ) ) @ X24 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['28','29','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_D_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16 = X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ ( k1_tarski @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','42'])).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( X25 = k1_xboole_0 )
      | ( X25
       != ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k1_funct_1 @ X24 @ X23 )
        = k1_xboole_0 )
      | ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( k1_funct_1 @ X24 @ X23 ) ) @ X24 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D_2 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D_2 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('55',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D_2 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k2_tarski @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16 = X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ ( k1_tarski @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ sk_D_2 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['56','59'])).

thf('61',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['43','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.psVfdg1qgJ
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 19.71/19.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.71/19.90  % Solved by: fo/fo7.sh
% 19.71/19.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.71/19.90  % done 6616 iterations in 19.426s
% 19.71/19.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.71/19.90  % SZS output start Refutation
% 19.71/19.90  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 19.71/19.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.71/19.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 19.71/19.90  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 19.71/19.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 19.71/19.90  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 19.71/19.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 19.71/19.90  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 19.71/19.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.71/19.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.71/19.90  thf(sk_A_type, type, sk_A: $i).
% 19.71/19.90  thf(sk_B_type, type, sk_B: $i > $i).
% 19.71/19.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 19.71/19.90  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 19.71/19.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 19.71/19.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 19.71/19.90  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 19.71/19.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 19.71/19.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.71/19.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.71/19.90  thf(sk_D_2_type, type, sk_D_2: $i).
% 19.71/19.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 19.71/19.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.71/19.90  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 19.71/19.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 19.71/19.90  thf(t65_funct_2, conjecture,
% 19.71/19.90    (![A:$i,B:$i,C:$i,D:$i]:
% 19.71/19.90     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 19.71/19.90         ( m1_subset_1 @
% 19.71/19.90           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 19.71/19.90       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 19.71/19.90  thf(zf_stmt_0, negated_conjecture,
% 19.71/19.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 19.71/19.90        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 19.71/19.90            ( m1_subset_1 @
% 19.71/19.90              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 19.71/19.90          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 19.71/19.90    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 19.71/19.90  thf('0', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B_1))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf(d1_funct_2, axiom,
% 19.71/19.90    (![A:$i,B:$i,C:$i]:
% 19.71/19.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.71/19.90       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.71/19.90           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 19.71/19.90             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 19.71/19.90         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.71/19.90           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 19.71/19.90             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 19.71/19.90  thf(zf_stmt_1, axiom,
% 19.71/19.90    (![B:$i,A:$i]:
% 19.71/19.90     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.71/19.90       ( zip_tseitin_0 @ B @ A ) ))).
% 19.71/19.90  thf('2', plain,
% 19.71/19.90      (![X39 : $i, X40 : $i]:
% 19.71/19.90         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.71/19.90  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 19.71/19.90  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 19.71/19.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.71/19.90  thf('4', plain,
% 19.71/19.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.71/19.90         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 19.71/19.90      inference('sup+', [status(thm)], ['2', '3'])).
% 19.71/19.90  thf('5', plain,
% 19.71/19.90      ((m1_subset_1 @ sk_D_2 @ 
% 19.71/19.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 19.71/19.90  thf(zf_stmt_3, axiom,
% 19.71/19.90    (![C:$i,B:$i,A:$i]:
% 19.71/19.90     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 19.71/19.90       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 19.71/19.90  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 19.71/19.90  thf(zf_stmt_5, axiom,
% 19.71/19.90    (![A:$i,B:$i,C:$i]:
% 19.71/19.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.71/19.90       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 19.71/19.90         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.71/19.90           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 19.71/19.90             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 19.71/19.90  thf('6', plain,
% 19.71/19.90      (![X44 : $i, X45 : $i, X46 : $i]:
% 19.71/19.90         (~ (zip_tseitin_0 @ X44 @ X45)
% 19.71/19.90          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 19.71/19.90          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.71/19.90  thf('7', plain,
% 19.71/19.90      (((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 19.71/19.90        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 19.71/19.90      inference('sup-', [status(thm)], ['5', '6'])).
% 19.71/19.90  thf('8', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         ((r1_tarski @ (k1_tarski @ sk_B_1) @ X0)
% 19.71/19.90          | (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 19.71/19.90      inference('sup-', [status(thm)], ['4', '7'])).
% 19.71/19.90  thf(t29_mcart_1, axiom,
% 19.71/19.90    (![A:$i]:
% 19.71/19.90     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 19.71/19.90          ( ![B:$i]:
% 19.71/19.90            ( ~( ( r2_hidden @ B @ A ) & 
% 19.71/19.90                 ( ![C:$i,D:$i,E:$i]:
% 19.71/19.90                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 19.71/19.90                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 19.71/19.90  thf('9', plain,
% 19.71/19.90      (![X35 : $i]:
% 19.71/19.90         (((X35) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X35) @ X35))),
% 19.71/19.90      inference('cnf', [status(esa)], [t29_mcart_1])).
% 19.71/19.90  thf(t31_zfmisc_1, axiom,
% 19.71/19.90    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 19.71/19.90  thf('10', plain, (![X19 : $i]: ((k3_tarski @ (k1_tarski @ X19)) = (X19))),
% 19.71/19.90      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 19.71/19.90  thf(d4_tarski, axiom,
% 19.71/19.90    (![A:$i,B:$i]:
% 19.71/19.90     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 19.71/19.90       ( ![C:$i]:
% 19.71/19.90         ( ( r2_hidden @ C @ B ) <=>
% 19.71/19.90           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 19.71/19.90  thf('11', plain,
% 19.71/19.90      (![X8 : $i, X10 : $i, X11 : $i]:
% 19.71/19.90         (~ (r2_hidden @ X11 @ X10)
% 19.71/19.90          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 19.71/19.90          | ((X10) != (k3_tarski @ X8)))),
% 19.71/19.90      inference('cnf', [status(esa)], [d4_tarski])).
% 19.71/19.90  thf('12', plain,
% 19.71/19.90      (![X8 : $i, X11 : $i]:
% 19.71/19.90         ((r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 19.71/19.90          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 19.71/19.90      inference('simplify', [status(thm)], ['11'])).
% 19.71/19.90  thf('13', plain,
% 19.71/19.90      (![X0 : $i, X1 : $i]:
% 19.71/19.90         (~ (r2_hidden @ X1 @ X0)
% 19.71/19.90          | (r2_hidden @ (sk_D_1 @ X1 @ (k1_tarski @ X0)) @ (k1_tarski @ X0)))),
% 19.71/19.90      inference('sup-', [status(thm)], ['10', '12'])).
% 19.71/19.90  thf('14', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         (((X0) = (k1_xboole_0))
% 19.71/19.90          | (r2_hidden @ (sk_D_1 @ (sk_B @ X0) @ (k1_tarski @ X0)) @ 
% 19.71/19.90             (k1_tarski @ X0)))),
% 19.71/19.90      inference('sup-', [status(thm)], ['9', '13'])).
% 19.71/19.90  thf(t7_ordinal1, axiom,
% 19.71/19.90    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.71/19.90  thf('15', plain,
% 19.71/19.90      (![X27 : $i, X28 : $i]:
% 19.71/19.90         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 19.71/19.90      inference('cnf', [status(esa)], [t7_ordinal1])).
% 19.71/19.90  thf('16', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         (((X0) = (k1_xboole_0))
% 19.71/19.90          | ~ (r1_tarski @ (k1_tarski @ X0) @ 
% 19.71/19.90               (sk_D_1 @ (sk_B @ X0) @ (k1_tarski @ X0))))),
% 19.71/19.90      inference('sup-', [status(thm)], ['14', '15'])).
% 19.71/19.90  thf('17', plain,
% 19.71/19.90      (((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 19.71/19.90        | ((sk_B_1) = (k1_xboole_0)))),
% 19.71/19.90      inference('sup-', [status(thm)], ['8', '16'])).
% 19.71/19.90  thf('18', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf('19', plain,
% 19.71/19.90      (![X41 : $i, X42 : $i, X43 : $i]:
% 19.71/19.90         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 19.71/19.90          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 19.71/19.90          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.71/19.90  thf('20', plain,
% 19.71/19.90      ((~ (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 19.71/19.90        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)))),
% 19.71/19.90      inference('sup-', [status(thm)], ['18', '19'])).
% 19.71/19.90  thf('21', plain,
% 19.71/19.90      ((m1_subset_1 @ sk_D_2 @ 
% 19.71/19.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf(redefinition_k1_relset_1, axiom,
% 19.71/19.90    (![A:$i,B:$i,C:$i]:
% 19.71/19.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.71/19.90       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 19.71/19.90  thf('22', plain,
% 19.71/19.90      (![X32 : $i, X33 : $i, X34 : $i]:
% 19.71/19.90         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 19.71/19.90          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 19.71/19.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 19.71/19.90  thf('23', plain,
% 19.71/19.90      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)
% 19.71/19.90         = (k1_relat_1 @ sk_D_2))),
% 19.71/19.90      inference('sup-', [status(thm)], ['21', '22'])).
% 19.71/19.90  thf('24', plain,
% 19.71/19.90      ((~ (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 19.71/19.90        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 19.71/19.90      inference('demod', [status(thm)], ['20', '23'])).
% 19.71/19.90  thf('25', plain,
% 19.71/19.90      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 19.71/19.90      inference('sup-', [status(thm)], ['17', '24'])).
% 19.71/19.90  thf(d4_funct_1, axiom,
% 19.71/19.90    (![A:$i]:
% 19.71/19.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 19.71/19.90       ( ![B:$i,C:$i]:
% 19.71/19.90         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 19.71/19.90             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 19.71/19.90               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 19.71/19.90           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 19.71/19.90             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 19.71/19.90               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 19.71/19.90  thf('26', plain,
% 19.71/19.90      (![X23 : $i, X24 : $i, X26 : $i]:
% 19.71/19.90         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 19.71/19.90          | (r2_hidden @ (k4_tarski @ X23 @ X26) @ X24)
% 19.71/19.90          | ((X26) != (k1_funct_1 @ X24 @ X23))
% 19.71/19.90          | ~ (v1_funct_1 @ X24)
% 19.71/19.90          | ~ (v1_relat_1 @ X24))),
% 19.71/19.90      inference('cnf', [status(esa)], [d4_funct_1])).
% 19.71/19.90  thf('27', plain,
% 19.71/19.90      (![X23 : $i, X24 : $i]:
% 19.71/19.90         (~ (v1_relat_1 @ X24)
% 19.71/19.90          | ~ (v1_funct_1 @ X24)
% 19.71/19.90          | (r2_hidden @ (k4_tarski @ X23 @ (k1_funct_1 @ X24 @ X23)) @ X24)
% 19.71/19.90          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X24)))),
% 19.71/19.90      inference('simplify', [status(thm)], ['26'])).
% 19.71/19.90  thf('28', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         (~ (r2_hidden @ X0 @ sk_A)
% 19.71/19.90          | ((sk_B_1) = (k1_xboole_0))
% 19.71/19.90          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ sk_D_2)
% 19.71/19.90          | ~ (v1_funct_1 @ sk_D_2)
% 19.71/19.90          | ~ (v1_relat_1 @ sk_D_2))),
% 19.71/19.90      inference('sup-', [status(thm)], ['25', '27'])).
% 19.71/19.90  thf('29', plain, ((v1_funct_1 @ sk_D_2)),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf('30', plain,
% 19.71/19.90      ((m1_subset_1 @ sk_D_2 @ 
% 19.71/19.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf(cc1_relset_1, axiom,
% 19.71/19.90    (![A:$i,B:$i,C:$i]:
% 19.71/19.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.71/19.90       ( v1_relat_1 @ C ) ))).
% 19.71/19.90  thf('31', plain,
% 19.71/19.90      (![X29 : $i, X30 : $i, X31 : $i]:
% 19.71/19.90         ((v1_relat_1 @ X29)
% 19.71/19.90          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 19.71/19.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 19.71/19.90  thf('32', plain, ((v1_relat_1 @ sk_D_2)),
% 19.71/19.90      inference('sup-', [status(thm)], ['30', '31'])).
% 19.71/19.90  thf('33', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         (~ (r2_hidden @ X0 @ sk_A)
% 19.71/19.90          | ((sk_B_1) = (k1_xboole_0))
% 19.71/19.90          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ sk_D_2))),
% 19.71/19.90      inference('demod', [status(thm)], ['28', '29', '32'])).
% 19.71/19.90  thf('34', plain,
% 19.71/19.90      (((r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_1)) @ 
% 19.71/19.90         sk_D_2)
% 19.71/19.90        | ((sk_B_1) = (k1_xboole_0)))),
% 19.71/19.90      inference('sup-', [status(thm)], ['1', '33'])).
% 19.71/19.90  thf('35', plain,
% 19.71/19.90      ((m1_subset_1 @ sk_D_2 @ 
% 19.71/19.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf(l3_subset_1, axiom,
% 19.71/19.90    (![A:$i,B:$i]:
% 19.71/19.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 19.71/19.90       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 19.71/19.90  thf('36', plain,
% 19.71/19.90      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.71/19.90         (~ (r2_hidden @ X20 @ X21)
% 19.71/19.90          | (r2_hidden @ X20 @ X22)
% 19.71/19.90          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 19.71/19.90      inference('cnf', [status(esa)], [l3_subset_1])).
% 19.71/19.90  thf('37', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)))
% 19.71/19.90          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 19.71/19.90      inference('sup-', [status(thm)], ['35', '36'])).
% 19.71/19.90  thf('38', plain,
% 19.71/19.90      ((((sk_B_1) = (k1_xboole_0))
% 19.71/19.90        | (r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_1)) @ 
% 19.71/19.90           (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 19.71/19.90      inference('sup-', [status(thm)], ['34', '37'])).
% 19.71/19.90  thf(t129_zfmisc_1, axiom,
% 19.71/19.90    (![A:$i,B:$i,C:$i,D:$i]:
% 19.71/19.90     ( ( r2_hidden @
% 19.71/19.90         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 19.71/19.90       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 19.71/19.90  thf('39', plain,
% 19.71/19.90      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 19.71/19.90         (((X16) = (X17))
% 19.71/19.90          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ 
% 19.71/19.90               (k2_zfmisc_1 @ X15 @ (k1_tarski @ X17))))),
% 19.71/19.90      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 19.71/19.90  thf('40', plain,
% 19.71/19.90      ((((sk_B_1) = (k1_xboole_0))
% 19.71/19.90        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1)))),
% 19.71/19.90      inference('sup-', [status(thm)], ['38', '39'])).
% 19.71/19.90  thf('41', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B_1))),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf('42', plain, (((sk_B_1) = (k1_xboole_0))),
% 19.71/19.90      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 19.71/19.90  thf('43', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (k1_xboole_0))),
% 19.71/19.90      inference('demod', [status(thm)], ['0', '42'])).
% 19.71/19.90  thf('44', plain,
% 19.71/19.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 19.71/19.90         ((r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 19.71/19.90          | ((X25) = (k1_xboole_0))
% 19.71/19.90          | ((X25) != (k1_funct_1 @ X24 @ X23))
% 19.71/19.90          | ~ (v1_funct_1 @ X24)
% 19.71/19.90          | ~ (v1_relat_1 @ X24))),
% 19.71/19.90      inference('cnf', [status(esa)], [d4_funct_1])).
% 19.71/19.90  thf('45', plain,
% 19.71/19.90      (![X23 : $i, X24 : $i]:
% 19.71/19.90         (~ (v1_relat_1 @ X24)
% 19.71/19.90          | ~ (v1_funct_1 @ X24)
% 19.71/19.90          | ((k1_funct_1 @ X24 @ X23) = (k1_xboole_0))
% 19.71/19.90          | (r2_hidden @ X23 @ (k1_relat_1 @ X24)))),
% 19.71/19.90      inference('simplify', [status(thm)], ['44'])).
% 19.71/19.90  thf('46', plain,
% 19.71/19.90      (![X23 : $i, X24 : $i]:
% 19.71/19.90         (~ (v1_relat_1 @ X24)
% 19.71/19.90          | ~ (v1_funct_1 @ X24)
% 19.71/19.90          | (r2_hidden @ (k4_tarski @ X23 @ (k1_funct_1 @ X24 @ X23)) @ X24)
% 19.71/19.90          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X24)))),
% 19.71/19.90      inference('simplify', [status(thm)], ['26'])).
% 19.71/19.90  thf('47', plain,
% 19.71/19.90      (![X0 : $i, X1 : $i]:
% 19.71/19.90         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 19.71/19.90          | ~ (v1_funct_1 @ X0)
% 19.71/19.90          | ~ (v1_relat_1 @ X0)
% 19.71/19.90          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 19.71/19.90          | ~ (v1_funct_1 @ X0)
% 19.71/19.90          | ~ (v1_relat_1 @ X0))),
% 19.71/19.90      inference('sup-', [status(thm)], ['45', '46'])).
% 19.71/19.90  thf('48', plain,
% 19.71/19.90      (![X0 : $i, X1 : $i]:
% 19.71/19.90         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 19.71/19.90          | ~ (v1_relat_1 @ X0)
% 19.71/19.90          | ~ (v1_funct_1 @ X0)
% 19.71/19.90          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 19.71/19.90      inference('simplify', [status(thm)], ['47'])).
% 19.71/19.90  thf('49', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)))
% 19.71/19.90          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 19.71/19.90      inference('sup-', [status(thm)], ['35', '36'])).
% 19.71/19.90  thf('50', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         (((k1_funct_1 @ sk_D_2 @ X0) = (k1_xboole_0))
% 19.71/19.90          | ~ (v1_funct_1 @ sk_D_2)
% 19.71/19.90          | ~ (v1_relat_1 @ sk_D_2)
% 19.71/19.90          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ 
% 19.71/19.90             (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 19.71/19.90      inference('sup-', [status(thm)], ['48', '49'])).
% 19.71/19.90  thf('51', plain, ((v1_funct_1 @ sk_D_2)),
% 19.71/19.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.90  thf('52', plain, ((v1_relat_1 @ sk_D_2)),
% 19.71/19.90      inference('sup-', [status(thm)], ['30', '31'])).
% 19.71/19.90  thf('53', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         (((k1_funct_1 @ sk_D_2 @ X0) = (k1_xboole_0))
% 19.71/19.90          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ 
% 19.71/19.90             (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 19.71/19.90      inference('demod', [status(thm)], ['50', '51', '52'])).
% 19.71/19.90  thf('54', plain, (((sk_B_1) = (k1_xboole_0))),
% 19.71/19.90      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 19.71/19.90  thf(t69_enumset1, axiom,
% 19.71/19.90    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 19.71/19.90  thf('55', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 19.71/19.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 19.71/19.90  thf('56', plain,
% 19.71/19.90      (![X0 : $i]:
% 19.71/19.90         (((k1_funct_1 @ sk_D_2 @ X0) = (k1_xboole_0))
% 19.71/19.90          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ 
% 19.71/19.90             (k2_zfmisc_1 @ sk_A @ (k2_tarski @ k1_xboole_0 @ k1_xboole_0))))),
% 19.71/19.90      inference('demod', [status(thm)], ['53', '54', '55'])).
% 19.71/19.90  thf('57', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 19.71/19.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 19.71/19.90  thf('58', plain,
% 19.71/19.90      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 19.71/19.90         (((X16) = (X17))
% 19.71/19.90          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ 
% 19.71/19.90               (k2_zfmisc_1 @ X15 @ (k1_tarski @ X17))))),
% 19.71/19.90      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 19.71/19.90  thf('59', plain,
% 19.71/19.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.71/19.90         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 19.71/19.90             (k2_zfmisc_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 19.71/19.90          | ((X2) = (X0)))),
% 19.71/19.90      inference('sup-', [status(thm)], ['57', '58'])).
% 19.71/19.90  thf('60', plain, (![X0 : $i]: ((k1_funct_1 @ sk_D_2 @ X0) = (k1_xboole_0))),
% 19.71/19.90      inference('clc', [status(thm)], ['56', '59'])).
% 19.71/19.90  thf('61', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 19.71/19.90      inference('demod', [status(thm)], ['43', '60'])).
% 19.71/19.90  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 19.71/19.90  
% 19.71/19.90  % SZS output end Refutation
% 19.71/19.90  
% 19.74/19.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
