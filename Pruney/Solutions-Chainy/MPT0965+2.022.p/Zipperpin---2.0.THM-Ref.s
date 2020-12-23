%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cyoZlknefg

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 178 expanded)
%              Number of leaves         :   42 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  612 (1850 expanded)
%              Number of equality atoms :   29 (  95 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_D @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X23 @ X22 ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['3','28'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X6 @ X7 ) )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['23','24'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) @ X18 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('45',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('46',plain,
    ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','52'])).

thf('54',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ),
    inference(clc,[status(thm)],['31','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cyoZlknefg
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:45:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.60  % Solved by: fo/fo7.sh
% 0.22/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.60  % done 119 iterations in 0.141s
% 0.22/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.60  % SZS output start Refutation
% 0.22/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.22/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.60  thf(t7_funct_2, conjecture,
% 0.22/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.60       ( ( r2_hidden @ C @ A ) =>
% 0.22/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.60           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.22/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.60            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.60          ( ( r2_hidden @ C @ A ) =>
% 0.22/0.60            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.60              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.22/0.60    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.22/0.60  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('1', plain,
% 0.22/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf(cc2_relset_1, axiom,
% 0.22/0.60    (![A:$i,B:$i,C:$i]:
% 0.22/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.60  thf('2', plain,
% 0.22/0.60      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.60         ((v5_relat_1 @ X25 @ X27)
% 0.22/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.22/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.60  thf('3', plain, ((v5_relat_1 @ sk_D @ sk_B_1)),
% 0.22/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.60  thf('4', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf(d1_funct_2, axiom,
% 0.22/0.60    (![A:$i,B:$i,C:$i]:
% 0.22/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.22/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.60  thf(zf_stmt_1, axiom,
% 0.22/0.60    (![C:$i,B:$i,A:$i]:
% 0.22/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.60  thf('6', plain,
% 0.22/0.60      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.60         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.22/0.60          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.22/0.60          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.60  thf('7', plain,
% 0.22/0.60      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.22/0.60        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.22/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.60  thf(zf_stmt_2, axiom,
% 0.22/0.60    (![B:$i,A:$i]:
% 0.22/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.22/0.60  thf('8', plain,
% 0.22/0.60      (![X31 : $i, X32 : $i]:
% 0.22/0.60         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.60  thf('9', plain,
% 0.22/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.22/0.60  thf(zf_stmt_5, axiom,
% 0.22/0.60    (![A:$i,B:$i,C:$i]:
% 0.22/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.60  thf('10', plain,
% 0.22/0.60      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.60         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.22/0.60          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.22/0.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.60  thf('11', plain,
% 0.22/0.60      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.22/0.60        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.22/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.60  thf('12', plain,
% 0.22/0.60      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.22/0.60      inference('sup-', [status(thm)], ['8', '11'])).
% 0.22/0.60  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('14', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.22/0.60      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.22/0.60  thf('15', plain,
% 0.22/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.60    (![A:$i,B:$i,C:$i]:
% 0.22/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.60  thf('16', plain,
% 0.22/0.60      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.60         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.22/0.60          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.22/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.60  thf('17', plain,
% 0.22/0.60      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.22/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.60  thf('18', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.22/0.60      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.22/0.60  thf(t176_funct_1, axiom,
% 0.22/0.60    (![A:$i,B:$i,C:$i]:
% 0.22/0.60     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.60       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.22/0.60         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.22/0.60  thf('19', plain,
% 0.22/0.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.60         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.22/0.60          | (m1_subset_1 @ (k1_funct_1 @ X23 @ X22) @ X24)
% 0.22/0.60          | ~ (v1_funct_1 @ X23)
% 0.22/0.60          | ~ (v5_relat_1 @ X23 @ X24)
% 0.22/0.60          | ~ (v1_relat_1 @ X23))),
% 0.22/0.60      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.22/0.60  thf('20', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]:
% 0.22/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.60          | ~ (v1_relat_1 @ sk_D)
% 0.22/0.60          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.22/0.60          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.60          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.22/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.60  thf('21', plain,
% 0.22/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf(cc2_relat_1, axiom,
% 0.22/0.60    (![A:$i]:
% 0.22/0.60     ( ( v1_relat_1 @ A ) =>
% 0.22/0.60       ( ![B:$i]:
% 0.22/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.60  thf('22', plain,
% 0.22/0.60      (![X13 : $i, X14 : $i]:
% 0.22/0.60         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.22/0.60          | (v1_relat_1 @ X13)
% 0.22/0.60          | ~ (v1_relat_1 @ X14))),
% 0.22/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.60  thf('23', plain,
% 0.22/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.22/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.60  thf(fc6_relat_1, axiom,
% 0.22/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.60  thf('24', plain,
% 0.22/0.60      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.22/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.60  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.60  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('27', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]:
% 0.22/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.60          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.22/0.60          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.22/0.60      inference('demod', [status(thm)], ['20', '25', '26'])).
% 0.22/0.60  thf('28', plain,
% 0.22/0.60      (![X0 : $i]:
% 0.22/0.60         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ X0)
% 0.22/0.60          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.22/0.60      inference('sup-', [status(thm)], ['4', '27'])).
% 0.22/0.60  thf('29', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.22/0.60      inference('sup-', [status(thm)], ['3', '28'])).
% 0.22/0.60  thf(t2_subset, axiom,
% 0.22/0.60    (![A:$i,B:$i]:
% 0.22/0.60     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.60       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.60  thf('30', plain,
% 0.22/0.60      (![X8 : $i, X9 : $i]:
% 0.22/0.60         ((r2_hidden @ X8 @ X9)
% 0.22/0.60          | (v1_xboole_0 @ X9)
% 0.22/0.60          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.22/0.60      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.60  thf('31', plain,
% 0.22/0.60      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.60        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1))),
% 0.22/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.60  thf(fc3_zfmisc_1, axiom,
% 0.22/0.60    (![A:$i,B:$i]:
% 0.22/0.60     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.22/0.60  thf('32', plain,
% 0.22/0.60      (![X6 : $i, X7 : $i]:
% 0.22/0.60         ((v1_xboole_0 @ (k2_zfmisc_1 @ X6 @ X7)) | ~ (v1_xboole_0 @ X7))),
% 0.22/0.60      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.22/0.60  thf('33', plain,
% 0.22/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf(t3_subset, axiom,
% 0.22/0.60    (![A:$i,B:$i]:
% 0.22/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.60  thf('34', plain,
% 0.22/0.60      (![X10 : $i, X11 : $i]:
% 0.22/0.60         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.60  thf('35', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.22/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.60  thf(t25_relat_1, axiom,
% 0.22/0.60    (![A:$i]:
% 0.22/0.60     ( ( v1_relat_1 @ A ) =>
% 0.22/0.60       ( ![B:$i]:
% 0.22/0.60         ( ( v1_relat_1 @ B ) =>
% 0.22/0.60           ( ( r1_tarski @ A @ B ) =>
% 0.22/0.60             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.22/0.60               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.22/0.60  thf('36', plain,
% 0.22/0.60      (![X20 : $i, X21 : $i]:
% 0.22/0.60         (~ (v1_relat_1 @ X20)
% 0.22/0.60          | (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 0.22/0.60          | ~ (r1_tarski @ X21 @ X20)
% 0.22/0.60          | ~ (v1_relat_1 @ X21))),
% 0.22/0.60      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.22/0.60  thf('37', plain,
% 0.22/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.22/0.60        | (r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.22/0.60           (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.22/0.60        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.60  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.60  thf('39', plain,
% 0.22/0.60      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.22/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.60  thf('40', plain,
% 0.22/0.60      ((r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.22/0.60        (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.60      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.22/0.60  thf(d10_xboole_0, axiom,
% 0.22/0.60    (![A:$i,B:$i]:
% 0.22/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.60  thf('41', plain,
% 0.22/0.60      (![X3 : $i, X5 : $i]:
% 0.22/0.60         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.60  thf('42', plain,
% 0.22/0.60      ((~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.22/0.60           (k1_relat_1 @ sk_D))
% 0.22/0.60        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (k1_relat_1 @ sk_D)))),
% 0.22/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.60  thf('43', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.22/0.60      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.22/0.60  thf(t193_relat_1, axiom,
% 0.22/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.22/0.60  thf('44', plain,
% 0.22/0.60      (![X18 : $i, X19 : $i]:
% 0.22/0.60         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19)) @ X18)),
% 0.22/0.60      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.22/0.60  thf('45', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.22/0.60      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.22/0.60  thf('46', plain, (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.22/0.60      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.22/0.60  thf(fc10_relat_1, axiom,
% 0.22/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.22/0.60  thf('47', plain,
% 0.22/0.60      (![X15 : $i]:
% 0.22/0.60         ((v1_xboole_0 @ (k1_relat_1 @ X15)) | ~ (v1_xboole_0 @ X15))),
% 0.22/0.60      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.22/0.60  thf('48', plain,
% 0.22/0.60      (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.60      inference('sup+', [status(thm)], ['46', '47'])).
% 0.22/0.60  thf('49', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf(d1_xboole_0, axiom,
% 0.22/0.60    (![A:$i]:
% 0.22/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.60  thf('50', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.60  thf('51', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.60  thf('52', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.22/0.60      inference('clc', [status(thm)], ['48', '51'])).
% 0.22/0.60  thf('53', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.60      inference('sup-', [status(thm)], ['32', '52'])).
% 0.22/0.60  thf('54', plain, ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.22/0.60      inference('clc', [status(thm)], ['31', '53'])).
% 0.22/0.60  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 0.22/0.60  
% 0.22/0.60  % SZS output end Refutation
% 0.22/0.60  
% 0.22/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
