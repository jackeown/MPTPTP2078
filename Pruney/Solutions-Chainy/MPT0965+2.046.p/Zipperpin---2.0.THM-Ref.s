%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r0ngWmpB0E

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:04 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 148 expanded)
%              Number of leaves         :   42 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  705 (1276 expanded)
%              Number of equality atoms :   35 (  58 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X21 @ X20 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['18','23','24'])).

thf('26',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('30',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D ) ) @ sk_B_1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(clc,[status(thm)],['39','59'])).

thf('61',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['26','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r0ngWmpB0E
% 0.15/0.37  % Computer   : n012.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:49:22 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 179 iterations in 0.187s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.67  thf(t7_funct_2, conjecture,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.67       ( ( r2_hidden @ C @ A ) =>
% 0.47/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.67           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.67          ( ( r2_hidden @ C @ A ) =>
% 0.47/0.67            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.67              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.47/0.67  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ sk_B_1)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('2', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(d1_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_1, axiom,
% 0.47/0.67    (![C:$i,B:$i,A:$i]:
% 0.47/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.67         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.47/0.67          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.47/0.67          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.47/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.67         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.47/0.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.47/0.67        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.47/0.67      inference('demod', [status(thm)], ['4', '7'])).
% 0.47/0.67  thf(zf_stmt_2, axiom,
% 0.47/0.67    (![B:$i,A:$i]:
% 0.47/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X31 : $i, X32 : $i]:
% 0.47/0.67         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_5, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.67         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.47/0.67          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.47/0.67          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.47/0.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['9', '12'])).
% 0.47/0.67  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('15', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.47/0.67  thf('16', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['8', '15'])).
% 0.47/0.67  thf(t12_funct_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.67       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.67         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.47/0.67          | (r2_hidden @ (k1_funct_1 @ X21 @ X20) @ (k2_relat_1 @ X21))
% 0.47/0.67          | ~ (v1_funct_1 @ X21)
% 0.47/0.67          | ~ (v1_relat_1 @ X21))),
% 0.47/0.67      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.47/0.67          | ~ (v1_relat_1 @ sk_D)
% 0.47/0.67          | ~ (v1_funct_1 @ sk_D)
% 0.47/0.67          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc2_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.67  thf('20', plain,
% 0.47/0.67      (![X16 : $i, X17 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.47/0.67          | (v1_relat_1 @ X16)
% 0.47/0.67          | ~ (v1_relat_1 @ X17))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.67  thf(fc6_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.67  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.67      inference('demod', [status(thm)], ['21', '22'])).
% 0.47/0.67  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.47/0.67          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.47/0.67      inference('demod', [status(thm)], ['18', '23', '24'])).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['1', '25'])).
% 0.47/0.67  thf(d3_tarski, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (![X4 : $i, X6 : $i]:
% 0.47/0.67         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(dt_k2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.67         ((m1_subset_1 @ (k2_relset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X23))
% 0.47/0.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ 
% 0.47/0.67        (k1_zfmisc_1 @ sk_B_1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.67  thf(t4_subset, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.47/0.67       ( m1_subset_1 @ A @ C ) ))).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X13 @ X14)
% 0.47/0.67          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.47/0.67          | (m1_subset_1 @ X13 @ X15))),
% 0.47/0.67      inference('cnf', [status(esa)], [t4_subset])).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.47/0.67          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.67         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.47/0.67          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.47/0.67          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.47/0.67      inference('demod', [status(thm)], ['32', '35'])).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.47/0.67          | (m1_subset_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_D)) @ sk_B_1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['27', '36'])).
% 0.47/0.67  thf(t2_subset, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ A @ B ) =>
% 0.47/0.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i]:
% 0.47/0.67         ((r2_hidden @ X11 @ X12)
% 0.47/0.67          | (v1_xboole_0 @ X12)
% 0.47/0.67          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.47/0.67      inference('cnf', [status(esa)], [t2_subset])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.47/0.67          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.67          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D)) @ sk_B_1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      (![X4 : $i, X6 : $i]:
% 0.47/0.67         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.67  thf(d1_xboole_0, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.67  thf('43', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.47/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.67  thf(d10_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      (![X7 : $i, X9 : $i]:
% 0.47/0.67         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.67  thf('46', plain,
% 0.47/0.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['42', '45'])).
% 0.47/0.67  thf('47', plain,
% 0.47/0.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['42', '45'])).
% 0.47/0.67  thf('48', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['46', '47'])).
% 0.47/0.67  thf('49', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((X0) != (k1_xboole_0))
% 0.47/0.67          | ~ (v1_xboole_0 @ X0)
% 0.47/0.67          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.67  thf('51', plain,
% 0.47/0.67      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['50'])).
% 0.47/0.67  thf('52', plain,
% 0.47/0.67      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.47/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.67  thf('53', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.47/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.67  thf('54', plain,
% 0.47/0.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X3 @ X4)
% 0.47/0.67          | (r2_hidden @ X3 @ X5)
% 0.47/0.67          | ~ (r1_tarski @ X4 @ X5))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.67  thf('55', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.67  thf('56', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['52', '55'])).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.67  thf('58', plain,
% 0.47/0.67      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.67  thf('59', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.47/0.67      inference('clc', [status(thm)], ['51', '58'])).
% 0.47/0.67  thf('60', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D)) @ sk_B_1)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.47/0.67      inference('clc', [status(thm)], ['39', '59'])).
% 0.47/0.67  thf('61', plain,
% 0.47/0.67      (![X4 : $i, X6 : $i]:
% 0.47/0.67         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.67  thf('62', plain,
% 0.47/0.67      (((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1)
% 0.47/0.67        | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.67  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1)),
% 0.47/0.67      inference('simplify', [status(thm)], ['62'])).
% 0.47/0.67  thf('64', plain,
% 0.47/0.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X3 @ X4)
% 0.47/0.67          | (r2_hidden @ X3 @ X5)
% 0.47/0.67          | ~ (r1_tarski @ X4 @ X5))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.67  thf('65', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.67  thf('66', plain, ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ sk_B_1)),
% 0.47/0.67      inference('sup-', [status(thm)], ['26', '65'])).
% 0.47/0.67  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
