%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ReOLds8hcf

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 136 expanded)
%              Number of leaves         :   42 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  667 (1484 expanded)
%              Number of equality atoms :   46 (  98 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t50_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k8_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k10_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','26'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('30',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','42'])).

thf('44',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('45',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['19','45'])).

thf('47',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['17','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','47','50'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( r1_tarski @ X14 @ ( k10_relat_1 @ X15 @ ( k9_relat_1 @ X15 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['8','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ReOLds8hcf
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 122 iterations in 0.082s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(t50_funct_2, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( r1_tarski @ C @ A ) =>
% 0.20/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.53           ( r1_tarski @
% 0.20/0.53             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.53            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53          ( ( r1_tarski @ C @ A ) =>
% 0.20/0.53            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.53              ( r1_tarski @
% 0.20/0.53                C @ 
% 0.20/0.53                ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t50_funct_2])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (~ (r1_tarski @ sk_C_1 @ 
% 0.20/0.53          (k8_relset_1 @ sk_A @ sk_B_1 @ sk_D @ 
% 0.20/0.53           (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.53          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D @ X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (~ (r1_tarski @ sk_C_1 @ 
% 0.20/0.53          (k8_relset_1 @ sk_A @ sk_B_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.20/0.53          | ((k8_relset_1 @ X24 @ X25 @ X23 @ X26) = (k10_relat_1 @ X23 @ X26)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (~ (r1_tarski @ sk_C_1 @ 
% 0.20/0.53          (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '7'])).
% 0.20/0.53  thf('9', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d1_funct_2, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_1, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.20/0.53          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.20/0.53          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.20/0.53        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf(zf_stmt_2, axiom,
% 0.20/0.53    (![B:$i,A:$i]:
% 0.20/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_5, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.53         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.20/0.53          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.20/0.53          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.20/0.53        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.53  thf('18', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X4 : $i, X6 : $i]:
% 0.20/0.53         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X4 : $i, X6 : $i]:
% 0.20/0.53         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.53  thf('24', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.53  thf(t69_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.53       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ X8 @ X9)
% 0.20/0.53          | ~ (r1_tarski @ X8 @ X9)
% 0.20/0.53          | (v1_xboole_0 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.53  thf(d1_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf('30', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.53          | (r2_hidden @ X3 @ X5)
% 0.20/0.53          | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.20/0.53         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((((v1_xboole_0 @ sk_C_1) | (r2_hidden @ (sk_B @ sk_C_1) @ k1_xboole_0)))
% 0.20/0.53         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X4 : $i, X6 : $i]:
% 0.20/0.53         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (~ (r1_tarski @ sk_C_1 @ 
% 0.20/0.53          (k8_relset_1 @ sk_A @ sk_B_1 @ sk_D @ 
% 0.20/0.53           (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (((r2_hidden @ (sk_B @ sk_C_1) @ k1_xboole_0))
% 0.20/0.53         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('clc', [status(thm)], ['34', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf('45', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['19', '45'])).
% 0.20/0.53  thf('47', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['17', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.20/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '47', '50'])).
% 0.20/0.53  thf(t146_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.53         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.20/0.53          | (r1_tarski @ X14 @ (k10_relat_1 @ X15 @ (k9_relat_1 @ X15 @ X14)))
% 0.20/0.53          | ~ (v1_relat_1 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.53          | ~ (v1_relat_1 @ sk_D)
% 0.20/0.53          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.53          | (v1_relat_1 @ X10)
% 0.20/0.53          | ~ (v1_relat_1 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf(fc6_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.53          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['53', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      ((r1_tarski @ sk_C_1 @ 
% 0.20/0.53        (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '59'])).
% 0.20/0.53  thf('61', plain, ($false), inference('demod', [status(thm)], ['8', '60'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
