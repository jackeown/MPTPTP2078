%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ZwymeMYSq

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:14 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 641 expanded)
%              Number of leaves         :   35 ( 194 expanded)
%              Depth                    :   20
%              Number of atoms          :  960 (8969 expanded)
%              Number of equality atoms :   77 ( 551 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('3',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf('28',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['33'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X28 ) @ X29 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','39'])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['41'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','62'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('68',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('69',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','63'])).

thf('72',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['33'])).

thf('73',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( v1_funct_2 @ X28 @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('84',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('85',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('86',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['41'])).

thf('93',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['45','70','82','83','91','92'])).

thf('94',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['42','93'])).

thf('95',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','94'])).

thf('96',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('97',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['45','70','82','92','83'])).

thf('98',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ZwymeMYSq
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:48 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 437 iterations in 0.617s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.08  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.08  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.08  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.08  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.90/1.08  thf(d1_funct_2, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.08       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.08           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.90/1.08             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.90/1.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.08           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.90/1.08             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, axiom,
% 0.90/1.08    (![B:$i,A:$i]:
% 0.90/1.08     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.08       ( zip_tseitin_0 @ B @ A ) ))).
% 0.90/1.08  thf('0', plain,
% 0.90/1.08      (![X20 : $i, X21 : $i]:
% 0.90/1.08         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(t9_funct_2, conjecture,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.90/1.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.08       ( ( r1_tarski @ B @ C ) =>
% 0.90/1.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.90/1.08           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.90/1.08             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_1, negated_conjecture,
% 0.90/1.08    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.90/1.08            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.08          ( ( r1_tarski @ B @ C ) =>
% 0.90/1.08            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.90/1.08              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.90/1.08                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.90/1.08  thf('1', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.90/1.08  thf(zf_stmt_3, axiom,
% 0.90/1.08    (![C:$i,B:$i,A:$i]:
% 0.90/1.08     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.90/1.08       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.08  thf(zf_stmt_5, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.08       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.90/1.08         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.08           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.90/1.08             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.08         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.90/1.08          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.90/1.08          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.08  thf('3', plain,
% 0.90/1.08      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['0', '3'])).
% 0.90/1.08  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.08         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.90/1.08          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.90/1.08          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.08  thf('7', plain,
% 0.90/1.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.90/1.08        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.08       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.90/1.08         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.90/1.08          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.90/1.08      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.90/1.08      inference('demod', [status(thm)], ['7', '10'])).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['4', '11'])).
% 0.90/1.08  thf(d3_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      (![X1 : $i, X3 : $i]:
% 0.90/1.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf(cc2_relset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.08         ((v5_relat_1 @ X14 @ X16)
% 0.90/1.08          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.90/1.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.90/1.08  thf('16', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.90/1.08      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.08  thf(d19_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ B ) =>
% 0.90/1.08       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      (![X10 : $i, X11 : $i]:
% 0.90/1.08         (~ (v5_relat_1 @ X10 @ X11)
% 0.90/1.08          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.90/1.08          | ~ (v1_relat_1 @ X10))),
% 0.90/1.08      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.90/1.08      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf(cc2_relat_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ A ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.90/1.08  thf('20', plain,
% 0.90/1.08      (![X8 : $i, X9 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.90/1.08          | (v1_relat_1 @ X8)
% 0.90/1.08          | ~ (v1_relat_1 @ X9))),
% 0.90/1.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.08  thf('21', plain,
% 0.90/1.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.90/1.08      inference('sup-', [status(thm)], ['19', '20'])).
% 0.90/1.08  thf(fc6_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.08  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.08  thf('24', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.90/1.08      inference('demod', [status(thm)], ['18', '23'])).
% 0.90/1.08  thf('25', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.08          | (r2_hidden @ X0 @ X2)
% 0.90/1.08          | ~ (r1_tarski @ X1 @ X2))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['24', '25'])).
% 0.90/1.08  thf('27', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.90/1.08          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D)) @ sk_B))),
% 0.90/1.08      inference('sup-', [status(thm)], ['13', '26'])).
% 0.90/1.08  thf('28', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('29', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.08          | (r2_hidden @ X0 @ X2)
% 0.90/1.08          | ~ (r1_tarski @ X1 @ X2))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('30', plain,
% 0.90/1.08      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.90/1.08      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.90/1.08          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D)) @ sk_C_1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['27', '30'])).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      (![X1 : $i, X3 : $i]:
% 0.90/1.08         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('33', plain,
% 0.90/1.08      (((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)
% 0.90/1.08        | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.08  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.90/1.08      inference('simplify', [status(thm)], ['33'])).
% 0.90/1.08  thf(t4_funct_2, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.08       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.90/1.08         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.90/1.08           ( m1_subset_1 @
% 0.90/1.08             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.90/1.08  thf('35', plain,
% 0.90/1.08      (![X28 : $i, X29 : $i]:
% 0.90/1.08         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.90/1.08          | (m1_subset_1 @ X28 @ 
% 0.90/1.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X28) @ X29)))
% 0.90/1.08          | ~ (v1_funct_1 @ X28)
% 0.90/1.08          | ~ (v1_relat_1 @ X28))),
% 0.90/1.08      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.90/1.08  thf('36', plain,
% 0.90/1.08      ((~ (v1_relat_1 @ sk_D)
% 0.90/1.08        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.08        | (m1_subset_1 @ sk_D @ 
% 0.90/1.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['34', '35'])).
% 0.90/1.08  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.08  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('39', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_D @ 
% 0.90/1.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))),
% 0.90/1.08      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.90/1.08  thf('40', plain,
% 0.90/1.08      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))
% 0.90/1.08        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['12', '39'])).
% 0.90/1.08  thf('41', plain,
% 0.90/1.08      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.08        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.90/1.08        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('42', plain,
% 0.90/1.08      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.90/1.08         <= (~
% 0.90/1.08             ((m1_subset_1 @ sk_D @ 
% 0.90/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.90/1.08      inference('split', [status(esa)], ['41'])).
% 0.90/1.08  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('44', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.90/1.08      inference('split', [status(esa)], ['41'])).
% 0.90/1.08  thf('45', plain, (((v1_funct_1 @ sk_D))),
% 0.90/1.08      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.08  thf('46', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('47', plain,
% 0.90/1.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('split', [status(esa)], ['46'])).
% 0.90/1.08  thf('48', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('49', plain,
% 0.90/1.08      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['47', '48'])).
% 0.90/1.08  thf('50', plain,
% 0.90/1.08      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.08         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.90/1.08          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.90/1.08          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.08  thf('51', plain,
% 0.90/1.08      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.90/1.08         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.08  thf('52', plain,
% 0.90/1.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('split', [status(esa)], ['46'])).
% 0.90/1.08  thf('53', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('54', plain,
% 0.90/1.08      (((m1_subset_1 @ sk_D @ 
% 0.90/1.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['52', '53'])).
% 0.90/1.08  thf('55', plain,
% 0.90/1.08      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.90/1.08         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.90/1.08          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.08  thf('56', plain,
% 0.90/1.08      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.08  thf('57', plain,
% 0.90/1.08      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.90/1.08         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('demod', [status(thm)], ['51', '56'])).
% 0.90/1.08  thf('58', plain,
% 0.90/1.08      (((m1_subset_1 @ sk_D @ 
% 0.90/1.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['52', '53'])).
% 0.90/1.08  thf('59', plain,
% 0.90/1.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.08         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.90/1.08          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.90/1.08          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.08  thf('60', plain,
% 0.90/1.08      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.90/1.08         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.08  thf('61', plain,
% 0.90/1.08      (![X20 : $i, X21 : $i]:
% 0.90/1.08         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('62', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.90/1.08      inference('simplify', [status(thm)], ['61'])).
% 0.90/1.08  thf('63', plain,
% 0.90/1.08      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('demod', [status(thm)], ['60', '62'])).
% 0.90/1.08  thf('64', plain,
% 0.90/1.08      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('demod', [status(thm)], ['57', '63'])).
% 0.90/1.08  thf('65', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_D @ 
% 0.90/1.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))),
% 0.90/1.08      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.90/1.08  thf('66', plain,
% 0.90/1.08      (((m1_subset_1 @ sk_D @ 
% 0.90/1.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['64', '65'])).
% 0.90/1.08  thf('67', plain,
% 0.90/1.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('split', [status(esa)], ['46'])).
% 0.90/1.08  thf('68', plain,
% 0.90/1.08      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.90/1.08         <= (~
% 0.90/1.08             ((m1_subset_1 @ sk_D @ 
% 0.90/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.90/1.08      inference('split', [status(esa)], ['41'])).
% 0.90/1.08  thf('69', plain,
% 0.90/1.08      ((~ (m1_subset_1 @ sk_D @ 
% 0.90/1.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.90/1.08         <= (~
% 0.90/1.08             ((m1_subset_1 @ sk_D @ 
% 0.90/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.90/1.08             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['67', '68'])).
% 0.90/1.08  thf('70', plain,
% 0.90/1.08      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.90/1.08       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['66', '69'])).
% 0.90/1.08  thf('71', plain,
% 0.90/1.08      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('demod', [status(thm)], ['57', '63'])).
% 0.90/1.08  thf('72', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.90/1.08      inference('simplify', [status(thm)], ['33'])).
% 0.90/1.08  thf('73', plain,
% 0.90/1.08      (![X28 : $i, X29 : $i]:
% 0.90/1.08         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.90/1.08          | (v1_funct_2 @ X28 @ (k1_relat_1 @ X28) @ X29)
% 0.90/1.08          | ~ (v1_funct_1 @ X28)
% 0.90/1.08          | ~ (v1_relat_1 @ X28))),
% 0.90/1.08      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.90/1.08  thf('74', plain,
% 0.90/1.08      ((~ (v1_relat_1 @ sk_D)
% 0.90/1.08        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.08        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['72', '73'])).
% 0.90/1.08  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.08  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('77', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1)),
% 0.90/1.08      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.90/1.08  thf('78', plain,
% 0.90/1.08      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.90/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['71', '77'])).
% 0.90/1.08  thf('79', plain,
% 0.90/1.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('split', [status(esa)], ['46'])).
% 0.90/1.08  thf('80', plain,
% 0.90/1.08      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.90/1.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.90/1.08      inference('split', [status(esa)], ['41'])).
% 0.90/1.08  thf('81', plain,
% 0.90/1.08      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.90/1.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.90/1.08             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['79', '80'])).
% 0.90/1.08  thf('82', plain,
% 0.90/1.08      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['78', '81'])).
% 0.90/1.08  thf('83', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.90/1.08      inference('split', [status(esa)], ['46'])).
% 0.90/1.08  thf('84', plain,
% 0.90/1.08      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['4', '11'])).
% 0.90/1.08  thf('85', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1)),
% 0.90/1.08      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.90/1.08  thf('86', plain,
% 0.90/1.08      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1) | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['84', '85'])).
% 0.90/1.08  thf('87', plain,
% 0.90/1.08      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.90/1.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.90/1.08      inference('split', [status(esa)], ['41'])).
% 0.90/1.08  thf('88', plain,
% 0.90/1.08      ((((sk_B) = (k1_xboole_0))) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['86', '87'])).
% 0.90/1.08  thf('89', plain,
% 0.90/1.08      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.90/1.08      inference('split', [status(esa)], ['46'])).
% 0.90/1.08  thf('90', plain,
% 0.90/1.08      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.90/1.08         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.90/1.08             ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['88', '89'])).
% 0.90/1.08  thf('91', plain,
% 0.90/1.08      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | (((sk_B) = (k1_xboole_0)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['90'])).
% 0.90/1.08  thf('92', plain,
% 0.90/1.08      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.90/1.08       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 0.90/1.08      inference('split', [status(esa)], ['41'])).
% 0.90/1.08  thf('93', plain,
% 0.90/1.08      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.90/1.08      inference('sat_resolution*', [status(thm)],
% 0.90/1.08                ['45', '70', '82', '83', '91', '92'])).
% 0.90/1.08  thf('94', plain,
% 0.90/1.08      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.90/1.08      inference('simpl_trail', [status(thm)], ['42', '93'])).
% 0.90/1.08  thf('95', plain, (((sk_B) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['40', '94'])).
% 0.90/1.08  thf('96', plain,
% 0.90/1.08      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.90/1.08      inference('split', [status(esa)], ['46'])).
% 0.90/1.08  thf('97', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.90/1.08      inference('sat_resolution*', [status(thm)],
% 0.90/1.08                ['45', '70', '82', '92', '83'])).
% 0.90/1.08  thf('98', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.08      inference('simpl_trail', [status(thm)], ['96', '97'])).
% 0.90/1.08  thf('99', plain, ($false),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['95', '98'])).
% 0.90/1.08  
% 0.90/1.08  % SZS output end Refutation
% 0.90/1.08  
% 0.90/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
