%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KFYmrFlTut

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:15 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 296 expanded)
%              Number of leaves         :   45 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  793 (3281 expanded)
%              Number of equality atoms :   38 ( 132 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('15',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1 ),
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

thf('17',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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

thf('20',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['21','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['18','45','48'])).

thf('50',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['18','45','48'])).

thf('51',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['15','49','50'])).

thf('52',plain,(
    ! [X39: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('55',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('61',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['59','60'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X15 )
      | ( X16
        = ( k1_funct_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('65',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['18','45','48'])).

thf('68',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['53','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KFYmrFlTut
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:22:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 164 iterations in 0.178s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.65  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(t190_funct_2, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.65       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.46/0.65            ( ![E:$i]:
% 0.46/0.65              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.65            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.65          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.46/0.65               ( ![E:$i]:
% 0.46/0.65                 ( ( m1_subset_1 @ E @ B ) =>
% 0.46/0.65                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.65         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.46/0.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.65  thf(t146_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X13 : $i]:
% 0.46/0.65         (((k9_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (k2_relat_1 @ X13))
% 0.46/0.65          | ~ (v1_relat_1 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.46/0.65  thf(t143_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ C ) =>
% 0.46/0.65       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.46/0.65         ( ?[D:$i]:
% 0.46/0.65           ( ( r2_hidden @ D @ B ) & 
% 0.46/0.65             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.46/0.65             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.46/0.65          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ (k1_relat_1 @ X12))
% 0.46/0.65          | ~ (v1_relat_1 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.46/0.65             (k1_relat_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.65        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.46/0.65           (k1_relat_1 @ sk_D_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '8'])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(cc1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( v1_relat_1 @ C ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         ((v1_relat_1 @ X19)
% 0.46/0.65          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.65  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.46/0.65        (k1_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '12'])).
% 0.46/0.65  thf(t1_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_subset])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      ((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.46/0.65        (k1_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf('16', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d1_funct_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_1, axiom,
% 0.46/0.65    (![C:$i,B:$i,A:$i]:
% 0.46/0.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.46/0.65         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.46/0.65          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.46/0.65          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)
% 0.46/0.65        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.65  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.65  thf(zf_stmt_4, axiom,
% 0.46/0.65    (![B:$i,A:$i]:
% 0.46/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.65  thf(zf_stmt_5, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.65         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.46/0.65          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.46/0.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (((zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)
% 0.46/0.65        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X31 : $i, X32 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.65  thf('23', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.46/0.65      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.65  thf(d3_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X1 : $i, X3 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(cc2_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.65         ((v5_relat_1 @ X22 @ X24)
% 0.46/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.65  thf('28', plain, ((v5_relat_1 @ sk_D_1 @ sk_C_1)),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf(d19_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ B ) =>
% 0.46/0.65       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (v5_relat_1 @ X7 @ X8)
% 0.46/0.65          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.46/0.65          | ~ (v1_relat_1 @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C_1)),
% 0.46/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.65          | (r2_hidden @ X0 @ X2)
% 0.46/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ sk_C_1)
% 0.46/0.65          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0)
% 0.46/0.65          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D_1)) @ sk_C_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '34'])).
% 0.46/0.65  thf(t7_ordinal1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0)
% 0.46/0.65          | ~ (r1_tarski @ sk_C_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_D_1))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ sk_C_1 @ X1)
% 0.46/0.65          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['24', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('43', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.46/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf('44', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 0.46/0.65      inference('sup-', [status(thm)], ['38', '43'])).
% 0.46/0.65  thf('45', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)),
% 0.46/0.65      inference('demod', [status(thm)], ['21', '44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.46/0.65          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (((k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.65  thf('49', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['18', '45', '48'])).
% 0.46/0.65  thf('50', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['18', '45', '48'])).
% 0.46/0.65  thf('51', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_B)),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '49', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X39 : $i]:
% 0.46/0.65         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X39))
% 0.46/0.65          | ~ (m1_subset_1 @ X39 @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.65  thf('54', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X13 : $i]:
% 0.46/0.65         (((k9_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (k2_relat_1 @ X13))
% 0.46/0.65          | ~ (v1_relat_1 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X10 @ X11) @ X11) @ X12)
% 0.46/0.65          | ~ (v1_relat_1 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r2_hidden @ 
% 0.46/0.65           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.65        | (r2_hidden @ 
% 0.46/0.65           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.46/0.65           sk_D_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['54', '58'])).
% 0.46/0.65  thf('60', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      ((r2_hidden @ 
% 0.46/0.65        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.46/0.65        sk_D_1)),
% 0.46/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.65  thf(t8_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.46/0.65         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.65           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X15)
% 0.46/0.65          | ((X16) = (k1_funct_1 @ X15 @ X14))
% 0.46/0.65          | ~ (v1_funct_1 @ X15)
% 0.46/0.65          | ~ (v1_relat_1 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_D_1)
% 0.46/0.65        | ((sk_A)
% 0.46/0.65            = (k1_funct_1 @ sk_D_1 @ 
% 0.46/0.65               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.65  thf('64', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('65', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (((sk_A)
% 0.46/0.65         = (k1_funct_1 @ sk_D_1 @ 
% 0.46/0.65            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.46/0.65  thf('67', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['18', '45', '48'])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.65  thf('69', plain, (((sk_A) != (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['53', '68'])).
% 0.46/0.65  thf('70', plain, ($false), inference('simplify', [status(thm)], ['69'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
