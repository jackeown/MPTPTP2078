%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JwLpALYDaz

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:30 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 160 expanded)
%              Number of leaves         :   44 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  673 (1642 expanded)
%              Number of equality atoms :   41 (  79 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ( X27
       != ( k2_relat_1 @ X25 ) )
      | ( r2_hidden @ ( sk_D_1 @ X28 @ X25 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X25: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( r2_hidden @ X28 @ ( k2_relat_1 @ X25 ) )
      | ( r2_hidden @ ( sk_D_1 @ X28 @ X25 ) @ ( k1_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
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

thf('9',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('12',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v5_relat_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ),
    inference(demod,[status(thm)],['19','24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['14','29'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( zip_tseitin_0 @ ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X3 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['13','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['10','42','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['22','23'])).

thf('49',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['7','46','47','48'])).

thf('50',plain,(
    ! [X48: $i] :
      ( ~ ( r2_hidden @ X48 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ X48 )
       != sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) )
 != sk_C_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('53',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ( X27
       != ( k2_relat_1 @ X25 ) )
      | ( X28
        = ( k1_funct_1 @ X25 @ ( sk_D_1 @ X28 @ X25 ) ) )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('54',plain,(
    ! [X25: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( r2_hidden @ X28 @ ( k2_relat_1 @ X25 ) )
      | ( X28
        = ( k1_funct_1 @ X25 @ ( sk_D_1 @ X28 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['22','23'])).

thf('58',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    sk_C_1 != sk_C_1 ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JwLpALYDaz
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:20:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 145 iterations in 0.148s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.60  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.38/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.60  thf(t17_funct_2, conjecture,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.38/0.60            ( ![E:$i]:
% 0.38/0.60              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.60            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.38/0.60               ( ![E:$i]:
% 0.38/0.60                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.38/0.60                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.60         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.38/0.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.60  thf('4', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.60  thf(d5_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.60               ( ?[D:$i]:
% 0.38/0.60                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.38/0.60                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.38/0.60         (((X27) != (k2_relat_1 @ X25))
% 0.38/0.60          | (r2_hidden @ (sk_D_1 @ X28 @ X25) @ (k1_relat_1 @ X25))
% 0.38/0.60          | ~ (r2_hidden @ X28 @ X27)
% 0.38/0.60          | ~ (v1_funct_1 @ X25)
% 0.38/0.60          | ~ (v1_relat_1 @ X25))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X25 : $i, X28 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X25)
% 0.38/0.60          | ~ (v1_funct_1 @ X25)
% 0.38/0.60          | ~ (r2_hidden @ X28 @ (k2_relat_1 @ X25))
% 0.38/0.60          | (r2_hidden @ (sk_D_1 @ X28 @ X25) @ (k1_relat_1 @ X25)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.38/0.60        | ~ (v1_funct_1 @ sk_D_2)
% 0.38/0.60        | ~ (v1_relat_1 @ sk_D_2))),
% 0.38/0.60      inference('sup-', [status(thm)], ['4', '6'])).
% 0.38/0.60  thf('8', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(d1_funct_2, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_1, axiom,
% 0.38/0.60    (![C:$i,B:$i,A:$i]:
% 0.38/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.38/0.60         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.38/0.60          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.38/0.60          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.38/0.60        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_4, axiom,
% 0.38/0.60    (![B:$i,A:$i]:
% 0.38/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.60  thf(zf_stmt_5, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.38/0.60         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.38/0.60          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.38/0.60          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.38/0.60        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.60  thf('14', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.60         ((v5_relat_1 @ X31 @ X33)
% 0.38/0.60          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.60  thf('17', plain, ((v5_relat_1 @ sk_D_2 @ sk_B)),
% 0.38/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf(d19_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i]:
% 0.38/0.60         (~ (v5_relat_1 @ X20 @ X21)
% 0.38/0.60          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.38/0.60          | ~ (v1_relat_1 @ X20))),
% 0.38/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.38/0.60          | (v1_relat_1 @ X18)
% 0.38/0.60          | ~ (v1_relat_1 @ X19))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.38/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.60  thf(fc6_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.60  thf('24', plain, ((v1_relat_1 @ sk_D_2)),
% 0.38/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.60  thf('25', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B)),
% 0.38/0.60      inference('demod', [status(thm)], ['19', '24'])).
% 0.38/0.60  thf(t3_subset, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (![X15 : $i, X17 : $i]:
% 0.38/0.60         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.60  thf(l3_subset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X10 @ X11)
% 0.38/0.60          | (r2_hidden @ X10 @ X12)
% 0.38/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.38/0.60      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.60  thf('30', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '29'])).
% 0.38/0.60  thf(t63_subset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.60       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k1_tarski @ X13) @ (k1_zfmisc_1 @ X14))
% 0.38/0.60          | ~ (r2_hidden @ X13 @ X14))),
% 0.38/0.60      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (![X15 : $i, X16 : $i]:
% 0.38/0.60         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('34', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.38/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.60  thf(t12_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.60  thf('36', plain, (((k2_xboole_0 @ (k1_tarski @ sk_C_1) @ sk_B) = (sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (![X40 : $i, X41 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.60  thf(t49_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k1_tarski @ X8) @ X9) != (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.60         (((k2_xboole_0 @ (k1_tarski @ X2) @ X1) != (X0))
% 0.38/0.60          | (zip_tseitin_0 @ X0 @ X3))),
% 0.38/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.60         (zip_tseitin_0 @ (k2_xboole_0 @ (k1_tarski @ X2) @ X1) @ X3)),
% 0.38/0.60      inference('simplify', [status(thm)], ['39'])).
% 0.38/0.60  thf('41', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.38/0.60      inference('sup+', [status(thm)], ['36', '40'])).
% 0.38/0.60  thf('42', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['13', '41'])).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('44', plain,
% 0.38/0.60      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.60         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.38/0.60          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.38/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.60  thf('46', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.38/0.60      inference('demod', [status(thm)], ['10', '42', '45'])).
% 0.38/0.60  thf('47', plain, ((v1_funct_1 @ sk_D_2)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('48', plain, ((v1_relat_1 @ sk_D_2)),
% 0.38/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.60  thf('49', plain, ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['7', '46', '47', '48'])).
% 0.38/0.60  thf('50', plain,
% 0.38/0.60      (![X48 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X48 @ sk_A)
% 0.38/0.60          | ((k1_funct_1 @ sk_D_2 @ X48) != (sk_C_1)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('51', plain,
% 0.38/0.60      (((k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)) != (sk_C_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.60  thf('52', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.38/0.60         (((X27) != (k2_relat_1 @ X25))
% 0.38/0.60          | ((X28) = (k1_funct_1 @ X25 @ (sk_D_1 @ X28 @ X25)))
% 0.38/0.60          | ~ (r2_hidden @ X28 @ X27)
% 0.38/0.60          | ~ (v1_funct_1 @ X25)
% 0.38/0.60          | ~ (v1_relat_1 @ X25))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.38/0.60  thf('54', plain,
% 0.38/0.60      (![X25 : $i, X28 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X25)
% 0.38/0.60          | ~ (v1_funct_1 @ X25)
% 0.38/0.60          | ~ (r2_hidden @ X28 @ (k2_relat_1 @ X25))
% 0.38/0.60          | ((X28) = (k1_funct_1 @ X25 @ (sk_D_1 @ X28 @ X25))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['53'])).
% 0.38/0.60  thf('55', plain,
% 0.38/0.60      ((((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))
% 0.38/0.60        | ~ (v1_funct_1 @ sk_D_2)
% 0.38/0.60        | ~ (v1_relat_1 @ sk_D_2))),
% 0.38/0.60      inference('sup-', [status(thm)], ['52', '54'])).
% 0.38/0.60  thf('56', plain, ((v1_funct_1 @ sk_D_2)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('57', plain, ((v1_relat_1 @ sk_D_2)),
% 0.38/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.60  thf('58', plain,
% 0.38/0.60      (((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))),
% 0.38/0.60      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.38/0.60  thf('59', plain, (((sk_C_1) != (sk_C_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['51', '58'])).
% 0.38/0.60  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
