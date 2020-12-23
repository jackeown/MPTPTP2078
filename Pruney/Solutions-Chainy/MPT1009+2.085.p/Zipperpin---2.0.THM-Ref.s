%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tBdF6YZpAB

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:00 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 313 expanded)
%              Number of leaves         :   47 ( 115 expanded)
%              Depth                    :   15
%              Number of atoms          :  829 (3922 expanded)
%              Number of equality atoms :   64 ( 219 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('2',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( r1_tarski @ X13 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) )
      | ( X13
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( r1_tarski @ ( k1_tarski @ X9 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k1_tarski @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( ( k11_relat_1 @ X25 @ X24 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k11_relat_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','32'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k11_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ X14 @ ( k1_tarski @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_tarski @ X0 ) ) )
        = ( k11_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_tarski @ X0 ) ) )
      = ( k11_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    = ( k11_relat_1 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('45',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('49',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('53',plain,(
    v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ~ ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('57',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k11_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['42','57'])).

thf('59',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('63',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['59','66','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tBdF6YZpAB
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 311 iterations in 0.222s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.68  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.68  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(t64_funct_2, conjecture,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.68         ( m1_subset_1 @
% 0.45/0.68           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.68       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.68         ( r1_tarski @
% 0.45/0.68           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.68           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.68            ( m1_subset_1 @
% 0.45/0.68              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.68          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.68            ( r1_tarski @
% 0.45/0.68              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.68              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      (~ (r1_tarski @ 
% 0.45/0.68          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.45/0.68          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('1', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(d1_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_1, axiom,
% 0.45/0.68    (![C:$i,B:$i,A:$i]:
% 0.45/0.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.68         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.45/0.68          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.45/0.68          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.68        | ((k1_tarski @ sk_A)
% 0.45/0.68            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.68  thf(zf_stmt_2, axiom,
% 0.45/0.68    (![B:$i,A:$i]:
% 0.45/0.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.68       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (![X36 : $i, X37 : $i]:
% 0.45/0.68         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.68  thf(zf_stmt_5, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.45/0.68         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.45/0.68          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.45/0.68          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.68        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      ((((sk_B) = (k1_xboole_0))
% 0.45/0.68        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['4', '7'])).
% 0.45/0.68  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.68         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.45/0.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.68  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (~ (r1_tarski @ 
% 0.45/0.68          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.45/0.68          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['0', '14'])).
% 0.45/0.68  thf('16', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.68  thf(t69_enumset1, axiom,
% 0.45/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.68  thf('17', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf(t70_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (![X1 : $i, X2 : $i]:
% 0.45/0.68         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.68  thf(t142_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.68       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.45/0.68            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.45/0.68            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.45/0.68            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.45/0.68            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.45/0.68            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.45/0.68  thf('19', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.45/0.68         ((r1_tarski @ X13 @ (k1_enumset1 @ X9 @ X10 @ X11))
% 0.45/0.68          | ((X13) != (k1_tarski @ X9)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (r1_tarski @ (k1_tarski @ X9) @ (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.45/0.68      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.68  thf(l1_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      (![X6 : $i, X7 : $i]:
% 0.45/0.68         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k1_tarski @ X6) @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['18', '22'])).
% 0.45/0.68  thf('24', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['17', '23'])).
% 0.45/0.68  thf('25', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '24'])).
% 0.45/0.68  thf(t117_funct_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.68       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.45/0.68         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      (![X24 : $i, X25 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.45/0.68          | ((k11_relat_1 @ X25 @ X24) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 0.45/0.68          | ~ (v1_funct_1 @ X25)
% 0.45/0.68          | ~ (v1_relat_1 @ X25))),
% 0.45/0.68      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_D)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_D)
% 0.45/0.68        | ((k11_relat_1 @ sk_D @ sk_A)
% 0.45/0.68            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc1_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( v1_relat_1 @ C ) ))).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.68         ((v1_relat_1 @ X26)
% 0.45/0.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.68  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (((k11_relat_1 @ sk_D @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (~ (r1_tarski @ 
% 0.45/0.68          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.45/0.68          (k11_relat_1 @ sk_D @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['15', '32'])).
% 0.45/0.68  thf('34', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.68  thf(d16_relat_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (![X14 : $i, X15 : $i]:
% 0.45/0.68         (((k11_relat_1 @ X14 @ X15) = (k9_relat_1 @ X14 @ (k1_tarski @ X15)))
% 0.45/0.68          | ~ (v1_relat_1 @ X14))),
% 0.45/0.68      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.45/0.68  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf(t148_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ B ) =>
% 0.45/0.68       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (![X20 : $i, X21 : $i]:
% 0.45/0.68         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 0.45/0.68          | ~ (v1_relat_1 @ X20))),
% 0.45/0.68      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf('39', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k2_relat_1 @ (k7_relat_1 @ sk_D @ (k1_tarski @ X0)))
% 0.45/0.68            = (k11_relat_1 @ sk_D @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ sk_D))),
% 0.45/0.68      inference('sup+', [status(thm)], ['35', '38'])).
% 0.45/0.68  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ (k1_tarski @ X0)))
% 0.45/0.68           = (k11_relat_1 @ sk_D @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (((k2_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.45/0.68         = (k11_relat_1 @ sk_D @ sk_A))),
% 0.45/0.68      inference('sup+', [status(thm)], ['34', '41'])).
% 0.45/0.68  thf('43', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.68  thf('44', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['17', '23'])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      (![X6 : $i, X8 : $i]:
% 0.45/0.68         ((r1_tarski @ (k1_tarski @ X6) @ X8) | ~ (r2_hidden @ X6 @ X8))),
% 0.45/0.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.68  thf('47', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('sup+', [status(thm)], ['43', '46'])).
% 0.45/0.68  thf('48', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.68  thf('49', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.68  thf(d18_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ B ) =>
% 0.45/0.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.68  thf('50', plain,
% 0.45/0.68      (![X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.45/0.68          | (v4_relat_1 @ X16 @ X17)
% 0.45/0.68          | ~ (v1_relat_1 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.68  thf('51', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.68  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('53', plain, ((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.68  thf(t209_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.68       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (![X22 : $i, X23 : $i]:
% 0.45/0.68         (((X22) = (k7_relat_1 @ X22 @ X23))
% 0.45/0.68          | ~ (v4_relat_1 @ X22 @ X23)
% 0.45/0.68          | ~ (v1_relat_1 @ X22))),
% 0.45/0.68      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_D)
% 0.45/0.68        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.68  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('57', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.45/0.68      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.68  thf('58', plain, (((k2_relat_1 @ sk_D) = (k11_relat_1 @ sk_D @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['42', '57'])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      (~ (r1_tarski @ 
% 0.45/0.68          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.45/0.68          (k2_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['33', '58'])).
% 0.45/0.68  thf('60', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('61', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.68  thf('62', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.68  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.68  thf('63', plain,
% 0.45/0.68      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.45/0.68          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.68  thf('64', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.45/0.68           = (k9_relat_1 @ sk_D @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.68  thf('65', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf('66', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.45/0.68           = (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.68  thf('67', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf(t144_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ B ) =>
% 0.45/0.68       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.45/0.68  thf('68', plain,
% 0.45/0.68      (![X18 : $i, X19 : $i]:
% 0.45/0.68         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ (k2_relat_1 @ X18))
% 0.45/0.68          | ~ (v1_relat_1 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.45/0.68  thf('69', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.45/0.68           (k2_relat_1 @ sk_D))
% 0.45/0.68          | ~ (v1_relat_1 @ sk_D))),
% 0.45/0.68      inference('sup+', [status(thm)], ['67', '68'])).
% 0.45/0.68  thf('70', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('71', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.45/0.68          (k2_relat_1 @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['69', '70'])).
% 0.45/0.68  thf('72', plain, ($false),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '66', '71'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
