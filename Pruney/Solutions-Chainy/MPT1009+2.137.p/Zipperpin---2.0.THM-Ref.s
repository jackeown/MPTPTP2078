%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DzhCah5p0M

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 340 expanded)
%              Number of leaves         :   46 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  775 (4155 expanded)
%              Number of equality atoms :   61 ( 216 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) )
        = X10 )
      | ( r2_hidden @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 != X6 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X6 ) )
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('19',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X6 ) )
     != ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( ( k11_relat_1 @ X25 @ X24 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k11_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ X14 @ ( k1_tarski @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_tarski @ X0 ) ) )
        = ( k11_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_tarski @ X0 ) ) )
      = ( k11_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    = ( k11_relat_1 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ~ ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('46',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('48',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k11_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','29','30','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('55',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k9_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('63',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['51','58','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DzhCah5p0M
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:38:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 192 iterations in 0.134s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.56  thf(t64_funct_2, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.56         ( m1_subset_1 @
% 0.21/0.56           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.56         ( r1_tarski @
% 0.21/0.56           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.21/0.56           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.56            ( m1_subset_1 @
% 0.21/0.56              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.56          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.56            ( r1_tarski @
% 0.21/0.56              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.21/0.56              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (~ (r1_tarski @ 
% 0.21/0.56          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.21/0.56          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d1_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_1, axiom,
% 0.21/0.56    (![C:$i,B:$i,A:$i]:
% 0.21/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.56         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.21/0.56          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.21/0.56          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.56        | ((k1_tarski @ sk_A)
% 0.21/0.56            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf(zf_stmt_2, axiom,
% 0.21/0.56    (![B:$i,A:$i]:
% 0.21/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X36 : $i, X37 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_5, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.56         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.21/0.56          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.21/0.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.56        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      ((((sk_B) = (k1_xboole_0))
% 0.21/0.56        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.56  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.56         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.21/0.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.56  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (~ (r1_tarski @ 
% 0.21/0.56          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.21/0.56          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.56  thf('16', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.21/0.56  thf(t65_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.56       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X10 @ (k1_tarski @ X11)) = (X10))
% 0.21/0.56          | (r2_hidden @ X11 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.56  thf(t20_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.56         ( k1_tarski @ A ) ) <=>
% 0.21/0.56       ( ( A ) != ( B ) ) ))).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i]:
% 0.21/0.56         (((X7) != (X6))
% 0.21/0.56          | ((k4_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X6))
% 0.21/0.56              != (k1_tarski @ X7)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X6 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X6))
% 0.21/0.56           != (k1_tarski @ X6))),
% 0.21/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.56          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.56  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.56  thf('22', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('sup+', [status(thm)], ['16', '21'])).
% 0.21/0.56  thf(t117_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.56         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.21/0.56          | ((k11_relat_1 @ X25 @ X24) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 0.21/0.56          | ~ (v1_funct_1 @ X25)
% 0.21/0.56          | ~ (v1_relat_1 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.56        | ((k11_relat_1 @ sk_D @ sk_A)
% 0.21/0.56            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc2_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.21/0.56          | (v1_relat_1 @ X12)
% 0.21/0.56          | ~ (v1_relat_1 @ X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.21/0.56        | (v1_relat_1 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf(fc6_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.56  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('31', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.21/0.56  thf(d16_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i]:
% 0.21/0.56         (((k11_relat_1 @ X14 @ X15) = (k9_relat_1 @ X14 @ (k1_tarski @ X15)))
% 0.21/0.56          | ~ (v1_relat_1 @ X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.21/0.56  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf(t148_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i]:
% 0.21/0.56         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 0.21/0.56          | ~ (v1_relat_1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_relat_1 @ (k7_relat_1 @ sk_D @ (k1_tarski @ X0)))
% 0.21/0.56            = (k11_relat_1 @ sk_D @ X0))
% 0.21/0.56          | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.56      inference('sup+', [status(thm)], ['32', '35'])).
% 0.21/0.56  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ (k1_tarski @ X0)))
% 0.21/0.56           = (k11_relat_1 @ sk_D @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (((k2_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.21/0.56         = (k11_relat_1 @ sk_D @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['31', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc2_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.56         ((v4_relat_1 @ X26 @ X27)
% 0.21/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.56  thf('42', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.56  thf(t209_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.56       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X22 : $i, X23 : $i]:
% 0.21/0.56         (((X22) = (k7_relat_1 @ X22 @ X23))
% 0.21/0.56          | ~ (v4_relat_1 @ X22 @ X23)
% 0.21/0.56          | ~ (v1_relat_1 @ X22))),
% 0.21/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.56        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf('46', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.56  thf('47', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.21/0.56  thf('48', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.21/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('49', plain, (((k2_relat_1 @ sk_D) = (k11_relat_1 @ sk_D @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['39', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['24', '29', '30', '49'])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (~ (r1_tarski @ 
% 0.21/0.56          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.21/0.56          (k2_relat_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '50'])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.21/0.56          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.21/0.56           = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.21/0.56           = (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf(t147_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( r1_tarski @
% 0.21/0.56         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ 
% 0.21/0.56           (k9_relat_1 @ X18 @ (k1_relat_1 @ X18)))
% 0.21/0.56          | ~ (v1_relat_1 @ X18))),
% 0.21/0.56      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.21/0.56           (k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.21/0.56          | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.56      inference('sup+', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('63', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.21/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.21/0.56          (k2_relat_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.21/0.56  thf('66', plain, ($false),
% 0.21/0.56      inference('demod', [status(thm)], ['51', '58', '65'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
