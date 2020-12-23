%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cuu0i3lCmG

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:08 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 334 expanded)
%              Number of leaves         :   44 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  730 (4110 expanded)
%              Number of equality atoms :   56 ( 211 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k11_relat_1 @ X21 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k11_relat_1 @ X10 @ X11 )
        = ( k9_relat_1 @ X10 @ ( k1_tarski @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
      = ( k11_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('41',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('43',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k11_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['34','43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','26','27','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X14 @ X15 ) @ ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('59',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['47','54','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cuu0i3lCmG
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 139 iterations in 0.150s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.38/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(t64_funct_2, conjecture,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.60         ( m1_subset_1 @
% 0.38/0.60           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.60       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.60         ( r1_tarski @
% 0.38/0.60           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.38/0.60           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.60            ( m1_subset_1 @
% 0.38/0.60              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.60          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.60            ( r1_tarski @
% 0.38/0.60              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.38/0.60              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (~ (r1_tarski @ 
% 0.38/0.60          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.38/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
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
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.60         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.38/0.60          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.38/0.60          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.38/0.60        | ((k1_tarski @ sk_A)
% 0.38/0.60            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.60  thf(zf_stmt_2, axiom,
% 0.38/0.60    (![B:$i,A:$i]:
% 0.38/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X32 : $i, X33 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_5, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.60         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.38/0.60          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.38/0.60          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.38/0.60        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      ((((sk_B) = (k1_xboole_0))
% 0.38/0.60        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['4', '7'])).
% 0.38/0.60  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.60         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.38/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.38/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.60  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (~ (r1_tarski @ 
% 0.38/0.60          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.38/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '14'])).
% 0.38/0.60  thf('16', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.38/0.60  thf(d1_tarski, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.60  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.60  thf('19', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.38/0.60      inference('sup+', [status(thm)], ['16', '18'])).
% 0.38/0.60  thf(t117_funct_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.60       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.60         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.38/0.60          | ((k11_relat_1 @ X21 @ X20) = (k1_tarski @ (k1_funct_1 @ X21 @ X20)))
% 0.38/0.60          | ~ (v1_funct_1 @ X21)
% 0.38/0.60          | ~ (v1_relat_1 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.38/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.38/0.60        | ((k11_relat_1 @ sk_D @ sk_A)
% 0.38/0.60            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.38/0.60          | (v1_relat_1 @ X8)
% 0.38/0.60          | ~ (v1_relat_1 @ X9))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.38/0.60        | (v1_relat_1 @ sk_D))),
% 0.38/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.60  thf(fc6_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.60  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('28', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.38/0.60  thf(d16_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i]:
% 0.38/0.60         (((k11_relat_1 @ X10 @ X11) = (k9_relat_1 @ X10 @ (k1_tarski @ X11)))
% 0.38/0.60          | ~ (v1_relat_1 @ X10))),
% 0.38/0.60      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k11_relat_1 @ X0 @ sk_A) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D)))
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.60  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf(t148_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X16 : $i, X17 : $i]:
% 0.38/0.60         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.38/0.60          | ~ (v1_relat_1 @ X16))),
% 0.38/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      ((((k2_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.38/0.60          = (k11_relat_1 @ sk_D @ sk_A))
% 0.38/0.60        | ~ (v1_relat_1 @ sk_D))),
% 0.38/0.60      inference('sup+', [status(thm)], ['30', '33'])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.60         ((v4_relat_1 @ X22 @ X23)
% 0.38/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.60  thf('37', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.60  thf(t209_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.38/0.60       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i]:
% 0.38/0.60         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.38/0.60          | ~ (v4_relat_1 @ X18 @ X19)
% 0.38/0.60          | ~ (v1_relat_1 @ X18))),
% 0.38/0.60      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.38/0.60        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.60  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('41', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.60  thf('42', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.38/0.60  thf('43', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.38/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.60  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('45', plain, (((k2_relat_1 @ sk_D) = (k11_relat_1 @ sk_D @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['34', '43', '44'])).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['21', '26', '27', '45'])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      (~ (r1_tarski @ 
% 0.38/0.60          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.38/0.60          (k2_relat_1 @ sk_D))),
% 0.38/0.60      inference('demod', [status(thm)], ['15', '46'])).
% 0.38/0.60  thf('48', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('49', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.38/0.60  thf('50', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.38/0.60  thf('51', plain,
% 0.38/0.60      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.38/0.60          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.38/0.60  thf('52', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.38/0.60           = (k9_relat_1 @ sk_D @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.60  thf('54', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.38/0.60           = (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.60  thf('55', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.60  thf(t147_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( r1_tarski @
% 0.38/0.60         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.38/0.60  thf('56', plain,
% 0.38/0.60      (![X14 : $i, X15 : $i]:
% 0.38/0.60         ((r1_tarski @ (k9_relat_1 @ X14 @ X15) @ 
% 0.38/0.60           (k9_relat_1 @ X14 @ (k1_relat_1 @ X14)))
% 0.38/0.60          | ~ (v1_relat_1 @ X14))),
% 0.38/0.60      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.38/0.60  thf('57', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.38/0.60           (k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.38/0.60          | ~ (v1_relat_1 @ sk_D))),
% 0.38/0.60      inference('sup+', [status(thm)], ['55', '56'])).
% 0.38/0.60  thf('58', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ sk_D @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.60  thf('59', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.38/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.60  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('61', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.38/0.60          (k2_relat_1 @ sk_D))),
% 0.38/0.60      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.38/0.60  thf('62', plain, ($false),
% 0.38/0.60      inference('demod', [status(thm)], ['47', '54', '61'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
