%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c3vcFXQkJY

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:08 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 144 expanded)
%              Number of leaves         :   41 (  63 expanded)
%              Depth                    :   21
%              Number of atoms          :  701 (1442 expanded)
%              Number of equality atoms :   40 (  62 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k7_relset_1 @ X43 @ X44 @ X42 @ X45 )
        = ( k9_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X20 @ X21 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v4_relat_1 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('12',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relat_1 @ X36 )
       != ( k1_tarski @ X35 ) )
      | ( ( k2_relat_1 @ X36 )
        = ( k1_tarski @ ( k1_funct_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( sk_D @ X27 @ X28 @ X29 ) @ X27 )
      | ( zip_tseitin_0 @ ( sk_E @ X27 @ X28 @ X29 ) @ ( sk_D @ X27 @ X28 @ X29 ) @ X28 @ X29 )
      | ( X27
        = ( k9_relat_1 @ X29 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ ( k1_relat_1 @ X22 ) )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ X1 @ X0 @ sk_D_1 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_D_1 ) @ X1 )
      | ( X1
        = ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ X1 @ X0 @ sk_D_1 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_D_1 ) @ X1 )
      | ( X1
        = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('43',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_D_1 ) @ X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_E @ X1 @ X0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_D_1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ sk_D_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ k1_xboole_0 @ X1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','52'])).

thf('54',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c3vcFXQkJY
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.63  % Solved by: fo/fo7.sh
% 0.47/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.63  % done 418 iterations in 0.176s
% 0.47/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.63  % SZS output start Refutation
% 0.47/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.47/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.63  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.47/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.63  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.47/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.63  thf(t64_funct_2, conjecture,
% 0.47/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.63         ( m1_subset_1 @
% 0.47/0.63           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.63       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.63         ( r1_tarski @
% 0.47/0.63           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.63           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.63            ( m1_subset_1 @
% 0.47/0.63              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.63          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.63            ( r1_tarski @
% 0.47/0.63              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.63              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.47/0.63    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.47/0.63  thf('0', plain,
% 0.47/0.63      (~ (r1_tarski @ 
% 0.47/0.63          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C_1) @ 
% 0.47/0.63          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('1', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(redefinition_k7_relset_1, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.63       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.47/0.63  thf('2', plain,
% 0.47/0.63      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.47/0.63          | ((k7_relset_1 @ X43 @ X44 @ X42 @ X45) = (k9_relat_1 @ X42 @ X45)))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.63  thf('3', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.47/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.63  thf('4', plain,
% 0.47/0.63      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_1) @ 
% 0.47/0.63          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.63  thf(d3_tarski, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.63  thf('5', plain,
% 0.47/0.63      (![X1 : $i, X3 : $i]:
% 0.47/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.63  thf('6', plain,
% 0.47/0.63      (![X1 : $i, X3 : $i]:
% 0.47/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.63  thf('7', plain,
% 0.47/0.63      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.63  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.63      inference('simplify', [status(thm)], ['7'])).
% 0.47/0.63  thf(t144_relat_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ B ) =>
% 0.47/0.63       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.47/0.63  thf('9', plain,
% 0.47/0.63      (![X20 : $i, X21 : $i]:
% 0.47/0.63         ((r1_tarski @ (k9_relat_1 @ X20 @ X21) @ (k2_relat_1 @ X20))
% 0.47/0.63          | ~ (v1_relat_1 @ X20))),
% 0.47/0.63      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.47/0.63  thf('10', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(cc2_relset_1, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.63  thf('11', plain,
% 0.47/0.63      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.47/0.63         ((v4_relat_1 @ X39 @ X40)
% 0.47/0.63          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.47/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.63  thf('12', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.63  thf(d18_relat_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ B ) =>
% 0.47/0.63       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.63  thf('13', plain,
% 0.47/0.63      (![X16 : $i, X17 : $i]:
% 0.47/0.63         (~ (v4_relat_1 @ X16 @ X17)
% 0.47/0.63          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.47/0.63          | ~ (v1_relat_1 @ X16))),
% 0.47/0.63      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.63  thf('14', plain,
% 0.47/0.63      ((~ (v1_relat_1 @ sk_D_1)
% 0.47/0.63        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.63  thf('15', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(cc2_relat_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ A ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.63  thf('16', plain,
% 0.47/0.63      (![X14 : $i, X15 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.47/0.63          | (v1_relat_1 @ X14)
% 0.47/0.63          | ~ (v1_relat_1 @ X15))),
% 0.47/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.63  thf('17', plain,
% 0.47/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.47/0.63        | (v1_relat_1 @ sk_D_1))),
% 0.47/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.63  thf(fc6_relat_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.63  thf('18', plain,
% 0.47/0.63      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.63  thf('19', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.63  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['14', '19'])).
% 0.47/0.63  thf(l3_zfmisc_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.47/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      (![X11 : $i, X12 : $i]:
% 0.47/0.63         (((X12) = (k1_tarski @ X11))
% 0.47/0.63          | ((X12) = (k1_xboole_0))
% 0.47/0.63          | ~ (r1_tarski @ X12 @ (k1_tarski @ X11)))),
% 0.47/0.63      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.47/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.63  thf(t14_funct_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.63       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.47/0.63         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.47/0.63  thf('23', plain,
% 0.47/0.63      (![X35 : $i, X36 : $i]:
% 0.47/0.63         (((k1_relat_1 @ X36) != (k1_tarski @ X35))
% 0.47/0.63          | ((k2_relat_1 @ X36) = (k1_tarski @ (k1_funct_1 @ X36 @ X35)))
% 0.47/0.63          | ~ (v1_funct_1 @ X36)
% 0.47/0.63          | ~ (v1_relat_1 @ X36))),
% 0.47/0.63      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.47/0.63  thf('24', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_1))
% 0.47/0.63          | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.47/0.63          | ~ (v1_relat_1 @ X0)
% 0.47/0.63          | ~ (v1_funct_1 @ X0)
% 0.47/0.63          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.63  thf('25', plain,
% 0.47/0.63      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.47/0.63        | ~ (v1_funct_1 @ sk_D_1)
% 0.47/0.63        | ~ (v1_relat_1 @ sk_D_1)
% 0.47/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('eq_res', [status(thm)], ['24'])).
% 0.47/0.63  thf('26', plain, ((v1_funct_1 @ sk_D_1)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.63  thf('28', plain,
% 0.47/0.63      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.47/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.47/0.63  thf('29', plain,
% 0.47/0.63      (~ (r1_tarski @ 
% 0.47/0.63          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C_1) @ 
% 0.47/0.63          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      ((~ (r1_tarski @ 
% 0.47/0.63           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C_1) @ 
% 0.47/0.63           (k2_relat_1 @ sk_D_1))
% 0.47/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.63  thf('31', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.47/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.63  thf('32', plain,
% 0.47/0.63      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_1) @ (k2_relat_1 @ sk_D_1))
% 0.47/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.63  thf('33', plain,
% 0.47/0.63      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['9', '32'])).
% 0.47/0.63  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.63  thf('35', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.47/0.63      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.63  thf(d12_funct_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.47/0.63       ( ![B:$i,C:$i]:
% 0.47/0.63         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.47/0.63           ( ![D:$i]:
% 0.47/0.63             ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.63               ( ?[E:$i]:
% 0.47/0.63                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.47/0.63                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.47/0.63  thf(zf_stmt_2, axiom,
% 0.47/0.63    (![E:$i,D:$i,B:$i,A:$i]:
% 0.47/0.63     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.47/0.63       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.47/0.63         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_3, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.63       ( ![B:$i,C:$i]:
% 0.47/0.63         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.47/0.63           ( ![D:$i]:
% 0.47/0.63             ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.63               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.47/0.63  thf('36', plain,
% 0.47/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.63         ((r2_hidden @ (sk_D @ X27 @ X28 @ X29) @ X27)
% 0.47/0.63          | (zip_tseitin_0 @ (sk_E @ X27 @ X28 @ X29) @ 
% 0.47/0.63             (sk_D @ X27 @ X28 @ X29) @ X28 @ X29)
% 0.47/0.63          | ((X27) = (k9_relat_1 @ X29 @ X28))
% 0.47/0.63          | ~ (v1_funct_1 @ X29)
% 0.47/0.63          | ~ (v1_relat_1 @ X29))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.63  thf('37', plain,
% 0.47/0.63      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.63         ((r2_hidden @ X23 @ (k1_relat_1 @ X22))
% 0.47/0.63          | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.63  thf('38', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.63         (~ (v1_relat_1 @ X0)
% 0.47/0.63          | ~ (v1_funct_1 @ X0)
% 0.47/0.63          | ((X2) = (k9_relat_1 @ X0 @ X1))
% 0.47/0.63          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.47/0.63          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.63  thf('39', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         ((r2_hidden @ (sk_E @ X1 @ X0 @ sk_D_1) @ k1_xboole_0)
% 0.47/0.63          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_D_1) @ X1)
% 0.47/0.63          | ((X1) = (k9_relat_1 @ sk_D_1 @ X0))
% 0.47/0.63          | ~ (v1_funct_1 @ sk_D_1)
% 0.47/0.63          | ~ (v1_relat_1 @ sk_D_1))),
% 0.47/0.63      inference('sup+', [status(thm)], ['35', '38'])).
% 0.47/0.63  thf('40', plain, ((v1_funct_1 @ sk_D_1)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('41', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.63  thf('42', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         ((r2_hidden @ (sk_E @ X1 @ X0 @ sk_D_1) @ k1_xboole_0)
% 0.47/0.63          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_D_1) @ X1)
% 0.47/0.63          | ((X1) = (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.47/0.63      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.47/0.63  thf(t7_ordinal1, axiom,
% 0.47/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.63  thf('43', plain,
% 0.47/0.63      (![X37 : $i, X38 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X37 @ X38) | ~ (r1_tarski @ X38 @ X37))),
% 0.47/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.47/0.63  thf('44', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (((X1) = (k9_relat_1 @ sk_D_1 @ X0))
% 0.47/0.63          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_D_1) @ X1)
% 0.47/0.63          | ~ (r1_tarski @ k1_xboole_0 @ (sk_E @ X1 @ X0 @ sk_D_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.63  thf('45', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.47/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.63  thf('46', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (((X1) = (k9_relat_1 @ sk_D_1 @ X0))
% 0.47/0.63          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_D_1) @ X1))),
% 0.47/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.47/0.63  thf('47', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.47/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.63  thf('48', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.63          | (r2_hidden @ X0 @ X2)
% 0.47/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.63  thf('49', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.63  thf('50', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (((k1_xboole_0) = (k9_relat_1 @ sk_D_1 @ X0))
% 0.47/0.63          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_D_1) @ X1))),
% 0.47/0.63      inference('sup-', [status(thm)], ['46', '49'])).
% 0.47/0.63  thf('51', plain,
% 0.47/0.63      (![X37 : $i, X38 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X37 @ X38) | ~ (r1_tarski @ X38 @ X37))),
% 0.47/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.47/0.63  thf('52', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (((k1_xboole_0) = (k9_relat_1 @ sk_D_1 @ X1))
% 0.47/0.63          | ~ (r1_tarski @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ sk_D_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.63  thf('53', plain, (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['8', '52'])).
% 0.47/0.63  thf('54', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.47/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.63  thf('55', plain, ($false),
% 0.47/0.63      inference('demod', [status(thm)], ['4', '53', '54'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
