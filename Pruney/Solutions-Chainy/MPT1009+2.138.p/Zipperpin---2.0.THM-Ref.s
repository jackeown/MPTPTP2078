%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nz83ZRjCV0

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:08 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 239 expanded)
%              Number of leaves         :   42 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  620 (2285 expanded)
%              Number of equality atoms :   43 ( 113 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k9_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X30 @ X31 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v4_relat_1 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16
        = ( k1_tarski @ X15 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relat_1 @ X34 )
       != ( k1_tarski @ X33 ) )
      | ( ( k2_relat_1 @ X34 )
        = ( k1_tarski @ ( k1_funct_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X32: $i] :
      ( ( ( k1_relat_1 @ X32 )
       != k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X27: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X27 ) )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X30 @ X31 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('48',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ X24 )
      | ( r2_hidden @ ( sk_B_1 @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('49',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','51'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('59',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('63',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['4','34','61','62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nz83ZRjCV0
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 237 iterations in 0.164s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.42/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.42/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.62  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.42/0.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(t64_funct_2, conjecture,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.62         ( m1_subset_1 @
% 0.42/0.62           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62         ( r1_tarski @
% 0.42/0.62           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.42/0.62           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.62            ( m1_subset_1 @
% 0.42/0.62              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.62          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62            ( r1_tarski @
% 0.42/0.62              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.42/0.62              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (~ (r1_tarski @ 
% 0.42/0.62          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_D_1 @ sk_C_2) @ 
% 0.42/0.62          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(redefinition_k7_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.42/0.62          | ((k7_relset_1 @ X41 @ X42 @ X40 @ X43) = (k9_relat_1 @ X40 @ X43)))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_D_1 @ X0)
% 0.42/0.62           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_2) @ 
% 0.42/0.62          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.62  thf(t144_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X30 : $i, X31 : $i]:
% 0.42/0.62         ((r1_tarski @ (k9_relat_1 @ X30 @ X31) @ (k2_relat_1 @ X30))
% 0.42/0.62          | ~ (v1_relat_1 @ X30))),
% 0.42/0.62      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc2_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.42/0.62         ((v4_relat_1 @ X37 @ X38)
% 0.42/0.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.62  thf('8', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.62  thf(d18_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i]:
% 0.42/0.62         (~ (v4_relat_1 @ X20 @ X21)
% 0.42/0.62          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.42/0.62          | ~ (v1_relat_1 @ X20))),
% 0.42/0.62      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_D_1)
% 0.42/0.62        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc2_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.42/0.62          | (v1_relat_1 @ X18)
% 0.42/0.62          | ~ (v1_relat_1 @ X19))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.42/0.62        | (v1_relat_1 @ sk_D_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.62  thf(fc6_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.62  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.42/0.62  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['10', '15'])).
% 0.42/0.62  thf(l3_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.42/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]:
% 0.42/0.62         (((X16) = (k1_tarski @ X15))
% 0.42/0.62          | ((X16) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_tarski @ X16 @ (k1_tarski @ X15)))),
% 0.42/0.62      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.42/0.62        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.62  thf(t14_funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.42/0.62         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X33 : $i, X34 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X34) != (k1_tarski @ X33))
% 0.42/0.62          | ((k2_relat_1 @ X34) = (k1_tarski @ (k1_funct_1 @ X34 @ X33)))
% 0.42/0.62          | ~ (v1_funct_1 @ X34)
% 0.42/0.62          | ~ (v1_relat_1 @ X34))),
% 0.42/0.62      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_1))
% 0.42/0.62          | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_D_1)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_D_1)
% 0.42/0.62        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('eq_res', [status(thm)], ['20'])).
% 0.42/0.62  thf('22', plain, ((v1_funct_1 @ sk_D_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.42/0.62        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_2) @ 
% 0.42/0.62          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_2) @ (k2_relat_1 @ sk_D_1))
% 0.42/0.62        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['5', '26'])).
% 0.42/0.62  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.42/0.62  thf('29', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.42/0.62  thf(t64_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.62         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X32 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X32) != (k1_xboole_0))
% 0.42/0.62          | ((X32) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ X32))),
% 0.42/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62        | ~ (v1_relat_1 @ sk_D_1)
% 0.42/0.62        | ((sk_D_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.62  thf('32', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf('34', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['33'])).
% 0.42/0.62  thf(d1_xboole_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.62  thf('36', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf(t7_ordinal1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X35 : $i, X36 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.62  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['36', '39'])).
% 0.42/0.62  thf(fc11_relat_1, axiom,
% 0.42/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (![X27 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ (k2_relat_1 @ X27)) | ~ (v1_xboole_0 @ X27))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.42/0.62  thf(l13_xboole_0, axiom,
% 0.42/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.42/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.62  thf('44', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['40', '43'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (![X30 : $i, X31 : $i]:
% 0.42/0.62         ((r1_tarski @ (k9_relat_1 @ X30 @ X31) @ (k2_relat_1 @ X30))
% 0.42/0.62          | ~ (v1_relat_1 @ X30))),
% 0.42/0.62      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.42/0.62          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['44', '45'])).
% 0.42/0.62  thf('47', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.62  thf(d1_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) <=>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ~( ( r2_hidden @ B @ A ) & 
% 0.42/0.62              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (![X24 : $i]: ((v1_relat_1 @ X24) | (r2_hidden @ (sk_B_1 @ X24) @ X24))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      (![X35 : $i, X36 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (r1_tarski @ X0 @ (sk_B_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.42/0.62  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['47', '50'])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.42/0.62      inference('demod', [status(thm)], ['46', '51'])).
% 0.42/0.62  thf(d3_tarski, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X3 @ X4)
% 0.42/0.62          | (r2_hidden @ X3 @ X5)
% 0.42/0.62          | ~ (r1_tarski @ X4 @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r2_hidden @ X1 @ k1_xboole_0)
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ k1_xboole_0 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.42/0.62          | (r2_hidden @ (sk_B @ (k9_relat_1 @ k1_xboole_0 @ X0)) @ k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['35', '54'])).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.42/0.62          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.62  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['36', '39'])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      (![X0 : $i]: (v1_xboole_0 @ (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['57', '58'])).
% 0.42/0.62  thf('60', plain,
% 0.42/0.62      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.42/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['59', '60'])).
% 0.42/0.62  thf('62', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['33'])).
% 0.42/0.62  thf('63', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.62  thf('64', plain, ($false),
% 0.42/0.62      inference('demod', [status(thm)], ['4', '34', '61', '62', '63'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
