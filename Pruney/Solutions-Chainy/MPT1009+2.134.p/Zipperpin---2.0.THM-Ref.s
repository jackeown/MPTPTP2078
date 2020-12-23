%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zm0zQEmVic

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:08 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 320 expanded)
%              Number of leaves         :   43 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  718 (3246 expanded)
%              Number of equality atoms :   68 ( 176 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k7_relset_1 @ X44 @ X45 @ X43 @ X46 )
        = ( k9_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X31 @ X32 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v4_relat_1 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( v4_relat_1 @ X27 @ X28 )
      | ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k1_tarski @ X13 ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('21',plain,(
    ! [X1: $i,X4: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X4 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k1_relat_1 @ X39 ) )
      | ( ( k11_relat_1 @ X39 @ X38 )
        = ( k1_tarski @ ( k1_funct_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('27',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k11_relat_1 @ X25 @ X26 )
        = ( k9_relat_1 @ X25 @ ( k1_tarski @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('29',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35
        = ( k7_relat_1 @ X35 @ X36 ) )
      | ~ ( v4_relat_1 @ X35 @ X36 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('33',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k9_relat_1 @ X33 @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k11_relat_1 @ sk_D_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k11_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','40'])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X37: $i] :
      ( ( ( k1_relat_1 @ X37 )
       != k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('54',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('55',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v4_relat_1 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35
        = ( k7_relat_1 @ X35 @ X36 ) )
      | ~ ( v4_relat_1 @ X35 @ X36 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_zfmisc_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('60',plain,(
    ! [X18: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X29: $i,X30: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('62',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','62'])).

thf('64',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k9_relat_1 @ X33 @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('66',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['60','61'])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53','68','69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zm0zQEmVic
% 0.10/0.31  % Computer   : n003.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 20:31:42 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running portfolio for 600 s
% 0.10/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.10/0.32  % Number of cores: 8
% 0.10/0.32  % Python version: Python 3.6.8
% 0.10/0.32  % Running in FO mode
% 0.17/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.17/0.48  % Solved by: fo/fo7.sh
% 0.17/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.48  % done 174 iterations in 0.061s
% 0.17/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.17/0.48  % SZS output start Refutation
% 0.17/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.17/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.17/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.17/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.17/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.17/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.17/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.17/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.17/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.17/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.17/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.17/0.48  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.17/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.17/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.17/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.17/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.17/0.48  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.17/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.17/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.17/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.17/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.17/0.48  thf(t64_funct_2, conjecture,
% 0.17/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.17/0.48         ( m1_subset_1 @
% 0.17/0.48           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.17/0.48       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.17/0.48         ( r1_tarski @
% 0.17/0.48           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.17/0.48           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.17/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.48        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.17/0.48            ( m1_subset_1 @
% 0.17/0.48              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.17/0.48          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.17/0.48            ( r1_tarski @
% 0.17/0.48              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.17/0.48              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.17/0.48    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.17/0.48  thf('0', plain,
% 0.17/0.48      (~ (r1_tarski @ 
% 0.17/0.48          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.17/0.48          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.17/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.48  thf('1', plain,
% 0.17/0.48      ((m1_subset_1 @ sk_D_1 @ 
% 0.17/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.17/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.48  thf(redefinition_k7_relset_1, axiom,
% 0.17/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.17/0.48       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.17/0.48  thf('2', plain,
% 0.17/0.48      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.17/0.48         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.17/0.48          | ((k7_relset_1 @ X44 @ X45 @ X43 @ X46) = (k9_relat_1 @ X43 @ X46)))),
% 0.17/0.48      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.17/0.48  thf('3', plain,
% 0.17/0.48      (![X0 : $i]:
% 0.17/0.48         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.17/0.48           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.17/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.48  thf('4', plain,
% 0.17/0.48      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.17/0.48          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.17/0.48      inference('demod', [status(thm)], ['0', '3'])).
% 0.17/0.48  thf(t144_relat_1, axiom,
% 0.17/0.48    (![A:$i,B:$i]:
% 0.17/0.48     ( ( v1_relat_1 @ B ) =>
% 0.17/0.48       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.17/0.48  thf('5', plain,
% 0.17/0.48      (![X31 : $i, X32 : $i]:
% 0.17/0.48         ((r1_tarski @ (k9_relat_1 @ X31 @ X32) @ (k2_relat_1 @ X31))
% 0.17/0.48          | ~ (v1_relat_1 @ X31))),
% 0.17/0.48      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.17/0.48  thf('6', plain,
% 0.17/0.48      ((m1_subset_1 @ sk_D_1 @ 
% 0.17/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.17/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf(cc2_relset_1, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i]:
% 0.17/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.17/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.17/0.49  thf('7', plain,
% 0.17/0.49      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.17/0.49         ((v4_relat_1 @ X40 @ X41)
% 0.17/0.49          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.17/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.17/0.49  thf('8', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.17/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.17/0.49  thf(d18_relat_1, axiom,
% 0.17/0.49    (![A:$i,B:$i]:
% 0.17/0.49     ( ( v1_relat_1 @ B ) =>
% 0.17/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.17/0.49  thf('9', plain,
% 0.17/0.49      (![X27 : $i, X28 : $i]:
% 0.17/0.49         (~ (v4_relat_1 @ X27 @ X28)
% 0.17/0.49          | (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 0.17/0.49          | ~ (v1_relat_1 @ X27))),
% 0.17/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.17/0.49  thf('10', plain,
% 0.17/0.49      ((~ (v1_relat_1 @ sk_D_1)
% 0.17/0.49        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.17/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.17/0.49  thf('11', plain,
% 0.17/0.49      ((m1_subset_1 @ sk_D_1 @ 
% 0.17/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf(cc2_relat_1, axiom,
% 0.17/0.49    (![A:$i]:
% 0.17/0.49     ( ( v1_relat_1 @ A ) =>
% 0.17/0.49       ( ![B:$i]:
% 0.17/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.17/0.49  thf('12', plain,
% 0.17/0.49      (![X23 : $i, X24 : $i]:
% 0.17/0.49         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.17/0.49          | (v1_relat_1 @ X23)
% 0.17/0.49          | ~ (v1_relat_1 @ X24))),
% 0.17/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.17/0.49  thf('13', plain,
% 0.17/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.17/0.49        | (v1_relat_1 @ sk_D_1))),
% 0.17/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.17/0.49  thf(fc6_relat_1, axiom,
% 0.17/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.17/0.49  thf('14', plain,
% 0.17/0.49      (![X29 : $i, X30 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X29 @ X30))),
% 0.17/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.17/0.49  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.17/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.17/0.49  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.17/0.49      inference('demod', [status(thm)], ['10', '15'])).
% 0.17/0.49  thf(l3_zfmisc_1, axiom,
% 0.17/0.49    (![A:$i,B:$i]:
% 0.17/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.17/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.17/0.49  thf('17', plain,
% 0.17/0.49      (![X13 : $i, X14 : $i]:
% 0.17/0.49         (((X14) = (k1_tarski @ X13))
% 0.17/0.49          | ((X14) = (k1_xboole_0))
% 0.17/0.49          | ~ (r1_tarski @ X14 @ (k1_tarski @ X13)))),
% 0.17/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.17/0.49  thf('18', plain,
% 0.17/0.49      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.17/0.49        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.17/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.17/0.49  thf(t69_enumset1, axiom,
% 0.17/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.17/0.49  thf('19', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.17/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.17/0.49  thf(d2_tarski, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i]:
% 0.17/0.49     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.17/0.49       ( ![D:$i]:
% 0.17/0.49         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.17/0.49  thf('20', plain,
% 0.17/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.49         (((X2) != (X1))
% 0.17/0.49          | (r2_hidden @ X2 @ X3)
% 0.17/0.49          | ((X3) != (k2_tarski @ X4 @ X1)))),
% 0.17/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.17/0.49  thf('21', plain,
% 0.17/0.49      (![X1 : $i, X4 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X4 @ X1))),
% 0.17/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.17/0.49  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.17/0.49      inference('sup+', [status(thm)], ['19', '21'])).
% 0.17/0.49  thf('23', plain,
% 0.17/0.49      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.17/0.49        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.17/0.49      inference('sup+', [status(thm)], ['18', '22'])).
% 0.17/0.49  thf(t117_funct_1, axiom,
% 0.17/0.49    (![A:$i,B:$i]:
% 0.17/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.17/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.17/0.49         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.17/0.49  thf('24', plain,
% 0.17/0.49      (![X38 : $i, X39 : $i]:
% 0.17/0.49         (~ (r2_hidden @ X38 @ (k1_relat_1 @ X39))
% 0.17/0.49          | ((k11_relat_1 @ X39 @ X38) = (k1_tarski @ (k1_funct_1 @ X39 @ X38)))
% 0.17/0.49          | ~ (v1_funct_1 @ X39)
% 0.17/0.49          | ~ (v1_relat_1 @ X39))),
% 0.17/0.49      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.17/0.49  thf('25', plain,
% 0.17/0.49      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.17/0.49        | ~ (v1_relat_1 @ sk_D_1)
% 0.17/0.49        | ~ (v1_funct_1 @ sk_D_1)
% 0.17/0.49        | ((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.17/0.49            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.17/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.17/0.49  thf('26', plain, ((v1_relat_1 @ sk_D_1)),
% 0.17/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.17/0.49  thf('27', plain, ((v1_funct_1 @ sk_D_1)),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf(d16_relat_1, axiom,
% 0.17/0.49    (![A:$i]:
% 0.17/0.49     ( ( v1_relat_1 @ A ) =>
% 0.17/0.49       ( ![B:$i]:
% 0.17/0.49         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.17/0.49  thf('28', plain,
% 0.17/0.49      (![X25 : $i, X26 : $i]:
% 0.17/0.49         (((k11_relat_1 @ X25 @ X26) = (k9_relat_1 @ X25 @ (k1_tarski @ X26)))
% 0.17/0.49          | ~ (v1_relat_1 @ X25))),
% 0.17/0.49      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.17/0.49  thf('29', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.17/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.17/0.49  thf(t209_relat_1, axiom,
% 0.17/0.49    (![A:$i,B:$i]:
% 0.17/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.17/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.17/0.49  thf('30', plain,
% 0.17/0.49      (![X35 : $i, X36 : $i]:
% 0.17/0.49         (((X35) = (k7_relat_1 @ X35 @ X36))
% 0.17/0.49          | ~ (v4_relat_1 @ X35 @ X36)
% 0.17/0.49          | ~ (v1_relat_1 @ X35))),
% 0.17/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.17/0.49  thf('31', plain,
% 0.17/0.49      ((~ (v1_relat_1 @ sk_D_1)
% 0.17/0.49        | ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))))),
% 0.17/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.17/0.49  thf('32', plain, ((v1_relat_1 @ sk_D_1)),
% 0.17/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.17/0.49  thf('33', plain, (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.17/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.17/0.49  thf(t148_relat_1, axiom,
% 0.17/0.49    (![A:$i,B:$i]:
% 0.17/0.49     ( ( v1_relat_1 @ B ) =>
% 0.17/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.17/0.49  thf('34', plain,
% 0.17/0.49      (![X33 : $i, X34 : $i]:
% 0.17/0.49         (((k2_relat_1 @ (k7_relat_1 @ X33 @ X34)) = (k9_relat_1 @ X33 @ X34))
% 0.17/0.49          | ~ (v1_relat_1 @ X33))),
% 0.17/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.17/0.49  thf('35', plain,
% 0.17/0.49      ((((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))
% 0.17/0.49        | ~ (v1_relat_1 @ sk_D_1))),
% 0.17/0.49      inference('sup+', [status(thm)], ['33', '34'])).
% 0.17/0.49  thf('36', plain, ((v1_relat_1 @ sk_D_1)),
% 0.17/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.17/0.49  thf('37', plain,
% 0.17/0.49      (((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.17/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.17/0.49  thf('38', plain,
% 0.17/0.49      ((((k2_relat_1 @ sk_D_1) = (k11_relat_1 @ sk_D_1 @ sk_A))
% 0.17/0.49        | ~ (v1_relat_1 @ sk_D_1))),
% 0.17/0.49      inference('sup+', [status(thm)], ['28', '37'])).
% 0.17/0.49  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 0.17/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.17/0.49  thf('40', plain, (((k2_relat_1 @ sk_D_1) = (k11_relat_1 @ sk_D_1 @ sk_A))),
% 0.17/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.17/0.49  thf('41', plain,
% 0.17/0.49      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.17/0.49        | ((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.17/0.49      inference('demod', [status(thm)], ['25', '26', '27', '40'])).
% 0.17/0.49  thf('42', plain,
% 0.17/0.49      (~ (r1_tarski @ 
% 0.17/0.49          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.17/0.49          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf('43', plain,
% 0.17/0.49      ((~ (r1_tarski @ 
% 0.17/0.49           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.17/0.49           (k2_relat_1 @ sk_D_1))
% 0.17/0.49        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.17/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.17/0.49  thf('44', plain,
% 0.17/0.49      (![X0 : $i]:
% 0.17/0.49         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.17/0.49           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.17/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.49  thf('45', plain,
% 0.17/0.49      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 0.17/0.49        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.17/0.49      inference('demod', [status(thm)], ['43', '44'])).
% 0.17/0.49  thf('46', plain,
% 0.17/0.49      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.17/0.49      inference('sup-', [status(thm)], ['5', '45'])).
% 0.17/0.49  thf('47', plain, ((v1_relat_1 @ sk_D_1)),
% 0.17/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.17/0.49  thf('48', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.17/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.17/0.49  thf(t64_relat_1, axiom,
% 0.17/0.49    (![A:$i]:
% 0.17/0.49     ( ( v1_relat_1 @ A ) =>
% 0.17/0.49       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.17/0.49           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.17/0.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.17/0.49  thf('49', plain,
% 0.17/0.49      (![X37 : $i]:
% 0.17/0.49         (((k1_relat_1 @ X37) != (k1_xboole_0))
% 0.17/0.49          | ((X37) = (k1_xboole_0))
% 0.17/0.49          | ~ (v1_relat_1 @ X37))),
% 0.17/0.49      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.17/0.49  thf('50', plain,
% 0.17/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.17/0.49        | ~ (v1_relat_1 @ sk_D_1)
% 0.17/0.49        | ((sk_D_1) = (k1_xboole_0)))),
% 0.17/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.17/0.49  thf('51', plain, ((v1_relat_1 @ sk_D_1)),
% 0.17/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.17/0.49  thf('52', plain,
% 0.17/0.49      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.17/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.17/0.49  thf('53', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.17/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.17/0.49  thf(t4_subset_1, axiom,
% 0.17/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.17/0.49  thf('54', plain,
% 0.17/0.49      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.17/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.17/0.49  thf('55', plain,
% 0.17/0.49      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.17/0.49         ((v4_relat_1 @ X40 @ X41)
% 0.17/0.49          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.17/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.17/0.49  thf('56', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.17/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.17/0.49  thf('57', plain,
% 0.17/0.49      (![X35 : $i, X36 : $i]:
% 0.17/0.49         (((X35) = (k7_relat_1 @ X35 @ X36))
% 0.17/0.49          | ~ (v4_relat_1 @ X35 @ X36)
% 0.17/0.49          | ~ (v1_relat_1 @ X35))),
% 0.17/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.17/0.49  thf('58', plain,
% 0.17/0.49      (![X0 : $i]:
% 0.17/0.49         (~ (v1_relat_1 @ k1_xboole_0)
% 0.17/0.49          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.17/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.17/0.49  thf(t113_zfmisc_1, axiom,
% 0.17/0.49    (![A:$i,B:$i]:
% 0.17/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.17/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.17/0.49  thf('59', plain,
% 0.17/0.49      (![X17 : $i, X18 : $i]:
% 0.17/0.49         (((k2_zfmisc_1 @ X17 @ X18) = (k1_xboole_0))
% 0.17/0.49          | ((X17) != (k1_xboole_0)))),
% 0.17/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.17/0.49  thf('60', plain,
% 0.17/0.49      (![X18 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.17/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.17/0.49  thf('61', plain,
% 0.17/0.49      (![X29 : $i, X30 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X29 @ X30))),
% 0.17/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.17/0.49  thf('62', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.17/0.49      inference('sup+', [status(thm)], ['60', '61'])).
% 0.17/0.49  thf('63', plain,
% 0.17/0.49      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.17/0.49      inference('demod', [status(thm)], ['58', '62'])).
% 0.17/0.49  thf('64', plain,
% 0.17/0.49      (![X33 : $i, X34 : $i]:
% 0.17/0.49         (((k2_relat_1 @ (k7_relat_1 @ X33 @ X34)) = (k9_relat_1 @ X33 @ X34))
% 0.17/0.49          | ~ (v1_relat_1 @ X33))),
% 0.17/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.17/0.49  thf('65', plain,
% 0.17/0.49      (![X0 : $i]:
% 0.17/0.49         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.17/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.17/0.49      inference('sup+', [status(thm)], ['63', '64'])).
% 0.17/0.49  thf(t60_relat_1, axiom,
% 0.17/0.49    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.17/0.49     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.17/0.49  thf('66', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.17/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.17/0.49  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.17/0.49      inference('sup+', [status(thm)], ['60', '61'])).
% 0.17/0.49  thf('68', plain,
% 0.17/0.49      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.17/0.49      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.17/0.49  thf('69', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.17/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.17/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.17/0.49  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.17/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.17/0.49  thf('71', plain, ($false),
% 0.17/0.49      inference('demod', [status(thm)], ['4', '53', '68', '69', '70'])).
% 0.17/0.49  
% 0.17/0.49  % SZS output end Refutation
% 0.17/0.49  
% 0.17/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
