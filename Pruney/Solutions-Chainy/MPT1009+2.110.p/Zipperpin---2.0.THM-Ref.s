%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yMbQKcarCE

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:04 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  137 (1028 expanded)
%              Number of leaves         :   42 ( 336 expanded)
%              Depth                    :   17
%              Number of atoms          :  946 (11191 expanded)
%              Number of equality atoms :   70 ( 537 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k7_relset_1 @ X49 @ X50 @ X48 @ X51 )
        = ( k9_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( v4_relat_1 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v4_relat_1 @ X30 @ X31 )
      | ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16
        = ( k1_tarski @ X15 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('20',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ X43 ) )
      | ~ ( r2_hidden @ X44 @ ( k1_relat_1 @ X43 ) )
      | ( ( k9_relat_1 @ X43 @ ( k2_tarski @ X42 @ X44 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X43 @ X42 ) @ ( k1_funct_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_A ) )
      = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k7_relat_1 @ X40 @ X41 ) )
      | ~ ( v4_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('35',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','39','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('46',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X36 @ X37 ) @ ( k2_relat_1 @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) @ X0 ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('51',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('52',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','54'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X52: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_D_1 ) ) @ sk_D_1 )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) )
      = sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_zfmisc_1 @ X19 @ X20 )
        = k1_xboole_0 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('63',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('64',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('65',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','54'])).

thf('68',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('69',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('70',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    k1_xboole_0 = sk_D_1 ),
    inference(demod,[status(thm)],['61','63','66','67','68','69','70'])).

thf('72',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('73',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( v5_relat_1 @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('75',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v5_relat_1 @ X32 @ X33 )
      | ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('78',plain,(
    ! [X34: $i,X35: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('82',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X36 @ X37 ) @ ( k2_relat_1 @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['77','78'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    k1_xboole_0 = sk_D_1 ),
    inference(demod,[status(thm)],['61','63','66','67','68','69','70'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['4','71','90','91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yMbQKcarCE
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:51:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.81  % Solved by: fo/fo7.sh
% 0.58/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.81  % done 669 iterations in 0.354s
% 0.58/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.81  % SZS output start Refutation
% 0.58/0.81  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.58/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.81  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.58/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.81  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.81  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.81  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.58/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.81  thf(t64_funct_2, conjecture,
% 0.58/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.81         ( m1_subset_1 @
% 0.58/0.81           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.81       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.81         ( r1_tarski @
% 0.58/0.81           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.58/0.81           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.58/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.81    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.81            ( m1_subset_1 @
% 0.58/0.81              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.81          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.81            ( r1_tarski @
% 0.58/0.81              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.58/0.81              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.58/0.81    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.58/0.81  thf('0', plain,
% 0.58/0.81      (~ (r1_tarski @ 
% 0.58/0.81          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.58/0.81          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('1', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_D_1 @ 
% 0.58/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(redefinition_k7_relset_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.81       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.58/0.81  thf('2', plain,
% 0.58/0.81      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.58/0.81          | ((k7_relset_1 @ X49 @ X50 @ X48 @ X51) = (k9_relat_1 @ X48 @ X51)))),
% 0.58/0.81      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.58/0.81  thf('3', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.58/0.81           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.81  thf('4', plain,
% 0.58/0.81      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.58/0.81          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.81  thf('5', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_D_1 @ 
% 0.58/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(cc2_relset_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.81  thf('6', plain,
% 0.58/0.81      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.58/0.81         ((v4_relat_1 @ X45 @ X46)
% 0.58/0.81          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.81  thf('7', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.81  thf(d18_relat_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ B ) =>
% 0.58/0.81       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.58/0.81  thf('8', plain,
% 0.58/0.81      (![X30 : $i, X31 : $i]:
% 0.58/0.81         (~ (v4_relat_1 @ X30 @ X31)
% 0.58/0.81          | (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.58/0.81          | ~ (v1_relat_1 @ X30))),
% 0.58/0.81      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.58/0.81  thf('9', plain,
% 0.58/0.81      ((~ (v1_relat_1 @ sk_D_1)
% 0.58/0.81        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.81  thf('10', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_D_1 @ 
% 0.58/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(cc2_relat_1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ A ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.58/0.81  thf('11', plain,
% 0.58/0.81      (![X28 : $i, X29 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.58/0.81          | (v1_relat_1 @ X28)
% 0.58/0.81          | ~ (v1_relat_1 @ X29))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.81  thf('12', plain,
% 0.58/0.81      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.58/0.81        | (v1_relat_1 @ sk_D_1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.81  thf(fc6_relat_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.58/0.81  thf('13', plain,
% 0.58/0.81      (![X34 : $i, X35 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X34 @ X35))),
% 0.58/0.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.81  thf('14', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.81      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['9', '14'])).
% 0.58/0.81  thf(l3_zfmisc_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.58/0.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.58/0.81  thf('16', plain,
% 0.58/0.81      (![X15 : $i, X16 : $i]:
% 0.58/0.81         (((X16) = (k1_tarski @ X15))
% 0.58/0.81          | ((X16) = (k1_xboole_0))
% 0.58/0.81          | ~ (r1_tarski @ X16 @ (k1_tarski @ X15)))),
% 0.58/0.81      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.58/0.81  thf('17', plain,
% 0.58/0.81      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.58/0.81        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.81  thf(t69_enumset1, axiom,
% 0.58/0.81    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.81  thf('18', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.58/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.81  thf(d2_tarski, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.58/0.81       ( ![D:$i]:
% 0.58/0.81         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.58/0.81  thf('19', plain,
% 0.58/0.81      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.81         (((X4) != (X3))
% 0.58/0.81          | (r2_hidden @ X4 @ X5)
% 0.58/0.81          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.58/0.81      inference('cnf', [status(esa)], [d2_tarski])).
% 0.58/0.81  thf('20', plain,
% 0.58/0.81      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 0.58/0.81      inference('simplify', [status(thm)], ['19'])).
% 0.58/0.81  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['18', '20'])).
% 0.58/0.81  thf('22', plain,
% 0.58/0.81      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.58/0.81        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['17', '21'])).
% 0.58/0.81  thf('23', plain,
% 0.58/0.81      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.58/0.81        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['17', '21'])).
% 0.58/0.81  thf(t118_funct_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.58/0.81       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.58/0.81           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.58/0.81         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.58/0.81           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.58/0.81  thf('24', plain,
% 0.58/0.81      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X42 @ (k1_relat_1 @ X43))
% 0.58/0.81          | ~ (r2_hidden @ X44 @ (k1_relat_1 @ X43))
% 0.58/0.81          | ((k9_relat_1 @ X43 @ (k2_tarski @ X42 @ X44))
% 0.58/0.81              = (k2_tarski @ (k1_funct_1 @ X43 @ X42) @ 
% 0.58/0.81                 (k1_funct_1 @ X43 @ X44)))
% 0.58/0.81          | ~ (v1_funct_1 @ X43)
% 0.58/0.81          | ~ (v1_relat_1 @ X43))),
% 0.58/0.81      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.58/0.81  thf('25', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.58/0.81          | ~ (v1_relat_1 @ sk_D_1)
% 0.58/0.81          | ~ (v1_funct_1 @ sk_D_1)
% 0.58/0.81          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ X0))
% 0.58/0.81              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.58/0.81                 (k1_funct_1 @ sk_D_1 @ X0)))
% 0.58/0.81          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.81  thf('26', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.81      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf('27', plain, ((v1_funct_1 @ sk_D_1)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('28', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.58/0.81          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ X0))
% 0.58/0.81              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.58/0.81                 (k1_funct_1 @ sk_D_1 @ X0)))
% 0.58/0.81          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.58/0.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.58/0.81  thf('29', plain,
% 0.58/0.81      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.58/0.81        | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ sk_A))
% 0.58/0.81            = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.58/0.81               (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.58/0.81        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['22', '28'])).
% 0.58/0.81  thf('30', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.58/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.81  thf('31', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.81  thf(t209_relat_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.58/0.81       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.58/0.81  thf('32', plain,
% 0.58/0.81      (![X40 : $i, X41 : $i]:
% 0.58/0.81         (((X40) = (k7_relat_1 @ X40 @ X41))
% 0.58/0.81          | ~ (v4_relat_1 @ X40 @ X41)
% 0.58/0.81          | ~ (v1_relat_1 @ X40))),
% 0.58/0.81      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.58/0.81  thf('33', plain,
% 0.58/0.81      ((~ (v1_relat_1 @ sk_D_1)
% 0.58/0.81        | ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.58/0.81  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.81      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf('35', plain, (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['33', '34'])).
% 0.58/0.81  thf(t148_relat_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ B ) =>
% 0.58/0.81       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.58/0.81  thf('36', plain,
% 0.58/0.81      (![X38 : $i, X39 : $i]:
% 0.58/0.81         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 0.58/0.81          | ~ (v1_relat_1 @ X38))),
% 0.58/0.81      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.58/0.81  thf('37', plain,
% 0.58/0.81      ((((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))
% 0.58/0.81        | ~ (v1_relat_1 @ sk_D_1))),
% 0.58/0.81      inference('sup+', [status(thm)], ['35', '36'])).
% 0.58/0.81  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.81      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf('39', plain,
% 0.58/0.81      (((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.81  thf('40', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.58/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.81  thf('41', plain,
% 0.58/0.81      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.58/0.81        | ((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.58/0.81        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['29', '30', '39', '40'])).
% 0.58/0.81  thf('42', plain,
% 0.58/0.81      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.58/0.81        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['41'])).
% 0.58/0.81  thf('43', plain,
% 0.58/0.81      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.58/0.81          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.81  thf('44', plain,
% 0.58/0.81      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 0.58/0.81        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.81  thf('45', plain, (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['33', '34'])).
% 0.58/0.81  thf('46', plain,
% 0.58/0.81      (![X38 : $i, X39 : $i]:
% 0.58/0.81         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 0.58/0.81          | ~ (v1_relat_1 @ X38))),
% 0.58/0.81      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.58/0.81  thf(t144_relat_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ B ) =>
% 0.58/0.81       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.58/0.81  thf('47', plain,
% 0.58/0.81      (![X36 : $i, X37 : $i]:
% 0.58/0.81         ((r1_tarski @ (k9_relat_1 @ X36 @ X37) @ (k2_relat_1 @ X36))
% 0.58/0.81          | ~ (v1_relat_1 @ X36))),
% 0.58/0.81      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.58/0.81  thf('48', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.58/0.81           (k9_relat_1 @ X1 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ X1)
% 0.58/0.81          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['46', '47'])).
% 0.58/0.81  thf('49', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ sk_D_1)
% 0.58/0.81          | ~ (v1_relat_1 @ sk_D_1)
% 0.58/0.81          | (r1_tarski @ 
% 0.58/0.81             (k9_relat_1 @ (k7_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)) @ X0) @ 
% 0.58/0.81             (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['45', '48'])).
% 0.58/0.81  thf('50', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.81      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf('51', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.81      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf('52', plain, (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['33', '34'])).
% 0.58/0.81  thf('53', plain,
% 0.58/0.81      (((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.81  thf('54', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))),
% 0.58/0.81      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.58/0.81  thf('55', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.58/0.81      inference('demod', [status(thm)], ['44', '54'])).
% 0.58/0.81  thf(t3_funct_2, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.81       ( ( v1_funct_1 @ A ) & 
% 0.58/0.81         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.58/0.81         ( m1_subset_1 @
% 0.58/0.81           A @ 
% 0.58/0.81           ( k1_zfmisc_1 @
% 0.58/0.81             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.81  thf('56', plain,
% 0.58/0.81      (![X52 : $i]:
% 0.58/0.81         ((m1_subset_1 @ X52 @ 
% 0.58/0.81           (k1_zfmisc_1 @ 
% 0.58/0.81            (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52))))
% 0.58/0.81          | ~ (v1_funct_1 @ X52)
% 0.58/0.81          | ~ (v1_relat_1 @ X52))),
% 0.58/0.81      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.58/0.81  thf(t3_subset, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.81  thf('57', plain,
% 0.58/0.81      (![X22 : $i, X23 : $i]:
% 0.58/0.81         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.81  thf('58', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | ~ (v1_funct_1 @ X0)
% 0.58/0.81          | (r1_tarski @ X0 @ 
% 0.58/0.81             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.81  thf(d10_xboole_0, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.81  thf('59', plain,
% 0.58/0.81      (![X0 : $i, X2 : $i]:
% 0.58/0.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.58/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.81  thf('60', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_funct_1 @ X0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | ~ (r1_tarski @ 
% 0.58/0.81               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.58/0.81          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.81  thf('61', plain,
% 0.58/0.81      ((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_D_1)) @ 
% 0.58/0.81           sk_D_1)
% 0.58/0.81        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1))
% 0.58/0.81            = (sk_D_1))
% 0.58/0.81        | ~ (v1_relat_1 @ sk_D_1)
% 0.58/0.81        | ~ (v1_funct_1 @ sk_D_1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['55', '60'])).
% 0.58/0.81  thf(t113_zfmisc_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.81  thf('62', plain,
% 0.58/0.81      (![X19 : $i, X20 : $i]:
% 0.58/0.81         (((k2_zfmisc_1 @ X19 @ X20) = (k1_xboole_0))
% 0.58/0.81          | ((X19) != (k1_xboole_0)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.81  thf('63', plain,
% 0.58/0.81      (![X20 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['62'])).
% 0.58/0.81  thf(t4_subset_1, axiom,
% 0.58/0.81    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.81  thf('64', plain,
% 0.58/0.81      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.58/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.81  thf('65', plain,
% 0.58/0.81      (![X22 : $i, X23 : $i]:
% 0.58/0.81         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.81  thf('66', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.81      inference('sup-', [status(thm)], ['64', '65'])).
% 0.58/0.81  thf('67', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.58/0.81      inference('demod', [status(thm)], ['44', '54'])).
% 0.58/0.81  thf('68', plain,
% 0.58/0.81      (![X20 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['62'])).
% 0.58/0.81  thf('69', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.81      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf('70', plain, ((v1_funct_1 @ sk_D_1)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('71', plain, (((k1_xboole_0) = (sk_D_1))),
% 0.58/0.81      inference('demod', [status(thm)],
% 0.58/0.81                ['61', '63', '66', '67', '68', '69', '70'])).
% 0.58/0.81  thf('72', plain,
% 0.58/0.81      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.58/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.81  thf('73', plain,
% 0.58/0.81      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.58/0.81         ((v5_relat_1 @ X45 @ X47)
% 0.58/0.82          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.82  thf('74', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('sup-', [status(thm)], ['72', '73'])).
% 0.58/0.82  thf(d19_relat_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( v1_relat_1 @ B ) =>
% 0.58/0.82       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.58/0.82  thf('75', plain,
% 0.58/0.82      (![X32 : $i, X33 : $i]:
% 0.58/0.82         (~ (v5_relat_1 @ X32 @ X33)
% 0.58/0.82          | (r1_tarski @ (k2_relat_1 @ X32) @ X33)
% 0.58/0.82          | ~ (v1_relat_1 @ X32))),
% 0.58/0.82      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.58/0.82  thf('76', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.82          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['74', '75'])).
% 0.58/0.82  thf('77', plain,
% 0.58/0.82      (![X20 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['62'])).
% 0.58/0.82  thf('78', plain,
% 0.58/0.82      (![X34 : $i, X35 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X34 @ X35))),
% 0.58/0.82      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.82  thf('79', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.82      inference('sup+', [status(thm)], ['77', '78'])).
% 0.58/0.82  thf('80', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.58/0.82      inference('demod', [status(thm)], ['76', '79'])).
% 0.58/0.82  thf('81', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('sup-', [status(thm)], ['64', '65'])).
% 0.58/0.82  thf('82', plain,
% 0.58/0.82      (![X0 : $i, X2 : $i]:
% 0.58/0.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.58/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.82  thf('83', plain,
% 0.58/0.82      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['81', '82'])).
% 0.58/0.82  thf('84', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['80', '83'])).
% 0.58/0.82  thf('85', plain,
% 0.58/0.82      (![X36 : $i, X37 : $i]:
% 0.58/0.82         ((r1_tarski @ (k9_relat_1 @ X36 @ X37) @ (k2_relat_1 @ X36))
% 0.58/0.82          | ~ (v1_relat_1 @ X36))),
% 0.58/0.82      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.58/0.82  thf('86', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.58/0.82          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['84', '85'])).
% 0.58/0.82  thf('87', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.82      inference('sup+', [status(thm)], ['77', '78'])).
% 0.58/0.82  thf('88', plain,
% 0.58/0.82      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.58/0.82      inference('demod', [status(thm)], ['86', '87'])).
% 0.58/0.82  thf('89', plain,
% 0.58/0.82      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['81', '82'])).
% 0.58/0.82  thf('90', plain,
% 0.58/0.82      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['88', '89'])).
% 0.58/0.82  thf('91', plain, (((k1_xboole_0) = (sk_D_1))),
% 0.58/0.82      inference('demod', [status(thm)],
% 0.58/0.82                ['61', '63', '66', '67', '68', '69', '70'])).
% 0.58/0.82  thf('92', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('sup-', [status(thm)], ['64', '65'])).
% 0.58/0.82  thf('93', plain, ($false),
% 0.58/0.82      inference('demod', [status(thm)], ['4', '71', '90', '91', '92'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.58/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
