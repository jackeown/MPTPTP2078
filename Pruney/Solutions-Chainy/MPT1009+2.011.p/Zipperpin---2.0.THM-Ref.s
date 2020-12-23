%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wdul8UhTkK

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:50 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  246 (2838 expanded)
%              Number of leaves         :   38 ( 849 expanded)
%              Depth                    :   34
%              Number of atoms          : 1929 (21962 expanded)
%              Number of equality atoms :  122 (1534 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ( ( k7_relset_1 @ X64 @ X65 @ X63 @ X66 )
        = ( k9_relat_1 @ X63 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k2_zfmisc_1 @ X42 @ X43 )
        = k1_xboole_0 )
      | ( X42 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X67 ) @ X68 )
      | ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X69 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k2_zfmisc_1 @ X42 @ X43 )
        = k1_xboole_0 )
      | ( X43 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X42: $i] :
      ( ( k2_zfmisc_1 @ X42 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( v4_relat_1 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v4_relat_1 @ X49 @ X50 )
      | ( r1_tarski @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X42: $i] :
      ( ( k2_zfmisc_1 @ X42 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v1_relat_1 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','27'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X60 @ X61 @ X59 @ X62 ) @ ( k1_zfmisc_1 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','27'])).

thf('32',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ( ( k7_relset_1 @ X64 @ X65 @ X63 @ X66 )
        = ( k9_relat_1 @ X63 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( v4_relat_1 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('40',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v4_relat_1 @ X49 @ X50 )
      | ( r1_tarski @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v1_relat_1 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('50',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ( X11 = X10 )
      | ( X11 = X7 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('52',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ( X11 = X7 )
      | ( X11 = X10 )
      | ~ ( r2_hidden @ X11 @ ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X49 ) @ X50 )
      | ( v4_relat_1 @ X49 @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( v4_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
      | ( v4_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('71',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D_1 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v4_relat_1 @ X49 @ X50 )
      | ( r1_tarski @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( X0
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('83',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('87',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v4_relat_1 @ X49 @ X50 )
      | ( r1_tarski @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ X1 ) )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['80','93'])).

thf('95',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('97',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('98',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X67 ) @ X68 )
      | ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X69 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['95','102'])).

thf('104',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','27'])).

thf('107',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X42 @ X41 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['94','115'])).

thf('117',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('126',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['114'])).

thf('127',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['114'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','128'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('130',plain,(
    ! [X71: $i] :
      ( ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X71 ) @ ( k2_relat_1 @ X71 ) ) ) )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('131',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D_1 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) )
      = sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('137',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['114'])).

thf('138',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('140',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) )
      = sk_D_1 ) ),
    inference(demod,[status(thm)],['135','138','139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','128'])).

thf('143',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('144',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ( ( k7_relset_1 @ X64 @ X65 @ X63 @ X66 )
        = ( k9_relat_1 @ X63 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      = ( k9_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ X1 @ k1_xboole_0 @ X0 )
        = ( k9_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('148',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('149',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ( ( k7_relset_1 @ X64 @ X65 @ X63 @ X66 )
        = ( k9_relat_1 @ X63 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X2 )
      = ( k9_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('153',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('156',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X60 @ X61 @ X59 @ X62 ) @ ( k1_zfmisc_1 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ k1_xboole_0 @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X2 )
      = ( k9_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('161',plain,(
    ! [X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X2 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['151','165'])).

thf('167',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['114'])).

thf('168',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['114'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['146','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['141','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('174',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('176',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('177',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k1_relat_1 @ X52 )
       != ( k1_tarski @ X51 ) )
      | ( ( k2_relat_1 @ X52 )
        = ( k1_tarski @ ( k1_funct_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['178'])).

thf('180',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('182',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('184',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('185',plain,(
    ! [X71: $i] :
      ( ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X71 ) @ ( k2_relat_1 @ X71 ) ) ) )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('186',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X67 ) @ X68 )
      | ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X69 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['184','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('191',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X67 ) @ X68 )
      | ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X69 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['183','193'])).

thf('195',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ( ( k7_relset_1 @ X64 @ X65 @ X63 @ X66 )
        = ( k9_relat_1 @ X63 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X71: $i] :
      ( ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X71 ) @ ( k2_relat_1 @ X71 ) ) ) )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('198',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X60 @ X61 @ X59 @ X62 ) @ ( k1_zfmisc_1 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D_1 ) ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['196','199'])).

thf('201',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('203',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('205',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    $false ),
    inference(demod,[status(thm)],['4','182','205'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wdul8UhTkK
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:57:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.32/1.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.32/1.52  % Solved by: fo/fo7.sh
% 1.32/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.32/1.52  % done 2971 iterations in 1.065s
% 1.32/1.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.32/1.52  % SZS output start Refutation
% 1.32/1.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.32/1.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.32/1.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.32/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.32/1.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.32/1.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.32/1.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.32/1.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.32/1.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.32/1.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.32/1.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.32/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.32/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.32/1.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.32/1.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.32/1.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.32/1.52  thf(sk_B_type, type, sk_B: $i).
% 1.32/1.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.32/1.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.32/1.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.32/1.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.32/1.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.32/1.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.32/1.52  thf(t64_funct_2, conjecture,
% 1.32/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.32/1.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.32/1.52         ( m1_subset_1 @
% 1.32/1.52           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.32/1.52       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.32/1.52         ( r1_tarski @
% 1.32/1.52           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.32/1.52           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 1.32/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.32/1.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.32/1.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.32/1.52            ( m1_subset_1 @
% 1.32/1.52              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.32/1.52          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.32/1.52            ( r1_tarski @
% 1.32/1.52              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.32/1.52              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 1.32/1.52    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 1.32/1.52  thf('0', plain,
% 1.32/1.52      (~ (r1_tarski @ 
% 1.32/1.52          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C_1) @ 
% 1.32/1.52          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('1', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_D_1 @ 
% 1.32/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf(redefinition_k7_relset_1, axiom,
% 1.32/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.32/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.32/1.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.32/1.52  thf('2', plain,
% 1.32/1.52      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 1.32/1.52          | ((k7_relset_1 @ X64 @ X65 @ X63 @ X66) = (k9_relat_1 @ X63 @ X66)))),
% 1.32/1.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.32/1.52  thf('3', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 1.32/1.52           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['1', '2'])).
% 1.32/1.52  thf('4', plain,
% 1.32/1.52      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_1) @ 
% 1.32/1.52          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.32/1.52      inference('demod', [status(thm)], ['0', '3'])).
% 1.32/1.52  thf(d10_xboole_0, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.32/1.52  thf('5', plain,
% 1.32/1.52      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.32/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.52  thf('6', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.32/1.52      inference('simplify', [status(thm)], ['5'])).
% 1.32/1.52  thf(t3_subset, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.32/1.52  thf('7', plain,
% 1.32/1.52      (![X46 : $i, X48 : $i]:
% 1.32/1.52         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['6', '7'])).
% 1.32/1.52  thf(t113_zfmisc_1, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.32/1.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.32/1.52  thf('9', plain,
% 1.32/1.52      (![X42 : $i, X43 : $i]:
% 1.32/1.52         (((k2_zfmisc_1 @ X42 @ X43) = (k1_xboole_0))
% 1.32/1.52          | ((X42) != (k1_xboole_0)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.32/1.52  thf('10', plain,
% 1.32/1.52      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.32/1.52      inference('simplify', [status(thm)], ['9'])).
% 1.32/1.52  thf(t13_relset_1, axiom,
% 1.32/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.32/1.52     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.32/1.52       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 1.32/1.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.32/1.52  thf('11', plain,
% 1.32/1.52      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 1.32/1.52         (~ (r1_tarski @ (k1_relat_1 @ X67) @ X68)
% 1.32/1.52          | (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 1.32/1.52          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X69))))),
% 1.32/1.52      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.32/1.52  thf('12', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.32/1.52          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.32/1.52          | ~ (r1_tarski @ (k1_relat_1 @ X1) @ X2))),
% 1.32/1.52      inference('sup-', [status(thm)], ['10', '11'])).
% 1.32/1.52  thf('13', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 1.32/1.52          | (m1_subset_1 @ k1_xboole_0 @ 
% 1.32/1.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['8', '12'])).
% 1.32/1.52  thf('14', plain,
% 1.32/1.52      (![X42 : $i, X43 : $i]:
% 1.32/1.52         (((k2_zfmisc_1 @ X42 @ X43) = (k1_xboole_0))
% 1.32/1.52          | ((X43) != (k1_xboole_0)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.32/1.52  thf('15', plain,
% 1.32/1.52      (![X42 : $i]: ((k2_zfmisc_1 @ X42 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.52      inference('simplify', [status(thm)], ['14'])).
% 1.32/1.52  thf('16', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['6', '7'])).
% 1.32/1.52  thf(cc2_relset_1, axiom,
% 1.32/1.52    (![A:$i,B:$i,C:$i]:
% 1.32/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.32/1.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.32/1.52  thf('17', plain,
% 1.32/1.52      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.32/1.52         ((v4_relat_1 @ X56 @ X57)
% 1.32/1.52          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 1.32/1.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.32/1.52  thf('18', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 1.32/1.52      inference('sup-', [status(thm)], ['16', '17'])).
% 1.32/1.52  thf('19', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 1.32/1.52      inference('sup+', [status(thm)], ['15', '18'])).
% 1.32/1.52  thf(d18_relat_1, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( v1_relat_1 @ B ) =>
% 1.32/1.52       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.32/1.52  thf('20', plain,
% 1.32/1.52      (![X49 : $i, X50 : $i]:
% 1.32/1.52         (~ (v4_relat_1 @ X49 @ X50)
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ X49) @ X50)
% 1.32/1.52          | ~ (v1_relat_1 @ X49))),
% 1.32/1.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.32/1.52  thf('21', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (~ (v1_relat_1 @ k1_xboole_0)
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['19', '20'])).
% 1.32/1.52  thf('22', plain,
% 1.32/1.52      (![X42 : $i]: ((k2_zfmisc_1 @ X42 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.52      inference('simplify', [status(thm)], ['14'])).
% 1.32/1.52  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['6', '7'])).
% 1.32/1.52  thf(cc1_relset_1, axiom,
% 1.32/1.52    (![A:$i,B:$i,C:$i]:
% 1.32/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.32/1.52       ( v1_relat_1 @ C ) ))).
% 1.32/1.52  thf('24', plain,
% 1.32/1.52      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.32/1.52         ((v1_relat_1 @ X53)
% 1.32/1.52          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 1.32/1.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.32/1.52  thf('25', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['23', '24'])).
% 1.32/1.52  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.32/1.52      inference('sup+', [status(thm)], ['22', '25'])).
% 1.32/1.52  thf('27', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.32/1.52      inference('demod', [status(thm)], ['21', '26'])).
% 1.32/1.52  thf('28', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.32/1.52      inference('demod', [status(thm)], ['13', '27'])).
% 1.32/1.52  thf(dt_k7_relset_1, axiom,
% 1.32/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.32/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.32/1.52       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.32/1.52  thf('29', plain,
% 1.32/1.52      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 1.32/1.52          | (m1_subset_1 @ (k7_relset_1 @ X60 @ X61 @ X59 @ X62) @ 
% 1.32/1.52             (k1_zfmisc_1 @ X61)))),
% 1.32/1.52      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.32/1.52  thf('30', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         (m1_subset_1 @ (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 1.32/1.52          (k1_zfmisc_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['28', '29'])).
% 1.32/1.52  thf('31', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.32/1.52      inference('demod', [status(thm)], ['13', '27'])).
% 1.32/1.52  thf('32', plain,
% 1.32/1.52      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 1.32/1.52          | ((k7_relset_1 @ X64 @ X65 @ X63 @ X66) = (k9_relat_1 @ X63 @ X66)))),
% 1.32/1.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.32/1.52  thf('33', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 1.32/1.52           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 1.32/1.52      inference('sup-', [status(thm)], ['31', '32'])).
% 1.32/1.52  thf('34', plain,
% 1.32/1.52      (![X0 : $i, X2 : $i]:
% 1.32/1.52         (m1_subset_1 @ (k9_relat_1 @ k1_xboole_0 @ X2) @ (k1_zfmisc_1 @ X0))),
% 1.32/1.52      inference('demod', [status(thm)], ['30', '33'])).
% 1.32/1.52  thf('35', plain,
% 1.32/1.52      (![X46 : $i, X47 : $i]:
% 1.32/1.52         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('36', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X1) @ X0)),
% 1.32/1.52      inference('sup-', [status(thm)], ['34', '35'])).
% 1.32/1.52  thf(d3_tarski, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( r1_tarski @ A @ B ) <=>
% 1.32/1.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.32/1.52  thf('37', plain,
% 1.32/1.52      (![X1 : $i, X3 : $i]:
% 1.32/1.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.32/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.32/1.52  thf('38', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_D_1 @ 
% 1.32/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('39', plain,
% 1.32/1.52      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.32/1.52         ((v4_relat_1 @ X56 @ X57)
% 1.32/1.52          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 1.32/1.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.32/1.52  thf('40', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 1.32/1.52      inference('sup-', [status(thm)], ['38', '39'])).
% 1.32/1.52  thf('41', plain,
% 1.32/1.52      (![X49 : $i, X50 : $i]:
% 1.32/1.52         (~ (v4_relat_1 @ X49 @ X50)
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ X49) @ X50)
% 1.32/1.52          | ~ (v1_relat_1 @ X49))),
% 1.32/1.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.32/1.52  thf('42', plain,
% 1.32/1.52      ((~ (v1_relat_1 @ sk_D_1)
% 1.32/1.52        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['40', '41'])).
% 1.32/1.52  thf('43', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_D_1 @ 
% 1.32/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('44', plain,
% 1.32/1.52      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.32/1.52         ((v1_relat_1 @ X53)
% 1.32/1.52          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 1.32/1.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.32/1.52  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 1.32/1.52      inference('sup-', [status(thm)], ['43', '44'])).
% 1.32/1.52  thf('46', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 1.32/1.52      inference('demod', [status(thm)], ['42', '45'])).
% 1.32/1.52  thf('47', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         (~ (r2_hidden @ X0 @ X1)
% 1.32/1.52          | (r2_hidden @ X0 @ X2)
% 1.32/1.52          | ~ (r1_tarski @ X1 @ X2))),
% 1.32/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.32/1.52  thf('48', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.32/1.52          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['46', '47'])).
% 1.32/1.52  thf('49', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 1.32/1.52          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) @ 
% 1.32/1.52             (k1_tarski @ sk_A)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['37', '48'])).
% 1.32/1.52  thf(t69_enumset1, axiom,
% 1.32/1.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.32/1.52  thf('50', plain,
% 1.32/1.52      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 1.32/1.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.32/1.52  thf(d2_tarski, axiom,
% 1.32/1.52    (![A:$i,B:$i,C:$i]:
% 1.32/1.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.32/1.52       ( ![D:$i]:
% 1.32/1.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.32/1.52  thf('51', plain,
% 1.32/1.52      (![X7 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.32/1.52         (~ (r2_hidden @ X11 @ X9)
% 1.32/1.52          | ((X11) = (X10))
% 1.32/1.52          | ((X11) = (X7))
% 1.32/1.52          | ((X9) != (k2_tarski @ X10 @ X7)))),
% 1.32/1.52      inference('cnf', [status(esa)], [d2_tarski])).
% 1.32/1.52  thf('52', plain,
% 1.32/1.52      (![X7 : $i, X10 : $i, X11 : $i]:
% 1.32/1.52         (((X11) = (X7))
% 1.32/1.52          | ((X11) = (X10))
% 1.32/1.52          | ~ (r2_hidden @ X11 @ (k2_tarski @ X10 @ X7)))),
% 1.32/1.52      inference('simplify', [status(thm)], ['51'])).
% 1.32/1.52  thf('53', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['50', '52'])).
% 1.32/1.52  thf('54', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.32/1.52      inference('simplify', [status(thm)], ['53'])).
% 1.32/1.52  thf('55', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 1.32/1.52          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) = (sk_A)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['49', '54'])).
% 1.32/1.52  thf('56', plain,
% 1.32/1.52      (![X1 : $i, X3 : $i]:
% 1.32/1.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.32/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.32/1.52  thf('57', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 1.32/1.52      inference('sup+', [status(thm)], ['55', '56'])).
% 1.32/1.52  thf('58', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 1.32/1.52          | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('simplify', [status(thm)], ['57'])).
% 1.32/1.52  thf('59', plain,
% 1.32/1.52      (![X49 : $i, X50 : $i]:
% 1.32/1.52         (~ (r1_tarski @ (k1_relat_1 @ X49) @ X50)
% 1.32/1.52          | (v4_relat_1 @ X49 @ X50)
% 1.32/1.52          | ~ (v1_relat_1 @ X49))),
% 1.32/1.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.32/1.52  thf('60', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ~ (v1_relat_1 @ sk_D_1)
% 1.32/1.52          | (v4_relat_1 @ sk_D_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['58', '59'])).
% 1.32/1.52  thf('61', plain, ((v1_relat_1 @ sk_D_1)),
% 1.32/1.52      inference('sup-', [status(thm)], ['43', '44'])).
% 1.32/1.52  thf('62', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | (v4_relat_1 @ sk_D_1 @ X0))),
% 1.32/1.52      inference('demod', [status(thm)], ['60', '61'])).
% 1.32/1.52  thf('63', plain,
% 1.32/1.52      (![X1 : $i, X3 : $i]:
% 1.32/1.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.32/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.32/1.52  thf('64', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.32/1.52      inference('simplify', [status(thm)], ['53'])).
% 1.32/1.52  thf('65', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.32/1.52          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['63', '64'])).
% 1.32/1.52  thf('66', plain,
% 1.32/1.52      (![X1 : $i, X3 : $i]:
% 1.32/1.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.32/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.32/1.52  thf('67', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (r2_hidden @ X0 @ X1)
% 1.32/1.52          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.32/1.52          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.32/1.52      inference('sup-', [status(thm)], ['65', '66'])).
% 1.32/1.52  thf('68', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.32/1.52      inference('simplify', [status(thm)], ['67'])).
% 1.32/1.52  thf('69', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((v4_relat_1 @ sk_D_1 @ X0)
% 1.32/1.52          | (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['62', '68'])).
% 1.32/1.52  thf('70', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 1.32/1.52      inference('demod', [status(thm)], ['42', '45'])).
% 1.32/1.52  thf('71', plain,
% 1.32/1.52      (![X4 : $i, X6 : $i]:
% 1.32/1.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.32/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.52  thf('72', plain,
% 1.32/1.52      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D_1))
% 1.32/1.52        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['70', '71'])).
% 1.32/1.52  thf('73', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((v4_relat_1 @ sk_D_1 @ X0)
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['69', '72'])).
% 1.32/1.52  thf('74', plain,
% 1.32/1.52      (![X49 : $i, X50 : $i]:
% 1.32/1.52         (~ (v4_relat_1 @ X49 @ X50)
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ X49) @ X50)
% 1.32/1.52          | ~ (v1_relat_1 @ X49))),
% 1.32/1.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.32/1.52  thf('75', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ~ (v1_relat_1 @ sk_D_1)
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['73', '74'])).
% 1.32/1.52  thf('76', plain, ((v1_relat_1 @ sk_D_1)),
% 1.32/1.52      inference('sup-', [status(thm)], ['43', '44'])).
% 1.32/1.52  thf('77', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 1.32/1.52      inference('demod', [status(thm)], ['75', '76'])).
% 1.32/1.52  thf('78', plain,
% 1.32/1.52      (![X4 : $i, X6 : $i]:
% 1.32/1.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.32/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.52  thf('79', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ((X0) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['77', '78'])).
% 1.32/1.52  thf('80', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['36', '79'])).
% 1.32/1.52  thf('81', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X1) @ X0)),
% 1.32/1.52      inference('sup-', [status(thm)], ['34', '35'])).
% 1.32/1.52  thf('82', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.32/1.52      inference('demod', [status(thm)], ['21', '26'])).
% 1.32/1.52  thf('83', plain,
% 1.32/1.52      (![X4 : $i, X6 : $i]:
% 1.32/1.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.32/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.52  thf('84', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 1.32/1.52          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['82', '83'])).
% 1.32/1.52  thf('85', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_relat_1 @ k1_xboole_0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['81', '84'])).
% 1.32/1.52  thf('86', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 1.32/1.52      inference('sup-', [status(thm)], ['16', '17'])).
% 1.32/1.52  thf('87', plain,
% 1.32/1.52      (![X49 : $i, X50 : $i]:
% 1.32/1.52         (~ (v4_relat_1 @ X49 @ X50)
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ X49) @ X50)
% 1.32/1.52          | ~ (v1_relat_1 @ X49))),
% 1.32/1.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.32/1.52  thf('88', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 1.32/1.52          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['86', '87'])).
% 1.32/1.52  thf('89', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['23', '24'])).
% 1.32/1.52  thf('90', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 1.32/1.52      inference('demod', [status(thm)], ['88', '89'])).
% 1.32/1.52  thf('91', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 1.32/1.52          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['82', '83'])).
% 1.32/1.52  thf('92', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ X0))
% 1.32/1.52           = (k1_relat_1 @ k1_xboole_0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['90', '91'])).
% 1.32/1.52  thf('93', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         ((k1_relat_1 @ (k2_zfmisc_1 @ (k9_relat_1 @ k1_xboole_0 @ X0) @ X1))
% 1.32/1.52           = (k1_relat_1 @ k1_xboole_0))),
% 1.32/1.52      inference('sup+', [status(thm)], ['85', '92'])).
% 1.32/1.52  thf('94', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X0))
% 1.32/1.52            = (k1_relat_1 @ k1_xboole_0))
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup+', [status(thm)], ['80', '93'])).
% 1.32/1.52  thf('95', plain,
% 1.32/1.52      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.32/1.52      inference('simplify', [status(thm)], ['9'])).
% 1.32/1.52  thf('96', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ X0))
% 1.32/1.52           = (k1_relat_1 @ k1_xboole_0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['90', '91'])).
% 1.32/1.52  thf('97', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['6', '7'])).
% 1.32/1.52  thf('98', plain,
% 1.32/1.52      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 1.32/1.52         (~ (r1_tarski @ (k1_relat_1 @ X67) @ X68)
% 1.32/1.52          | (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 1.32/1.52          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X69))))),
% 1.32/1.52      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.32/1.52  thf('99', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 1.32/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.32/1.52          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2))),
% 1.32/1.52      inference('sup-', [status(thm)], ['97', '98'])).
% 1.32/1.52  thf('100', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 1.32/1.52          | (m1_subset_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ X1) @ 
% 1.32/1.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['96', '99'])).
% 1.32/1.52  thf('101', plain,
% 1.32/1.52      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.32/1.52      inference('demod', [status(thm)], ['21', '26'])).
% 1.32/1.52  thf('102', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (m1_subset_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ X1) @ 
% 1.32/1.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.32/1.52      inference('demod', [status(thm)], ['100', '101'])).
% 1.32/1.52  thf('103', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (m1_subset_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ X0) @ 
% 1.32/1.52          (k1_zfmisc_1 @ k1_xboole_0))),
% 1.32/1.52      inference('sup+', [status(thm)], ['95', '102'])).
% 1.32/1.52  thf('104', plain,
% 1.32/1.52      (![X46 : $i, X47 : $i]:
% 1.32/1.52         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('105', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ X0) @ 
% 1.32/1.52          k1_xboole_0)),
% 1.32/1.52      inference('sup-', [status(thm)], ['103', '104'])).
% 1.32/1.52  thf('106', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.32/1.52      inference('demod', [status(thm)], ['13', '27'])).
% 1.32/1.52  thf('107', plain,
% 1.32/1.52      (![X46 : $i, X47 : $i]:
% 1.32/1.52         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('108', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['106', '107'])).
% 1.32/1.52  thf('109', plain,
% 1.32/1.52      (![X4 : $i, X6 : $i]:
% 1.32/1.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.32/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.52  thf('110', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ k1_xboole_0)
% 1.32/1.52          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['108', '109'])).
% 1.32/1.52  thf('111', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['105', '110'])).
% 1.32/1.52  thf('112', plain,
% 1.32/1.52      (![X41 : $i, X42 : $i]:
% 1.32/1.52         (((X41) = (k1_xboole_0))
% 1.32/1.52          | ((X42) = (k1_xboole_0))
% 1.32/1.52          | ((k2_zfmisc_1 @ X42 @ X41) != (k1_xboole_0)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.32/1.52  thf('113', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_xboole_0) != (k1_xboole_0))
% 1.32/1.52          | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.32/1.52          | ((X0) = (k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['111', '112'])).
% 1.32/1.52  thf('114', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((X0) = (k1_xboole_0)) | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.32/1.52      inference('simplify', [status(thm)], ['113'])).
% 1.32/1.52  thf('115', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.52      inference('condensation', [status(thm)], ['114'])).
% 1.32/1.52  thf('116', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X0))
% 1.32/1.52            = (k1_xboole_0))
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('demod', [status(thm)], ['94', '115'])).
% 1.32/1.52  thf('117', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.32/1.52      inference('simplify', [status(thm)], ['5'])).
% 1.32/1.52  thf('118', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 1.32/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.32/1.52          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2))),
% 1.32/1.52      inference('sup-', [status(thm)], ['97', '98'])).
% 1.32/1.52  thf('119', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 1.32/1.52          (k1_zfmisc_1 @ 
% 1.32/1.52           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['117', '118'])).
% 1.32/1.52  thf('120', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((m1_subset_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X0) @ 
% 1.32/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup+', [status(thm)], ['116', '119'])).
% 1.32/1.52  thf('121', plain,
% 1.32/1.52      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.32/1.52      inference('simplify', [status(thm)], ['9'])).
% 1.32/1.52  thf('122', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((m1_subset_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X0) @ 
% 1.32/1.52           (k1_zfmisc_1 @ k1_xboole_0))
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('demod', [status(thm)], ['120', '121'])).
% 1.32/1.52  thf('123', plain,
% 1.32/1.52      (![X46 : $i, X47 : $i]:
% 1.32/1.52         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('124', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X0) @ 
% 1.32/1.52             k1_xboole_0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['122', '123'])).
% 1.32/1.52  thf('125', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 1.32/1.52          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['82', '83'])).
% 1.32/1.52  thf('126', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.52      inference('condensation', [status(thm)], ['114'])).
% 1.32/1.52  thf('127', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.52      inference('condensation', [status(thm)], ['114'])).
% 1.32/1.52  thf('128', plain,
% 1.32/1.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.32/1.52      inference('demod', [status(thm)], ['125', '126', '127'])).
% 1.32/1.52  thf('129', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X0) = (k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['124', '128'])).
% 1.32/1.52  thf(t3_funct_2, axiom,
% 1.32/1.52    (![A:$i]:
% 1.32/1.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.32/1.52       ( ( v1_funct_1 @ A ) & 
% 1.32/1.52         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.32/1.52         ( m1_subset_1 @
% 1.32/1.52           A @ 
% 1.32/1.52           ( k1_zfmisc_1 @
% 1.32/1.52             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.32/1.52  thf('130', plain,
% 1.32/1.52      (![X71 : $i]:
% 1.32/1.52         ((m1_subset_1 @ X71 @ 
% 1.32/1.52           (k1_zfmisc_1 @ 
% 1.32/1.52            (k2_zfmisc_1 @ (k1_relat_1 @ X71) @ (k2_relat_1 @ X71))))
% 1.32/1.52          | ~ (v1_funct_1 @ X71)
% 1.32/1.52          | ~ (v1_relat_1 @ X71))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.32/1.52  thf('131', plain,
% 1.32/1.52      (![X46 : $i, X47 : $i]:
% 1.32/1.52         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('132', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (~ (v1_relat_1 @ X0)
% 1.32/1.52          | ~ (v1_funct_1 @ X0)
% 1.32/1.52          | (r1_tarski @ X0 @ 
% 1.32/1.52             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['130', '131'])).
% 1.32/1.52  thf('133', plain,
% 1.32/1.52      (![X4 : $i, X6 : $i]:
% 1.32/1.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.32/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.52  thf('134', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (~ (v1_funct_1 @ X0)
% 1.32/1.52          | ~ (v1_relat_1 @ X0)
% 1.32/1.52          | ~ (r1_tarski @ 
% 1.32/1.52               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 1.32/1.52          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['132', '133'])).
% 1.32/1.52  thf('135', plain,
% 1.32/1.52      ((~ (r1_tarski @ k1_xboole_0 @ sk_D_1)
% 1.32/1.52        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1))
% 1.32/1.52            = (sk_D_1))
% 1.32/1.52        | ~ (v1_relat_1 @ sk_D_1)
% 1.32/1.52        | ~ (v1_funct_1 @ sk_D_1))),
% 1.32/1.52      inference('sup-', [status(thm)], ['129', '134'])).
% 1.32/1.52  thf('136', plain,
% 1.32/1.52      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.32/1.52      inference('demod', [status(thm)], ['21', '26'])).
% 1.32/1.52  thf('137', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.52      inference('condensation', [status(thm)], ['114'])).
% 1.32/1.52  thf('138', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.32/1.52      inference('demod', [status(thm)], ['136', '137'])).
% 1.32/1.52  thf('139', plain, ((v1_relat_1 @ sk_D_1)),
% 1.32/1.52      inference('sup-', [status(thm)], ['43', '44'])).
% 1.32/1.52  thf('140', plain, ((v1_funct_1 @ sk_D_1)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('141', plain,
% 1.32/1.52      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1))
% 1.32/1.52            = (sk_D_1)))),
% 1.32/1.52      inference('demod', [status(thm)], ['135', '138', '139', '140'])).
% 1.32/1.52  thf('142', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X0) = (k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['124', '128'])).
% 1.32/1.52  thf('143', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['6', '7'])).
% 1.32/1.52  thf('144', plain,
% 1.32/1.52      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 1.32/1.52          | ((k7_relset_1 @ X64 @ X65 @ X63 @ X66) = (k9_relat_1 @ X63 @ X66)))),
% 1.32/1.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.32/1.52  thf('145', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         ((k7_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 1.32/1.52           = (k9_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))),
% 1.32/1.52      inference('sup-', [status(thm)], ['143', '144'])).
% 1.32/1.52  thf('146', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ X1 @ k1_xboole_0 @ X0)
% 1.32/1.52            = (k9_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X1) @ X0))
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup+', [status(thm)], ['142', '145'])).
% 1.32/1.52  thf('147', plain,
% 1.32/1.52      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.32/1.52      inference('demod', [status(thm)], ['21', '26'])).
% 1.32/1.52  thf('148', plain,
% 1.32/1.52      (![X46 : $i, X48 : $i]:
% 1.32/1.52         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('149', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['147', '148'])).
% 1.32/1.52  thf('150', plain,
% 1.32/1.52      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 1.32/1.52          | ((k7_relset_1 @ X64 @ X65 @ X63 @ X66) = (k9_relat_1 @ X63 @ X66)))),
% 1.32/1.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.32/1.52  thf('151', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         ((k7_relset_1 @ X1 @ X0 @ (k1_relat_1 @ k1_xboole_0) @ X2)
% 1.32/1.52           = (k9_relat_1 @ (k1_relat_1 @ k1_xboole_0) @ X2))),
% 1.32/1.52      inference('sup-', [status(thm)], ['149', '150'])).
% 1.32/1.52  thf('152', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 1.32/1.52      inference('demod', [status(thm)], ['88', '89'])).
% 1.32/1.52  thf('153', plain,
% 1.32/1.52      (![X46 : $i, X48 : $i]:
% 1.32/1.52         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('154', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (m1_subset_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ 
% 1.32/1.52          (k1_zfmisc_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['152', '153'])).
% 1.32/1.52  thf('155', plain,
% 1.32/1.52      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.32/1.52      inference('simplify', [status(thm)], ['9'])).
% 1.32/1.52  thf('156', plain,
% 1.32/1.52      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 1.32/1.52          | (m1_subset_1 @ (k7_relset_1 @ X60 @ X61 @ X59 @ X62) @ 
% 1.32/1.52             (k1_zfmisc_1 @ X61)))),
% 1.32/1.52      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.32/1.52  thf('157', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.32/1.52          | (m1_subset_1 @ (k7_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2) @ 
% 1.32/1.52             (k1_zfmisc_1 @ X0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['155', '156'])).
% 1.32/1.52  thf('158', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         (m1_subset_1 @ 
% 1.32/1.52          (k7_relset_1 @ k1_xboole_0 @ X1 @ 
% 1.32/1.52           (k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)) @ X2) @ 
% 1.32/1.52          (k1_zfmisc_1 @ X1))),
% 1.32/1.52      inference('sup-', [status(thm)], ['154', '157'])).
% 1.32/1.52  thf('159', plain,
% 1.32/1.52      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.32/1.52      inference('simplify', [status(thm)], ['9'])).
% 1.32/1.52  thf('160', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         ((k7_relset_1 @ X1 @ X0 @ (k1_relat_1 @ k1_xboole_0) @ X2)
% 1.32/1.52           = (k9_relat_1 @ (k1_relat_1 @ k1_xboole_0) @ X2))),
% 1.32/1.52      inference('sup-', [status(thm)], ['149', '150'])).
% 1.32/1.52  thf('161', plain,
% 1.32/1.52      (![X1 : $i, X2 : $i]:
% 1.32/1.52         (m1_subset_1 @ (k9_relat_1 @ (k1_relat_1 @ k1_xboole_0) @ X2) @ 
% 1.32/1.52          (k1_zfmisc_1 @ X1))),
% 1.32/1.52      inference('demod', [status(thm)], ['158', '159', '160'])).
% 1.32/1.52  thf('162', plain,
% 1.32/1.52      (![X46 : $i, X47 : $i]:
% 1.32/1.52         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('163', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (r1_tarski @ (k9_relat_1 @ (k1_relat_1 @ k1_xboole_0) @ X1) @ X0)),
% 1.32/1.52      inference('sup-', [status(thm)], ['161', '162'])).
% 1.32/1.52  thf('164', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 1.32/1.52          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['82', '83'])).
% 1.32/1.52  thf('165', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((k9_relat_1 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 1.32/1.52           = (k1_relat_1 @ k1_xboole_0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['163', '164'])).
% 1.32/1.52  thf('166', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         ((k7_relset_1 @ X1 @ X0 @ (k1_relat_1 @ k1_xboole_0) @ X2)
% 1.32/1.52           = (k1_relat_1 @ k1_xboole_0))),
% 1.32/1.52      inference('demod', [status(thm)], ['151', '165'])).
% 1.32/1.52  thf('167', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.52      inference('condensation', [status(thm)], ['114'])).
% 1.32/1.52  thf('168', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.52      inference('condensation', [status(thm)], ['114'])).
% 1.32/1.52  thf('169', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.32/1.52      inference('demod', [status(thm)], ['166', '167', '168'])).
% 1.32/1.52  thf('170', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (((k1_xboole_0)
% 1.32/1.52            = (k9_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X1) @ X0))
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('demod', [status(thm)], ['146', '169'])).
% 1.32/1.52  thf('171', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_xboole_0) = (k9_relat_1 @ sk_D_1 @ X0))
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup+', [status(thm)], ['141', '170'])).
% 1.32/1.52  thf('172', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_1 @ X0)))),
% 1.32/1.52      inference('simplify', [status(thm)], ['171'])).
% 1.32/1.52  thf('173', plain,
% 1.32/1.52      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_1) @ 
% 1.32/1.52          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.32/1.52      inference('demod', [status(thm)], ['0', '3'])).
% 1.32/1.52  thf('174', plain,
% 1.32/1.52      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 1.32/1.52        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['172', '173'])).
% 1.32/1.52  thf('175', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.32/1.52      inference('demod', [status(thm)], ['136', '137'])).
% 1.32/1.52  thf('176', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 1.32/1.52      inference('demod', [status(thm)], ['174', '175'])).
% 1.32/1.52  thf(t14_funct_1, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.32/1.52       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.32/1.52         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.32/1.52  thf('177', plain,
% 1.32/1.52      (![X51 : $i, X52 : $i]:
% 1.32/1.52         (((k1_relat_1 @ X52) != (k1_tarski @ X51))
% 1.32/1.52          | ((k2_relat_1 @ X52) = (k1_tarski @ (k1_funct_1 @ X52 @ X51)))
% 1.32/1.52          | ~ (v1_funct_1 @ X52)
% 1.32/1.52          | ~ (v1_relat_1 @ X52))),
% 1.32/1.52      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.32/1.52  thf('178', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_1))
% 1.32/1.52          | ~ (v1_relat_1 @ X0)
% 1.32/1.52          | ~ (v1_funct_1 @ X0)
% 1.32/1.52          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['176', '177'])).
% 1.32/1.52  thf('179', plain,
% 1.32/1.52      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 1.32/1.52        | ~ (v1_funct_1 @ sk_D_1)
% 1.32/1.52        | ~ (v1_relat_1 @ sk_D_1))),
% 1.32/1.52      inference('eq_res', [status(thm)], ['178'])).
% 1.32/1.52  thf('180', plain, ((v1_funct_1 @ sk_D_1)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('181', plain, ((v1_relat_1 @ sk_D_1)),
% 1.32/1.52      inference('sup-', [status(thm)], ['43', '44'])).
% 1.32/1.52  thf('182', plain,
% 1.32/1.52      (((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.32/1.52      inference('demod', [status(thm)], ['179', '180', '181'])).
% 1.32/1.52  thf('183', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.32/1.52      inference('simplify', [status(thm)], ['5'])).
% 1.32/1.52  thf('184', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 1.32/1.52      inference('demod', [status(thm)], ['42', '45'])).
% 1.32/1.52  thf('185', plain,
% 1.32/1.52      (![X71 : $i]:
% 1.32/1.52         ((m1_subset_1 @ X71 @ 
% 1.32/1.52           (k1_zfmisc_1 @ 
% 1.32/1.52            (k2_zfmisc_1 @ (k1_relat_1 @ X71) @ (k2_relat_1 @ X71))))
% 1.32/1.52          | ~ (v1_funct_1 @ X71)
% 1.32/1.52          | ~ (v1_relat_1 @ X71))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.32/1.52  thf('186', plain,
% 1.32/1.52      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 1.32/1.52         (~ (r1_tarski @ (k1_relat_1 @ X67) @ X68)
% 1.32/1.52          | (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 1.32/1.52          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X69))))),
% 1.32/1.52      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.32/1.52  thf('187', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_relat_1 @ X0)
% 1.32/1.52          | ~ (v1_funct_1 @ X0)
% 1.32/1.52          | (m1_subset_1 @ X0 @ 
% 1.32/1.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ X0))))
% 1.32/1.52          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 1.32/1.52      inference('sup-', [status(thm)], ['185', '186'])).
% 1.32/1.52  thf('188', plain,
% 1.32/1.52      (((m1_subset_1 @ sk_D_1 @ 
% 1.32/1.52         (k1_zfmisc_1 @ 
% 1.32/1.52          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_1))))
% 1.32/1.52        | ~ (v1_funct_1 @ sk_D_1)
% 1.32/1.52        | ~ (v1_relat_1 @ sk_D_1))),
% 1.32/1.52      inference('sup-', [status(thm)], ['184', '187'])).
% 1.32/1.52  thf('189', plain, ((v1_funct_1 @ sk_D_1)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('190', plain, ((v1_relat_1 @ sk_D_1)),
% 1.32/1.52      inference('sup-', [status(thm)], ['43', '44'])).
% 1.32/1.52  thf('191', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_D_1 @ 
% 1.32/1.52        (k1_zfmisc_1 @ 
% 1.32/1.52         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_1))))),
% 1.32/1.52      inference('demod', [status(thm)], ['188', '189', '190'])).
% 1.32/1.52  thf('192', plain,
% 1.32/1.52      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 1.32/1.52         (~ (r1_tarski @ (k1_relat_1 @ X67) @ X68)
% 1.32/1.52          | (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 1.32/1.52          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X69))))),
% 1.32/1.52      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.32/1.52  thf('193', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((m1_subset_1 @ sk_D_1 @ 
% 1.32/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_D_1))))
% 1.32/1.52          | ~ (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['191', '192'])).
% 1.32/1.52  thf('194', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_D_1 @ 
% 1.32/1.52        (k1_zfmisc_1 @ 
% 1.32/1.52         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['183', '193'])).
% 1.32/1.52  thf('195', plain,
% 1.32/1.52      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 1.32/1.52          | ((k7_relset_1 @ X64 @ X65 @ X63 @ X66) = (k9_relat_1 @ X63 @ X66)))),
% 1.32/1.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.32/1.52  thf('196', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1) @ 
% 1.32/1.52           sk_D_1 @ X0) = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['194', '195'])).
% 1.32/1.52  thf('197', plain,
% 1.32/1.52      (![X71 : $i]:
% 1.32/1.52         ((m1_subset_1 @ X71 @ 
% 1.32/1.52           (k1_zfmisc_1 @ 
% 1.32/1.52            (k2_zfmisc_1 @ (k1_relat_1 @ X71) @ (k2_relat_1 @ X71))))
% 1.32/1.52          | ~ (v1_funct_1 @ X71)
% 1.32/1.52          | ~ (v1_relat_1 @ X71))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.32/1.52  thf('198', plain,
% 1.32/1.52      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 1.32/1.52          | (m1_subset_1 @ (k7_relset_1 @ X60 @ X61 @ X59 @ X62) @ 
% 1.32/1.52             (k1_zfmisc_1 @ X61)))),
% 1.32/1.52      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.32/1.52  thf('199', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_relat_1 @ X0)
% 1.32/1.52          | ~ (v1_funct_1 @ X0)
% 1.32/1.52          | (m1_subset_1 @ 
% 1.32/1.52             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 1.32/1.52             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['197', '198'])).
% 1.32/1.52  thf('200', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((m1_subset_1 @ (k9_relat_1 @ sk_D_1 @ X0) @ 
% 1.32/1.52           (k1_zfmisc_1 @ (k2_relat_1 @ sk_D_1)))
% 1.32/1.52          | ~ (v1_funct_1 @ sk_D_1)
% 1.32/1.52          | ~ (v1_relat_1 @ sk_D_1))),
% 1.32/1.52      inference('sup+', [status(thm)], ['196', '199'])).
% 1.32/1.52  thf('201', plain, ((v1_funct_1 @ sk_D_1)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('202', plain, ((v1_relat_1 @ sk_D_1)),
% 1.32/1.52      inference('sup-', [status(thm)], ['43', '44'])).
% 1.32/1.52  thf('203', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (m1_subset_1 @ (k9_relat_1 @ sk_D_1 @ X0) @ 
% 1.32/1.52          (k1_zfmisc_1 @ (k2_relat_1 @ sk_D_1)))),
% 1.32/1.52      inference('demod', [status(thm)], ['200', '201', '202'])).
% 1.32/1.52  thf('204', plain,
% 1.32/1.52      (![X46 : $i, X47 : $i]:
% 1.32/1.52         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('205', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))),
% 1.32/1.52      inference('sup-', [status(thm)], ['203', '204'])).
% 1.32/1.52  thf('206', plain, ($false),
% 1.32/1.52      inference('demod', [status(thm)], ['4', '182', '205'])).
% 1.32/1.52  
% 1.32/1.52  % SZS output end Refutation
% 1.32/1.52  
% 1.32/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
