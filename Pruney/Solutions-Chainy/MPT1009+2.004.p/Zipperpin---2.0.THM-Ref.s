%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rz2wUVP8wQ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:48 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  203 (1058 expanded)
%              Number of leaves         :   49 ( 343 expanded)
%              Depth                    :   31
%              Number of atoms          : 1658 (10242 expanded)
%              Number of equality atoms :  151 ( 774 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_2 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ( ( k7_relset_1 @ X62 @ X63 @ X61 @ X64 )
        = ( k9_relat_1 @ X61 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k11_relat_1 @ X25 @ X26 )
        = ( k9_relat_1 @ X25 @ ( k1_tarski @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( v4_relat_1 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_A ) ),
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
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( v1_relat_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13
        = ( k1_tarski @ X12 ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
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

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('19',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_2 ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_2 ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X52 @ ( k1_relat_1 @ X53 ) )
      | ~ ( r2_hidden @ X54 @ ( k1_relat_1 @ X53 ) )
      | ( ( k9_relat_1 @ X53 @ ( k2_tarski @ X52 @ X54 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X53 @ X52 ) @ ( k1_funct_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( ( k9_relat_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('26',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_A ) )
      = ( k2_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( ( k9_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k11_relat_1 @ sk_D_2 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('35',plain,
    ( ( ( k11_relat_1 @ sk_D_2 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ sk_C ) @ ( k11_relat_1 @ sk_D_2 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k11_relat_1 @ X25 @ X26 )
        = ( k9_relat_1 @ X25 @ ( k1_tarski @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('41',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X33 @ X34 ) @ ( k9_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ X0 ) @ ( k11_relat_1 @ sk_D_2 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ X0 ) @ ( k11_relat_1 @ sk_D_2 @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X33 @ X34 ) @ ( k9_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ( ( k9_relat_1 @ sk_D_2 @ ( k1_relat_1 @ sk_D_2 ) )
        = ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

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

thf('51',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X44 @ X45 @ X46 ) @ X44 )
      | ( zip_tseitin_0 @ ( sk_E @ X44 @ X45 @ X46 ) @ ( sk_D_1 @ X44 @ X45 @ X46 ) @ X45 @ X46 )
      | ( X44
        = ( k9_relat_1 @ X46 @ X45 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ X40 @ X42 )
      | ~ ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('54',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('55',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X35 ) )
      | ( ( k11_relat_1 @ X35 @ X36 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X17: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('59',plain,(
    ! [X29: $i,X30: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('63',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X31 @ X32 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('67',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k11_relat_1 @ X25 @ X26 )
        = ( k9_relat_1 @ X25 @ ( k1_tarski @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','78'])).

thf('80',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('81',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X44 @ X45 @ X46 ) @ X44 )
      | ( zip_tseitin_0 @ ( sk_E @ X44 @ X45 @ X46 ) @ ( sk_D_1 @ X44 @ X45 @ X46 ) @ X45 @ X46 )
      | ( X44
        = ( k9_relat_1 @ X46 @ X45 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('83',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ X40 @ ( k1_relat_1 @ X39 ) )
      | ~ ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('86',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('87',plain,(
    ! [X3: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( X7 = X6 )
      | ( X7 = X3 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('88',plain,(
    ! [X3: $i,X6: $i,X7: $i] :
      ( ( X7 = X3 )
      | ( X7 = X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ sk_D_2 ) @ X1 )
      | ( X1
        = ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( ( sk_E @ X1 @ X0 @ sk_D_2 )
        = sk_A )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ sk_D_2 ) @ X1 )
      | ( X1
        = ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ( ( sk_E @ X1 @ X0 @ sk_D_2 )
        = sk_A )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( sk_E @ k1_xboole_0 @ X0 @ sk_D_2 )
        = sk_A )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','78'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('101',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ( v4_relat_1 @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X1 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( v4_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('107',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X1 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ( v4_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D_2 @ X0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v4_relat_1 @ X27 @ X28 )
      | ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('118',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( v4_relat_1 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v4_relat_1 @ X27 @ X28 )
      | ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X29: $i,X30: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ sk_D_2 )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['114','126'])).

thf('128',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X35 ) )
      | ( ( k11_relat_1 @ X35 @ X36 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_D_2 ) )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) )
      | ( ( k11_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) @ X1 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X29: $i,X30: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_D_2 ) )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) )
      | ( ( k11_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) @ X1 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['81','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['79','135'])).

thf('137',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X33 @ X34 ) @ ( k9_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('141',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) )
      | ( ( k9_relat_1 @ sk_D_2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( k1_xboole_0
    = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('147',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['37','45'])).

thf('148',plain,
    ( k1_xboole_0
    = ( k9_relat_1 @ sk_D_2 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['144'])).

thf('149',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('150',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','145','146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('152',plain,(
    $false ),
    inference(demod,[status(thm)],['4','150','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rz2wUVP8wQ
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.71/1.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.71/1.96  % Solved by: fo/fo7.sh
% 1.71/1.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.71/1.96  % done 1869 iterations in 1.501s
% 1.71/1.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.71/1.96  % SZS output start Refutation
% 1.71/1.96  thf(sk_B_type, type, sk_B: $i).
% 1.71/1.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.71/1.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.71/1.96  thf(sk_A_type, type, sk_A: $i).
% 1.71/1.96  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.71/1.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.71/1.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.71/1.96  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 1.71/1.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.71/1.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.71/1.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.71/1.96  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.71/1.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.71/1.96  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.71/1.96  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.71/1.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.71/1.96  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 1.71/1.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.71/1.96  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.71/1.96  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.71/1.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.71/1.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.71/1.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.71/1.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.71/1.96  thf(sk_C_type, type, sk_C: $i).
% 1.71/1.96  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.71/1.96  thf(t64_funct_2, conjecture,
% 1.71/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.71/1.96     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.71/1.96         ( m1_subset_1 @
% 1.71/1.96           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.71/1.96       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.71/1.96         ( r1_tarski @
% 1.71/1.96           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.71/1.96           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 1.71/1.96  thf(zf_stmt_0, negated_conjecture,
% 1.71/1.96    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.71/1.96        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.71/1.96            ( m1_subset_1 @
% 1.71/1.96              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.71/1.96          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.71/1.96            ( r1_tarski @
% 1.71/1.96              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.71/1.96              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 1.71/1.96    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 1.71/1.96  thf('0', plain,
% 1.71/1.96      (~ (r1_tarski @ 
% 1.71/1.96          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_2 @ sk_C) @ 
% 1.71/1.96          (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.96  thf('1', plain,
% 1.71/1.96      ((m1_subset_1 @ sk_D_2 @ 
% 1.71/1.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.96  thf(redefinition_k7_relset_1, axiom,
% 1.71/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.71/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.71/1.96       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.71/1.96  thf('2', plain,
% 1.71/1.96      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 1.71/1.96         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 1.71/1.96          | ((k7_relset_1 @ X62 @ X63 @ X61 @ X64) = (k9_relat_1 @ X61 @ X64)))),
% 1.71/1.96      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.71/1.96  thf('3', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_2 @ X0)
% 1.71/1.96           = (k9_relat_1 @ sk_D_2 @ X0))),
% 1.71/1.96      inference('sup-', [status(thm)], ['1', '2'])).
% 1.71/1.96  thf('4', plain,
% 1.71/1.96      (~ (r1_tarski @ (k9_relat_1 @ sk_D_2 @ sk_C) @ 
% 1.71/1.96          (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))),
% 1.71/1.96      inference('demod', [status(thm)], ['0', '3'])).
% 1.71/1.96  thf(d16_relat_1, axiom,
% 1.71/1.96    (![A:$i]:
% 1.71/1.96     ( ( v1_relat_1 @ A ) =>
% 1.71/1.96       ( ![B:$i]:
% 1.71/1.96         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 1.71/1.96  thf('5', plain,
% 1.71/1.96      (![X25 : $i, X26 : $i]:
% 1.71/1.96         (((k11_relat_1 @ X25 @ X26) = (k9_relat_1 @ X25 @ (k1_tarski @ X26)))
% 1.71/1.96          | ~ (v1_relat_1 @ X25))),
% 1.71/1.96      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.71/1.96  thf('6', plain,
% 1.71/1.96      ((m1_subset_1 @ sk_D_2 @ 
% 1.71/1.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.96  thf(cc2_relset_1, axiom,
% 1.71/1.96    (![A:$i,B:$i,C:$i]:
% 1.71/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.71/1.96       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.71/1.96  thf('7', plain,
% 1.71/1.96      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.71/1.96         ((v4_relat_1 @ X58 @ X59)
% 1.71/1.96          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 1.71/1.96      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.71/1.96  thf('8', plain, ((v4_relat_1 @ sk_D_2 @ (k1_tarski @ sk_A))),
% 1.71/1.96      inference('sup-', [status(thm)], ['6', '7'])).
% 1.71/1.96  thf(d18_relat_1, axiom,
% 1.71/1.96    (![A:$i,B:$i]:
% 1.71/1.96     ( ( v1_relat_1 @ B ) =>
% 1.71/1.96       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.71/1.96  thf('9', plain,
% 1.71/1.96      (![X27 : $i, X28 : $i]:
% 1.71/1.96         (~ (v4_relat_1 @ X27 @ X28)
% 1.71/1.96          | (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 1.71/1.96          | ~ (v1_relat_1 @ X27))),
% 1.71/1.96      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.71/1.96  thf('10', plain,
% 1.71/1.96      ((~ (v1_relat_1 @ sk_D_2)
% 1.71/1.96        | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (k1_tarski @ sk_A)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['8', '9'])).
% 1.71/1.96  thf('11', plain,
% 1.71/1.96      ((m1_subset_1 @ sk_D_2 @ 
% 1.71/1.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.96  thf(cc1_relset_1, axiom,
% 1.71/1.96    (![A:$i,B:$i,C:$i]:
% 1.71/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.71/1.96       ( v1_relat_1 @ C ) ))).
% 1.71/1.96  thf('12', plain,
% 1.71/1.96      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.71/1.96         ((v1_relat_1 @ X55)
% 1.71/1.96          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 1.71/1.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.71/1.96  thf('13', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ (k1_tarski @ sk_A))),
% 1.71/1.96      inference('demod', [status(thm)], ['10', '13'])).
% 1.71/1.96  thf(l3_zfmisc_1, axiom,
% 1.71/1.96    (![A:$i,B:$i]:
% 1.71/1.96     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.71/1.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.71/1.96  thf('15', plain,
% 1.71/1.96      (![X12 : $i, X13 : $i]:
% 1.71/1.96         (((X13) = (k1_tarski @ X12))
% 1.71/1.96          | ((X13) = (k1_xboole_0))
% 1.71/1.96          | ~ (r1_tarski @ X13 @ (k1_tarski @ X12)))),
% 1.71/1.96      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.71/1.96  thf('16', plain,
% 1.71/1.96      ((((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_tarski @ sk_A)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['14', '15'])).
% 1.71/1.96  thf(t69_enumset1, axiom,
% 1.71/1.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.71/1.96  thf('17', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.71/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.71/1.96  thf(d2_tarski, axiom,
% 1.71/1.96    (![A:$i,B:$i,C:$i]:
% 1.71/1.96     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.71/1.96       ( ![D:$i]:
% 1.71/1.96         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.71/1.96  thf('18', plain,
% 1.71/1.96      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.71/1.96         (((X4) != (X3))
% 1.71/1.96          | (r2_hidden @ X4 @ X5)
% 1.71/1.96          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 1.71/1.96      inference('cnf', [status(esa)], [d2_tarski])).
% 1.71/1.96  thf('19', plain,
% 1.71/1.96      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 1.71/1.96      inference('simplify', [status(thm)], ['18'])).
% 1.71/1.96  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.71/1.96      inference('sup+', [status(thm)], ['17', '19'])).
% 1.71/1.96  thf('21', plain,
% 1.71/1.96      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_2))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('sup+', [status(thm)], ['16', '20'])).
% 1.71/1.96  thf('22', plain,
% 1.71/1.96      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_2))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('sup+', [status(thm)], ['16', '20'])).
% 1.71/1.96  thf(t118_funct_1, axiom,
% 1.71/1.96    (![A:$i,B:$i,C:$i]:
% 1.71/1.96     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.71/1.96       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.71/1.96           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 1.71/1.96         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 1.71/1.96           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 1.71/1.96  thf('23', plain,
% 1.71/1.96      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X52 @ (k1_relat_1 @ X53))
% 1.71/1.96          | ~ (r2_hidden @ X54 @ (k1_relat_1 @ X53))
% 1.71/1.96          | ((k9_relat_1 @ X53 @ (k2_tarski @ X52 @ X54))
% 1.71/1.96              = (k2_tarski @ (k1_funct_1 @ X53 @ X52) @ 
% 1.71/1.96                 (k1_funct_1 @ X53 @ X54)))
% 1.71/1.96          | ~ (v1_funct_1 @ X53)
% 1.71/1.96          | ~ (v1_relat_1 @ X53))),
% 1.71/1.96      inference('cnf', [status(esa)], [t118_funct_1])).
% 1.71/1.96  thf('24', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2)
% 1.71/1.96          | ~ (v1_funct_1 @ sk_D_2)
% 1.71/1.96          | ((k9_relat_1 @ sk_D_2 @ (k2_tarski @ sk_A @ X0))
% 1.71/1.96              = (k2_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A) @ 
% 1.71/1.96                 (k1_funct_1 @ sk_D_2 @ X0)))
% 1.71/1.96          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['22', '23'])).
% 1.71/1.96  thf('25', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('26', plain, ((v1_funct_1 @ sk_D_2)),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.96  thf('27', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96          | ((k9_relat_1 @ sk_D_2 @ (k2_tarski @ sk_A @ X0))
% 1.71/1.96              = (k2_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A) @ 
% 1.71/1.96                 (k1_funct_1 @ sk_D_2 @ X0)))
% 1.71/1.96          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2)))),
% 1.71/1.96      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.71/1.96  thf('28', plain,
% 1.71/1.96      ((((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96        | ((k9_relat_1 @ sk_D_2 @ (k2_tarski @ sk_A @ sk_A))
% 1.71/1.96            = (k2_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A) @ 
% 1.71/1.96               (k1_funct_1 @ sk_D_2 @ sk_A)))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['21', '27'])).
% 1.71/1.96  thf('29', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.71/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.71/1.96  thf('30', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.71/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.71/1.96  thf('31', plain,
% 1.71/1.96      ((((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96        | ((k9_relat_1 @ sk_D_2 @ (k1_tarski @ sk_A))
% 1.71/1.96            = (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.71/1.96  thf('32', plain,
% 1.71/1.96      ((((k9_relat_1 @ sk_D_2 @ (k1_tarski @ sk_A))
% 1.71/1.96          = (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('simplify', [status(thm)], ['31'])).
% 1.71/1.96  thf('33', plain,
% 1.71/1.96      ((((k11_relat_1 @ sk_D_2 @ sk_A)
% 1.71/1.96          = (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))
% 1.71/1.96        | ~ (v1_relat_1 @ sk_D_2)
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('sup+', [status(thm)], ['5', '32'])).
% 1.71/1.96  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('35', plain,
% 1.71/1.96      ((((k11_relat_1 @ sk_D_2 @ sk_A)
% 1.71/1.96          = (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('demod', [status(thm)], ['33', '34'])).
% 1.71/1.96  thf('36', plain,
% 1.71/1.96      (~ (r1_tarski @ (k9_relat_1 @ sk_D_2 @ sk_C) @ 
% 1.71/1.96          (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))),
% 1.71/1.96      inference('demod', [status(thm)], ['0', '3'])).
% 1.71/1.96  thf('37', plain,
% 1.71/1.96      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_2 @ sk_C) @ 
% 1.71/1.96           (k11_relat_1 @ sk_D_2 @ sk_A))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['35', '36'])).
% 1.71/1.96  thf('38', plain,
% 1.71/1.96      ((((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_tarski @ sk_A)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['14', '15'])).
% 1.71/1.96  thf('39', plain,
% 1.71/1.96      (![X25 : $i, X26 : $i]:
% 1.71/1.96         (((k11_relat_1 @ X25 @ X26) = (k9_relat_1 @ X25 @ (k1_tarski @ X26)))
% 1.71/1.96          | ~ (v1_relat_1 @ X25))),
% 1.71/1.96      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.71/1.96  thf('40', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k11_relat_1 @ X0 @ sk_A)
% 1.71/1.96            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D_2)))
% 1.71/1.96          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96          | ~ (v1_relat_1 @ X0))),
% 1.71/1.96      inference('sup+', [status(thm)], ['38', '39'])).
% 1.71/1.96  thf(t147_relat_1, axiom,
% 1.71/1.96    (![A:$i,B:$i]:
% 1.71/1.96     ( ( v1_relat_1 @ B ) =>
% 1.71/1.96       ( r1_tarski @
% 1.71/1.96         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 1.71/1.96  thf('41', plain,
% 1.71/1.96      (![X33 : $i, X34 : $i]:
% 1.71/1.96         ((r1_tarski @ (k9_relat_1 @ X33 @ X34) @ 
% 1.71/1.96           (k9_relat_1 @ X33 @ (k1_relat_1 @ X33)))
% 1.71/1.96          | ~ (v1_relat_1 @ X33))),
% 1.71/1.96      inference('cnf', [status(esa)], [t147_relat_1])).
% 1.71/1.96  thf('42', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         ((r1_tarski @ (k9_relat_1 @ sk_D_2 @ X0) @ 
% 1.71/1.96           (k11_relat_1 @ sk_D_2 @ sk_A))
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2)
% 1.71/1.96          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2))),
% 1.71/1.96      inference('sup+', [status(thm)], ['40', '41'])).
% 1.71/1.96  thf('43', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('44', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('45', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         ((r1_tarski @ (k9_relat_1 @ sk_D_2 @ X0) @ 
% 1.71/1.96           (k11_relat_1 @ sk_D_2 @ sk_A))
% 1.71/1.96          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('demod', [status(thm)], ['42', '43', '44'])).
% 1.71/1.96  thf('46', plain, (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))),
% 1.71/1.96      inference('clc', [status(thm)], ['37', '45'])).
% 1.71/1.96  thf('47', plain,
% 1.71/1.96      (![X33 : $i, X34 : $i]:
% 1.71/1.96         ((r1_tarski @ (k9_relat_1 @ X33 @ X34) @ 
% 1.71/1.96           (k9_relat_1 @ X33 @ (k1_relat_1 @ X33)))
% 1.71/1.96          | ~ (v1_relat_1 @ X33))),
% 1.71/1.96      inference('cnf', [status(esa)], [t147_relat_1])).
% 1.71/1.96  thf(d10_xboole_0, axiom,
% 1.71/1.96    (![A:$i,B:$i]:
% 1.71/1.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.71/1.96  thf('48', plain,
% 1.71/1.96      (![X0 : $i, X2 : $i]:
% 1.71/1.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.71/1.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.71/1.96  thf('49', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         (~ (v1_relat_1 @ X0)
% 1.71/1.96          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 1.71/1.96               (k9_relat_1 @ X0 @ X1))
% 1.71/1.96          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k9_relat_1 @ X0 @ X1)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['47', '48'])).
% 1.71/1.96  thf('50', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (~ (r1_tarski @ (k9_relat_1 @ sk_D_2 @ k1_xboole_0) @ 
% 1.71/1.96             (k9_relat_1 @ sk_D_2 @ X0))
% 1.71/1.96          | ((k9_relat_1 @ sk_D_2 @ (k1_relat_1 @ sk_D_2))
% 1.71/1.96              = (k9_relat_1 @ sk_D_2 @ X0))
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2))),
% 1.71/1.96      inference('sup-', [status(thm)], ['46', '49'])).
% 1.71/1.96  thf(d12_funct_1, axiom,
% 1.71/1.96    (![A:$i]:
% 1.71/1.96     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 1.71/1.96       ( ![B:$i,C:$i]:
% 1.71/1.96         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.71/1.96           ( ![D:$i]:
% 1.71/1.96             ( ( r2_hidden @ D @ C ) <=>
% 1.71/1.96               ( ?[E:$i]:
% 1.71/1.96                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 1.71/1.96                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 1.71/1.96  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.71/1.96  thf(zf_stmt_2, axiom,
% 1.71/1.96    (![E:$i,D:$i,B:$i,A:$i]:
% 1.71/1.96     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 1.71/1.96       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 1.71/1.96         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 1.71/1.96  thf(zf_stmt_3, axiom,
% 1.71/1.96    (![A:$i]:
% 1.71/1.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.71/1.96       ( ![B:$i,C:$i]:
% 1.71/1.96         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.71/1.96           ( ![D:$i]:
% 1.71/1.96             ( ( r2_hidden @ D @ C ) <=>
% 1.71/1.96               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 1.71/1.96  thf('51', plain,
% 1.71/1.96      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.71/1.96         ((r2_hidden @ (sk_D_1 @ X44 @ X45 @ X46) @ X44)
% 1.71/1.96          | (zip_tseitin_0 @ (sk_E @ X44 @ X45 @ X46) @ 
% 1.71/1.96             (sk_D_1 @ X44 @ X45 @ X46) @ X45 @ X46)
% 1.71/1.96          | ((X44) = (k9_relat_1 @ X46 @ X45))
% 1.71/1.96          | ~ (v1_funct_1 @ X46)
% 1.71/1.96          | ~ (v1_relat_1 @ X46))),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.71/1.96  thf('52', plain,
% 1.71/1.96      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.71/1.96         ((r2_hidden @ X40 @ X42) | ~ (zip_tseitin_0 @ X40 @ X41 @ X42 @ X39))),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.71/1.96  thf('53', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.96         (~ (v1_relat_1 @ X0)
% 1.71/1.96          | ~ (v1_funct_1 @ X0)
% 1.71/1.96          | ((X2) = (k9_relat_1 @ X0 @ X1))
% 1.71/1.96          | (r2_hidden @ (sk_D_1 @ X2 @ X1 @ X0) @ X2)
% 1.71/1.96          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X1))),
% 1.71/1.96      inference('sup-', [status(thm)], ['51', '52'])).
% 1.71/1.96  thf(t60_relat_1, axiom,
% 1.71/1.96    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.71/1.96     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.71/1.96  thf('54', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.71/1.96      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.71/1.96  thf(t205_relat_1, axiom,
% 1.71/1.96    (![A:$i,B:$i]:
% 1.71/1.96     ( ( v1_relat_1 @ B ) =>
% 1.71/1.96       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 1.71/1.96         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 1.71/1.96  thf('55', plain,
% 1.71/1.96      (![X35 : $i, X36 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X36 @ (k1_relat_1 @ X35))
% 1.71/1.96          | ((k11_relat_1 @ X35 @ X36) != (k1_xboole_0))
% 1.71/1.96          | ~ (v1_relat_1 @ X35))),
% 1.71/1.96      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.71/1.96  thf('56', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.71/1.96          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.71/1.96          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['54', '55'])).
% 1.71/1.96  thf(t113_zfmisc_1, axiom,
% 1.71/1.96    (![A:$i,B:$i]:
% 1.71/1.96     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.71/1.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.71/1.96  thf('57', plain,
% 1.71/1.96      (![X16 : $i, X17 : $i]:
% 1.71/1.96         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 1.71/1.96          | ((X16) != (k1_xboole_0)))),
% 1.71/1.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.71/1.96  thf('58', plain,
% 1.71/1.96      (![X17 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 1.71/1.96      inference('simplify', [status(thm)], ['57'])).
% 1.71/1.96  thf(fc6_relat_1, axiom,
% 1.71/1.96    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.71/1.96  thf('59', plain,
% 1.71/1.96      (![X29 : $i, X30 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X29 @ X30))),
% 1.71/1.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.71/1.96  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.71/1.96      inference('sup+', [status(thm)], ['58', '59'])).
% 1.71/1.96  thf('61', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.71/1.96          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 1.71/1.96      inference('demod', [status(thm)], ['56', '60'])).
% 1.71/1.96  thf('62', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.71/1.96      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.71/1.96  thf(t144_relat_1, axiom,
% 1.71/1.96    (![A:$i,B:$i]:
% 1.71/1.96     ( ( v1_relat_1 @ B ) =>
% 1.71/1.96       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 1.71/1.96  thf('63', plain,
% 1.71/1.96      (![X31 : $i, X32 : $i]:
% 1.71/1.96         ((r1_tarski @ (k9_relat_1 @ X31 @ X32) @ (k2_relat_1 @ X31))
% 1.71/1.96          | ~ (v1_relat_1 @ X31))),
% 1.71/1.96      inference('cnf', [status(esa)], [t144_relat_1])).
% 1.71/1.96  thf('64', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 1.71/1.96          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.71/1.96      inference('sup+', [status(thm)], ['62', '63'])).
% 1.71/1.96  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.71/1.96      inference('sup+', [status(thm)], ['58', '59'])).
% 1.71/1.96  thf('66', plain,
% 1.71/1.96      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 1.71/1.96      inference('demod', [status(thm)], ['64', '65'])).
% 1.71/1.96  thf(t4_subset_1, axiom,
% 1.71/1.96    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.71/1.96  thf('67', plain,
% 1.71/1.96      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 1.71/1.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.71/1.96  thf(t3_subset, axiom,
% 1.71/1.96    (![A:$i,B:$i]:
% 1.71/1.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.71/1.96  thf('68', plain,
% 1.71/1.96      (![X19 : $i, X20 : $i]:
% 1.71/1.96         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.71/1.96      inference('cnf', [status(esa)], [t3_subset])).
% 1.71/1.96  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.71/1.96      inference('sup-', [status(thm)], ['67', '68'])).
% 1.71/1.96  thf('70', plain,
% 1.71/1.96      (![X0 : $i, X2 : $i]:
% 1.71/1.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.71/1.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.71/1.96  thf('71', plain,
% 1.71/1.96      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['69', '70'])).
% 1.71/1.96  thf('72', plain,
% 1.71/1.96      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.71/1.96      inference('sup-', [status(thm)], ['66', '71'])).
% 1.71/1.96  thf('73', plain,
% 1.71/1.96      (![X25 : $i, X26 : $i]:
% 1.71/1.96         (((k11_relat_1 @ X25 @ X26) = (k9_relat_1 @ X25 @ (k1_tarski @ X26)))
% 1.71/1.96          | ~ (v1_relat_1 @ X25))),
% 1.71/1.96      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.71/1.96  thf('74', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 1.71/1.96          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.71/1.96      inference('sup+', [status(thm)], ['72', '73'])).
% 1.71/1.96  thf('75', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.71/1.96      inference('sup+', [status(thm)], ['58', '59'])).
% 1.71/1.96  thf('76', plain,
% 1.71/1.96      (![X0 : $i]: ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.71/1.96      inference('demod', [status(thm)], ['74', '75'])).
% 1.71/1.96  thf('77', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X0 @ k1_xboole_0) | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.71/1.96      inference('demod', [status(thm)], ['61', '76'])).
% 1.71/1.96  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.71/1.96      inference('simplify', [status(thm)], ['77'])).
% 1.71/1.96  thf('79', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ X0 @ X1))
% 1.71/1.96          | ~ (v1_funct_1 @ X0)
% 1.71/1.96          | ~ (v1_relat_1 @ X0))),
% 1.71/1.96      inference('sup-', [status(thm)], ['53', '78'])).
% 1.71/1.96  thf('80', plain,
% 1.71/1.96      (![X16 : $i, X17 : $i]:
% 1.71/1.96         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 1.71/1.96          | ((X17) != (k1_xboole_0)))),
% 1.71/1.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.71/1.96  thf('81', plain,
% 1.71/1.96      (![X16 : $i]: ((k2_zfmisc_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 1.71/1.96      inference('simplify', [status(thm)], ['80'])).
% 1.71/1.96  thf('82', plain,
% 1.71/1.96      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.71/1.96         ((r2_hidden @ (sk_D_1 @ X44 @ X45 @ X46) @ X44)
% 1.71/1.96          | (zip_tseitin_0 @ (sk_E @ X44 @ X45 @ X46) @ 
% 1.71/1.96             (sk_D_1 @ X44 @ X45 @ X46) @ X45 @ X46)
% 1.71/1.96          | ((X44) = (k9_relat_1 @ X46 @ X45))
% 1.71/1.96          | ~ (v1_funct_1 @ X46)
% 1.71/1.96          | ~ (v1_relat_1 @ X46))),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.71/1.96  thf('83', plain,
% 1.71/1.96      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.71/1.96         ((r2_hidden @ X40 @ (k1_relat_1 @ X39))
% 1.71/1.96          | ~ (zip_tseitin_0 @ X40 @ X41 @ X42 @ X39))),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.71/1.96  thf('84', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.96         (~ (v1_relat_1 @ X0)
% 1.71/1.96          | ~ (v1_funct_1 @ X0)
% 1.71/1.96          | ((X2) = (k9_relat_1 @ X0 @ X1))
% 1.71/1.96          | (r2_hidden @ (sk_D_1 @ X2 @ X1 @ X0) @ X2)
% 1.71/1.96          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['82', '83'])).
% 1.71/1.96  thf('85', plain,
% 1.71/1.96      ((((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96        | ((k1_relat_1 @ sk_D_2) = (k1_tarski @ sk_A)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['14', '15'])).
% 1.71/1.96  thf('86', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.71/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.71/1.96  thf('87', plain,
% 1.71/1.96      (![X3 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X7 @ X5)
% 1.71/1.96          | ((X7) = (X6))
% 1.71/1.96          | ((X7) = (X3))
% 1.71/1.96          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 1.71/1.96      inference('cnf', [status(esa)], [d2_tarski])).
% 1.71/1.96  thf('88', plain,
% 1.71/1.96      (![X3 : $i, X6 : $i, X7 : $i]:
% 1.71/1.96         (((X7) = (X3))
% 1.71/1.96          | ((X7) = (X6))
% 1.71/1.96          | ~ (r2_hidden @ X7 @ (k2_tarski @ X6 @ X3)))),
% 1.71/1.96      inference('simplify', [status(thm)], ['87'])).
% 1.71/1.96  thf('89', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['86', '88'])).
% 1.71/1.96  thf('90', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.71/1.96      inference('simplify', [status(thm)], ['89'])).
% 1.71/1.96  thf('91', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2))
% 1.71/1.96          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96          | ((X0) = (sk_A)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['85', '90'])).
% 1.71/1.96  thf('92', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         ((r2_hidden @ (sk_D_1 @ X1 @ X0 @ sk_D_2) @ X1)
% 1.71/1.96          | ((X1) = (k9_relat_1 @ sk_D_2 @ X0))
% 1.71/1.96          | ~ (v1_funct_1 @ sk_D_2)
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2)
% 1.71/1.96          | ((sk_E @ X1 @ X0 @ sk_D_2) = (sk_A))
% 1.71/1.96          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['84', '91'])).
% 1.71/1.96  thf('93', plain, ((v1_funct_1 @ sk_D_2)),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.96  thf('94', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('95', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         ((r2_hidden @ (sk_D_1 @ X1 @ X0 @ sk_D_2) @ X1)
% 1.71/1.96          | ((X1) = (k9_relat_1 @ sk_D_2 @ X0))
% 1.71/1.96          | ((sk_E @ X1 @ X0 @ sk_D_2) = (sk_A))
% 1.71/1.96          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.71/1.96      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.71/1.96  thf('96', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.71/1.96      inference('simplify', [status(thm)], ['77'])).
% 1.71/1.96  thf('97', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96          | ((sk_E @ k1_xboole_0 @ X0 @ sk_D_2) = (sk_A))
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ X0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['95', '96'])).
% 1.71/1.96  thf('98', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ X0 @ X1))
% 1.71/1.96          | ~ (v1_funct_1 @ X0)
% 1.71/1.96          | ~ (v1_relat_1 @ X0))),
% 1.71/1.96      inference('sup-', [status(thm)], ['53', '78'])).
% 1.71/1.96  thf('99', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         ((r2_hidden @ sk_A @ X0)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ X0))
% 1.71/1.96          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2)
% 1.71/1.96          | ~ (v1_funct_1 @ sk_D_2)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ X0)))),
% 1.71/1.96      inference('sup+', [status(thm)], ['97', '98'])).
% 1.71/1.96  thf('100', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('101', plain, ((v1_funct_1 @ sk_D_2)),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.96  thf('102', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         ((r2_hidden @ sk_A @ X0)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ X0))
% 1.71/1.96          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ X0)))),
% 1.71/1.96      inference('demod', [status(thm)], ['99', '100', '101'])).
% 1.71/1.96  thf('103', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ X0))
% 1.71/1.96          | (r2_hidden @ sk_A @ X0))),
% 1.71/1.96      inference('simplify', [status(thm)], ['102'])).
% 1.71/1.96  thf('104', plain,
% 1.71/1.96      (![X27 : $i, X28 : $i]:
% 1.71/1.96         (~ (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 1.71/1.96          | (v4_relat_1 @ X27 @ X28)
% 1.71/1.96          | ~ (v1_relat_1 @ X27))),
% 1.71/1.96      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.71/1.96  thf('105', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.71/1.96          | (r2_hidden @ sk_A @ X1)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ X1))
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2)
% 1.71/1.96          | (v4_relat_1 @ sk_D_2 @ X0))),
% 1.71/1.96      inference('sup-', [status(thm)], ['103', '104'])).
% 1.71/1.96  thf('106', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.71/1.96      inference('sup-', [status(thm)], ['67', '68'])).
% 1.71/1.96  thf('107', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('108', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         ((r2_hidden @ sk_A @ X1)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ X1))
% 1.71/1.96          | (v4_relat_1 @ sk_D_2 @ X0))),
% 1.71/1.96      inference('demod', [status(thm)], ['105', '106', '107'])).
% 1.71/1.96  thf('109', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.71/1.96      inference('simplify', [status(thm)], ['77'])).
% 1.71/1.96  thf('110', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         ((v4_relat_1 @ sk_D_2 @ X0)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['108', '109'])).
% 1.71/1.96  thf('111', plain,
% 1.71/1.96      (![X27 : $i, X28 : $i]:
% 1.71/1.96         (~ (v4_relat_1 @ X27 @ X28)
% 1.71/1.96          | (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 1.71/1.96          | ~ (v1_relat_1 @ X27))),
% 1.71/1.96      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.71/1.96  thf('112', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2)
% 1.71/1.96          | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ X0))),
% 1.71/1.96      inference('sup-', [status(thm)], ['110', '111'])).
% 1.71/1.96  thf('113', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('114', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))
% 1.71/1.96          | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ X0))),
% 1.71/1.96      inference('demod', [status(thm)], ['112', '113'])).
% 1.71/1.96  thf('115', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.71/1.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.71/1.96  thf('116', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.71/1.96      inference('simplify', [status(thm)], ['115'])).
% 1.71/1.96  thf('117', plain,
% 1.71/1.96      (![X19 : $i, X21 : $i]:
% 1.71/1.96         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 1.71/1.96      inference('cnf', [status(esa)], [t3_subset])).
% 1.71/1.96  thf('118', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.71/1.96      inference('sup-', [status(thm)], ['116', '117'])).
% 1.71/1.96  thf('119', plain,
% 1.71/1.96      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.71/1.96         ((v4_relat_1 @ X58 @ X59)
% 1.71/1.96          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 1.71/1.96      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.71/1.96  thf('120', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 1.71/1.96      inference('sup-', [status(thm)], ['118', '119'])).
% 1.71/1.96  thf('121', plain,
% 1.71/1.96      (![X27 : $i, X28 : $i]:
% 1.71/1.96         (~ (v4_relat_1 @ X27 @ X28)
% 1.71/1.96          | (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 1.71/1.96          | ~ (v1_relat_1 @ X27))),
% 1.71/1.96      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.71/1.96  thf('122', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 1.71/1.96          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 1.71/1.96      inference('sup-', [status(thm)], ['120', '121'])).
% 1.71/1.96  thf('123', plain,
% 1.71/1.96      (![X29 : $i, X30 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X29 @ X30))),
% 1.71/1.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.71/1.96  thf('124', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 1.71/1.96      inference('demod', [status(thm)], ['122', '123'])).
% 1.71/1.96  thf('125', plain,
% 1.71/1.96      (![X0 : $i, X2 : $i]:
% 1.71/1.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.71/1.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.71/1.96  thf('126', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 1.71/1.96          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 1.71/1.96      inference('sup-', [status(thm)], ['124', '125'])).
% 1.71/1.96  thf('127', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))
% 1.71/1.96          | ((k1_relat_1 @ sk_D_2)
% 1.71/1.96              = (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ X0))))),
% 1.71/1.96      inference('sup-', [status(thm)], ['114', '126'])).
% 1.71/1.96  thf('128', plain,
% 1.71/1.96      (![X35 : $i, X36 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X36 @ (k1_relat_1 @ X35))
% 1.71/1.96          | ((k11_relat_1 @ X35 @ X36) != (k1_xboole_0))
% 1.71/1.96          | ~ (v1_relat_1 @ X35))),
% 1.71/1.96      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.71/1.96  thf('129', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_D_2))
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))
% 1.71/1.96          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ X0))
% 1.71/1.96          | ((k11_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ X0) @ X1)
% 1.71/1.96              != (k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['127', '128'])).
% 1.71/1.96  thf('130', plain,
% 1.71/1.96      (![X29 : $i, X30 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X29 @ X30))),
% 1.71/1.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.71/1.96  thf('131', plain,
% 1.71/1.96      (![X0 : $i, X1 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_D_2))
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))
% 1.71/1.96          | ((k11_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ X0) @ X1)
% 1.71/1.96              != (k1_xboole_0)))),
% 1.71/1.96      inference('demod', [status(thm)], ['129', '130'])).
% 1.71/1.96  thf('132', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))
% 1.71/1.96          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['81', '131'])).
% 1.71/1.96  thf('133', plain,
% 1.71/1.96      (![X0 : $i]: ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.71/1.96      inference('demod', [status(thm)], ['74', '75'])).
% 1.71/1.96  thf('134', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k1_xboole_0) != (k1_xboole_0))
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))
% 1.71/1.96          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2)))),
% 1.71/1.96      inference('demod', [status(thm)], ['132', '133'])).
% 1.71/1.96  thf('135', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2))
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0)))),
% 1.71/1.96      inference('simplify', [status(thm)], ['134'])).
% 1.71/1.96  thf('136', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (~ (v1_relat_1 @ X0)
% 1.71/1.96          | ~ (v1_funct_1 @ X0)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D_2)))
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['79', '135'])).
% 1.71/1.96  thf('137', plain,
% 1.71/1.96      (![X33 : $i, X34 : $i]:
% 1.71/1.96         ((r1_tarski @ (k9_relat_1 @ X33 @ X34) @ 
% 1.71/1.96           (k9_relat_1 @ X33 @ (k1_relat_1 @ X33)))
% 1.71/1.96          | ~ (v1_relat_1 @ X33))),
% 1.71/1.96      inference('cnf', [status(esa)], [t147_relat_1])).
% 1.71/1.96  thf('138', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         ((r1_tarski @ (k9_relat_1 @ sk_D_2 @ X0) @ k1_xboole_0)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))
% 1.71/1.96          | ~ (v1_funct_1 @ sk_D_2)
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2)
% 1.71/1.96          | ~ (v1_relat_1 @ sk_D_2))),
% 1.71/1.96      inference('sup+', [status(thm)], ['136', '137'])).
% 1.71/1.96  thf('139', plain, ((v1_funct_1 @ sk_D_2)),
% 1.71/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.96  thf('140', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('141', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('142', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         ((r1_tarski @ (k9_relat_1 @ sk_D_2 @ X0) @ k1_xboole_0)
% 1.71/1.96          | ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0)))),
% 1.71/1.96      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 1.71/1.96  thf('143', plain,
% 1.71/1.96      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['69', '70'])).
% 1.71/1.96  thf('144', plain,
% 1.71/1.96      (![X0 : $i]:
% 1.71/1.96         (((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))
% 1.71/1.96          | ((k9_relat_1 @ sk_D_2 @ X0) = (k1_xboole_0)))),
% 1.71/1.96      inference('sup-', [status(thm)], ['142', '143'])).
% 1.71/1.96  thf('145', plain, (((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))),
% 1.71/1.96      inference('condensation', [status(thm)], ['144'])).
% 1.71/1.96  thf('146', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.71/1.96      inference('sup-', [status(thm)], ['67', '68'])).
% 1.71/1.96  thf('147', plain, (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))),
% 1.71/1.96      inference('clc', [status(thm)], ['37', '45'])).
% 1.71/1.96  thf('148', plain, (((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ k1_xboole_0))),
% 1.71/1.96      inference('condensation', [status(thm)], ['144'])).
% 1.71/1.96  thf('149', plain, ((v1_relat_1 @ sk_D_2)),
% 1.71/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.96  thf('150', plain, (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_D_2 @ X0))),
% 1.71/1.96      inference('demod', [status(thm)],
% 1.71/1.96                ['50', '145', '146', '147', '148', '149'])).
% 1.71/1.96  thf('151', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.71/1.96      inference('sup-', [status(thm)], ['67', '68'])).
% 1.71/1.96  thf('152', plain, ($false),
% 1.71/1.96      inference('demod', [status(thm)], ['4', '150', '151'])).
% 1.71/1.96  
% 1.71/1.96  % SZS output end Refutation
% 1.71/1.96  
% 1.71/1.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
