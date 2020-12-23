%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qaI5D52xMy

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:04 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  199 (1610 expanded)
%              Number of leaves         :   52 ( 512 expanded)
%              Depth                    :   32
%              Number of atoms          : 1353 (16614 expanded)
%              Number of equality atoms :   84 ( 675 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
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
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ( ( k7_relset_1 @ X54 @ X55 @ X53 @ X56 )
        = ( k9_relat_1 @ X53 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_D_1 @ X0 ) )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v4_relat_1 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v4_relat_1 @ X32 @ X33 )
      | ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ( v4_relat_1 @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( v4_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
      | ( v4_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k7_relat_1 @ X40 @ X41 ) )
      | ~ ( v4_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( r1_tarski @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X36 @ X37 ) @ ( k2_relat_1 @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
      | ( v4_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D_1 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v4_relat_1 @ X32 @ X33 )
      | ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('63',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','63'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('65',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ X43 ) )
      | ( ( k11_relat_1 @ X43 @ X42 )
        = ( k1_tarski @ ( k1_funct_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('66',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('68',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('69',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k11_relat_1 @ X30 @ X31 )
        = ( k9_relat_1 @ X30 @ ( k1_tarski @ X31 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('70',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('71',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k7_relat_1 @ X40 @ X41 ) )
      | ~ ( v4_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('74',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('76',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k11_relat_1 @ sk_D_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['69','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k11_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','81'])).

thf('83',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('86',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('89',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('91',plain,(
    ! [X0: $i] :
      ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ sk_D_1 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','91'])).

thf('93',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_0 @ D @ C @ B @ A ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( ( k1_relat_1 @ X65 )
       != X64 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X65 @ X66 @ X64 ) @ X65 @ X66 @ X64 )
      | ( zip_tseitin_1 @ X65 @ X66 @ X64 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('96',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( v1_relat_1 @ X65 )
      | ~ ( v1_funct_1 @ X65 )
      | ( zip_tseitin_1 @ X65 @ X66 @ ( k1_relat_1 @ X65 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X65 @ X66 @ ( k1_relat_1 @ X65 ) ) @ X65 @ X66 @ ( k1_relat_1 @ X65 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_D_1 @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('99',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('100',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ k1_xboole_0 ) @ sk_D_1 @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('104',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( zip_tseitin_0 @ X57 @ X58 @ X59 @ X60 )
      | ( r2_hidden @ X57 @ X60 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('105',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( r1_tarski @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X1 @ X3 @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_0 @ X0 @ X2 @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X62 ) ) )
      | ~ ( zip_tseitin_1 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('110',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('111',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_zfmisc_1 @ X19 @ X20 )
        = k1_xboole_0 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('112',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','112'])).

thf('114',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('115',plain,(
    r1_tarski @ sk_D_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('117',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('119',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X50 @ X51 @ X49 @ X52 ) @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('122',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ( ( k7_relset_1 @ X54 @ X55 @ X53 @ X56 )
        = ( k9_relat_1 @ X53 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('125',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v4_relat_1 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('126',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k7_relat_1 @ X40 @ X41 ) )
      | ~ ( v4_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['111'])).

thf('130',plain,(
    ! [X34: $i,X35: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('131',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['129','130'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['123','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','137'])).

thf('139',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('140',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('142',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('144',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['93','117','142','143','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qaI5D52xMy
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:38:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 691 iterations in 0.237s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.48/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.48/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.48/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.48/0.69  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.48/0.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.48/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.48/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.48/0.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.48/0.69  thf(t64_funct_2, conjecture,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.48/0.69         ( m1_subset_1 @
% 0.48/0.69           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.48/0.69       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.69         ( r1_tarski @
% 0.48/0.69           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.48/0.69           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.48/0.69            ( m1_subset_1 @
% 0.48/0.69              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.48/0.69          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.69            ( r1_tarski @
% 0.48/0.69              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.48/0.69              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.48/0.69  thf('0', plain,
% 0.48/0.69      (~ (r1_tarski @ 
% 0.48/0.69          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C_2) @ 
% 0.48/0.69          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('1', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_D_1 @ 
% 0.48/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(redefinition_k7_relset_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.69       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.48/0.69  thf('2', plain,
% 0.48/0.69      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 0.48/0.69          | ((k7_relset_1 @ X54 @ X55 @ X53 @ X56) = (k9_relat_1 @ X53 @ X56)))),
% 0.48/0.69      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.48/0.69  thf('3', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.48/0.69           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.69  thf('4', plain,
% 0.48/0.69      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_2) @ 
% 0.48/0.69          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.48/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.69  thf('5', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_D_1 @ 
% 0.48/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(cc2_relat_1, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ A ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.48/0.69  thf('6', plain,
% 0.48/0.69      (![X28 : $i, X29 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.48/0.69          | (v1_relat_1 @ X28)
% 0.48/0.69          | ~ (v1_relat_1 @ X29))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.69  thf('7', plain,
% 0.48/0.69      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.48/0.69        | (v1_relat_1 @ sk_D_1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.69  thf(fc6_relat_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.48/0.69  thf('8', plain,
% 0.48/0.69      (![X34 : $i, X35 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X34 @ X35))),
% 0.48/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.48/0.69  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.69  thf(t148_relat_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ B ) =>
% 0.48/0.69       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.48/0.69  thf('10', plain,
% 0.48/0.69      (![X38 : $i, X39 : $i]:
% 0.48/0.69         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 0.48/0.69          | ~ (v1_relat_1 @ X38))),
% 0.48/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.48/0.69  thf('11', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_relat_1 @ (k7_relat_1 @ sk_D_1 @ X0))
% 0.48/0.69           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.48/0.69  thf(d3_tarski, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.69  thf('12', plain,
% 0.48/0.69      (![X1 : $i, X3 : $i]:
% 0.48/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('13', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_D_1 @ 
% 0.48/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(cc2_relset_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.48/0.69  thf('14', plain,
% 0.48/0.69      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.48/0.69         ((v4_relat_1 @ X46 @ X47)
% 0.48/0.69          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.69  thf('15', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.69  thf(d18_relat_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ B ) =>
% 0.48/0.69       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.48/0.69  thf('16', plain,
% 0.48/0.69      (![X32 : $i, X33 : $i]:
% 0.48/0.69         (~ (v4_relat_1 @ X32 @ X33)
% 0.48/0.69          | (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.48/0.69          | ~ (v1_relat_1 @ X32))),
% 0.48/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.48/0.69  thf('17', plain,
% 0.48/0.69      ((~ (v1_relat_1 @ sk_D_1)
% 0.48/0.69        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.48/0.69  thf('18', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.69  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.48/0.69      inference('demod', [status(thm)], ['17', '18'])).
% 0.48/0.69  thf('20', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.48/0.69          | (r2_hidden @ X0 @ X2)
% 0.48/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('21', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.48/0.69          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.48/0.69  thf('22', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 0.48/0.69          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) @ 
% 0.48/0.69             (k1_tarski @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['12', '21'])).
% 0.48/0.69  thf(d1_tarski, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.48/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.48/0.69  thf('23', plain,
% 0.48/0.69      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X10 @ X9)
% 0.48/0.69          | ((X10) = (X7))
% 0.48/0.69          | ((X9) != (k1_tarski @ X7)))),
% 0.48/0.69      inference('cnf', [status(esa)], [d1_tarski])).
% 0.48/0.69  thf('24', plain,
% 0.48/0.69      (![X7 : $i, X10 : $i]:
% 0.48/0.69         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.48/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.48/0.69  thf('25', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 0.48/0.69          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) = (sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['22', '24'])).
% 0.48/0.69  thf('26', plain,
% 0.48/0.69      (![X1 : $i, X3 : $i]:
% 0.48/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('27', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.48/0.69          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 0.48/0.69          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.48/0.69  thf('28', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 0.48/0.69          | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1)))),
% 0.48/0.69      inference('simplify', [status(thm)], ['27'])).
% 0.48/0.69  thf('29', plain,
% 0.48/0.69      (![X32 : $i, X33 : $i]:
% 0.48/0.69         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.48/0.69          | (v4_relat_1 @ X32 @ X33)
% 0.48/0.69          | ~ (v1_relat_1 @ X32))),
% 0.48/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.48/0.69  thf('30', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.48/0.69          | ~ (v1_relat_1 @ sk_D_1)
% 0.48/0.69          | (v4_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.69  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.69  thf('32', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.48/0.69          | (v4_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['30', '31'])).
% 0.48/0.69  thf(t209_relat_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.48/0.69       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.48/0.69  thf('33', plain,
% 0.48/0.69      (![X40 : $i, X41 : $i]:
% 0.48/0.69         (((X40) = (k7_relat_1 @ X40 @ X41))
% 0.48/0.69          | ~ (v4_relat_1 @ X40 @ X41)
% 0.48/0.69          | ~ (v1_relat_1 @ X40))),
% 0.48/0.69      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.48/0.69  thf('34', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.48/0.69          | ~ (v1_relat_1 @ sk_D_1)
% 0.48/0.69          | ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ X0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.48/0.69  thf('35', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.69  thf('36', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.48/0.69          | ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ X0)))),
% 0.48/0.69      inference('demod', [status(thm)], ['34', '35'])).
% 0.48/0.69  thf(t7_ordinal1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.69  thf('37', plain,
% 0.48/0.69      (![X44 : $i, X45 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X44 @ X45) | ~ (r1_tarski @ X45 @ X44))),
% 0.48/0.69      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.48/0.69  thf('38', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ X0))
% 0.48/0.69          | ~ (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.48/0.69  thf(t144_relat_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ B ) =>
% 0.48/0.69       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.48/0.69  thf('39', plain,
% 0.48/0.69      (![X36 : $i, X37 : $i]:
% 0.48/0.69         ((r1_tarski @ (k9_relat_1 @ X36 @ X37) @ (k2_relat_1 @ X36))
% 0.48/0.69          | ~ (v1_relat_1 @ X36))),
% 0.48/0.69      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.48/0.69  thf('40', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.48/0.69          | (v4_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['30', '31'])).
% 0.48/0.69  thf('41', plain,
% 0.48/0.69      (![X1 : $i, X3 : $i]:
% 0.48/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('42', plain,
% 0.48/0.69      (![X7 : $i, X10 : $i]:
% 0.48/0.69         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.48/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.48/0.69  thf('43', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.48/0.69          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.48/0.69  thf('44', plain,
% 0.48/0.69      (![X1 : $i, X3 : $i]:
% 0.48/0.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('45', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.48/0.69          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.48/0.69          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.69  thf('46', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.48/0.69      inference('simplify', [status(thm)], ['45'])).
% 0.48/0.69  thf('47', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((v4_relat_1 @ sk_D_1 @ X0)
% 0.48/0.69          | (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D_1)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['40', '46'])).
% 0.48/0.69  thf('48', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.48/0.69      inference('demod', [status(thm)], ['17', '18'])).
% 0.48/0.69  thf(d10_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.69  thf('49', plain,
% 0.48/0.69      (![X4 : $i, X6 : $i]:
% 0.48/0.69         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.48/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.69  thf('50', plain,
% 0.48/0.69      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D_1))
% 0.48/0.70        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.48/0.70  thf('51', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((v4_relat_1 @ sk_D_1 @ X0)
% 0.48/0.70          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['47', '50'])).
% 0.48/0.70  thf('52', plain,
% 0.48/0.70      (![X32 : $i, X33 : $i]:
% 0.48/0.70         (~ (v4_relat_1 @ X32 @ X33)
% 0.48/0.70          | (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.48/0.70          | ~ (v1_relat_1 @ X32))),
% 0.48/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.48/0.70  thf('53', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 0.48/0.70          | ~ (v1_relat_1 @ sk_D_1)
% 0.48/0.70          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.48/0.70  thf('54', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.70  thf('55', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 0.48/0.70          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['53', '54'])).
% 0.48/0.70  thf(t4_subset_1, axiom,
% 0.48/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.70  thf('56', plain,
% 0.48/0.70      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.48/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.70  thf(t3_subset, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.70  thf('57', plain,
% 0.48/0.70      (![X22 : $i, X23 : $i]:
% 0.48/0.70         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.48/0.70  thf('59', plain,
% 0.48/0.70      (![X4 : $i, X6 : $i]:
% 0.48/0.70         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.48/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.70  thf('60', plain,
% 0.48/0.70      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.48/0.70  thf('61', plain,
% 0.48/0.70      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))
% 0.48/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['55', '60'])).
% 0.48/0.70  thf('62', plain,
% 0.48/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.48/0.70         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_tarski])).
% 0.48/0.70  thf('63', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.48/0.70      inference('simplify', [status(thm)], ['62'])).
% 0.48/0.70  thf('64', plain,
% 0.48/0.70      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.48/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['61', '63'])).
% 0.48/0.70  thf(t117_funct_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.48/0.70       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.48/0.70         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.48/0.70  thf('65', plain,
% 0.48/0.70      (![X42 : $i, X43 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X42 @ (k1_relat_1 @ X43))
% 0.48/0.70          | ((k11_relat_1 @ X43 @ X42) = (k1_tarski @ (k1_funct_1 @ X43 @ X42)))
% 0.48/0.70          | ~ (v1_funct_1 @ X43)
% 0.48/0.70          | ~ (v1_relat_1 @ X43))),
% 0.48/0.70      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.48/0.70  thf('66', plain,
% 0.48/0.70      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.48/0.70        | ~ (v1_relat_1 @ sk_D_1)
% 0.48/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.70        | ((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.48/0.70            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['64', '65'])).
% 0.48/0.70  thf('67', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.70  thf('68', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(d16_relat_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( v1_relat_1 @ A ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.48/0.70  thf('69', plain,
% 0.48/0.70      (![X30 : $i, X31 : $i]:
% 0.48/0.70         (((k11_relat_1 @ X30 @ X31) = (k9_relat_1 @ X30 @ (k1_tarski @ X31)))
% 0.48/0.70          | ~ (v1_relat_1 @ X30))),
% 0.48/0.70      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.48/0.70  thf('70', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.70  thf('71', plain,
% 0.48/0.70      (![X40 : $i, X41 : $i]:
% 0.48/0.70         (((X40) = (k7_relat_1 @ X40 @ X41))
% 0.48/0.70          | ~ (v4_relat_1 @ X40 @ X41)
% 0.48/0.70          | ~ (v1_relat_1 @ X40))),
% 0.48/0.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.48/0.70  thf('72', plain,
% 0.48/0.70      ((~ (v1_relat_1 @ sk_D_1)
% 0.48/0.70        | ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.48/0.70  thf('73', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.70  thf('74', plain, (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.48/0.70      inference('demod', [status(thm)], ['72', '73'])).
% 0.48/0.70  thf('75', plain,
% 0.48/0.70      (![X38 : $i, X39 : $i]:
% 0.48/0.70         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 0.48/0.70          | ~ (v1_relat_1 @ X38))),
% 0.48/0.70      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.48/0.70  thf('76', plain,
% 0.48/0.70      ((((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))
% 0.48/0.70        | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('sup+', [status(thm)], ['74', '75'])).
% 0.48/0.70  thf('77', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.70  thf('78', plain,
% 0.48/0.70      (((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))),
% 0.48/0.70      inference('demod', [status(thm)], ['76', '77'])).
% 0.48/0.70  thf('79', plain,
% 0.48/0.70      ((((k2_relat_1 @ sk_D_1) = (k11_relat_1 @ sk_D_1 @ sk_A))
% 0.48/0.70        | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('sup+', [status(thm)], ['69', '78'])).
% 0.48/0.70  thf('80', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.70  thf('81', plain, (((k2_relat_1 @ sk_D_1) = (k11_relat_1 @ sk_D_1 @ sk_A))),
% 0.48/0.70      inference('demod', [status(thm)], ['79', '80'])).
% 0.48/0.70  thf('82', plain,
% 0.48/0.70      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.48/0.70        | ((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.48/0.70      inference('demod', [status(thm)], ['66', '67', '68', '81'])).
% 0.48/0.70  thf('83', plain,
% 0.48/0.70      (~ (r1_tarski @ 
% 0.48/0.70          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C_2) @ 
% 0.48/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('84', plain,
% 0.48/0.70      ((~ (r1_tarski @ 
% 0.48/0.70           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C_2) @ 
% 0.48/0.70           (k2_relat_1 @ sk_D_1))
% 0.48/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['82', '83'])).
% 0.48/0.70  thf('85', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.48/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.70  thf('86', plain,
% 0.48/0.70      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_2) @ (k2_relat_1 @ sk_D_1))
% 0.48/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.48/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.48/0.70  thf('87', plain,
% 0.48/0.70      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['39', '86'])).
% 0.48/0.70  thf('88', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.70  thf('89', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.48/0.70  thf('90', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.48/0.70  thf('91', plain, (![X0 : $i]: ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['38', '89', '90'])).
% 0.48/0.70  thf('92', plain,
% 0.48/0.70      (![X0 : $i]: ((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['11', '91'])).
% 0.48/0.70  thf('93', plain,
% 0.48/0.70      (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ 
% 0.48/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.48/0.70      inference('demod', [status(thm)], ['4', '92'])).
% 0.48/0.70  thf('94', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.48/0.70  thf(t5_funct_2, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.48/0.70       ( ( ( ![D:$i]:
% 0.48/0.70             ( ( r2_hidden @ D @ A ) =>
% 0.48/0.70               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.48/0.70           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.48/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.48/0.70           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.48/0.70  thf(zf_stmt_2, axiom,
% 0.48/0.70    (![C:$i,B:$i,A:$i]:
% 0.48/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.48/0.70       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.48/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.48/0.70  thf(zf_stmt_4, axiom,
% 0.48/0.70    (![D:$i,C:$i,B:$i,A:$i]:
% 0.48/0.70     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.48/0.70       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.48/0.70  thf(zf_stmt_5, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.48/0.70       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.48/0.70           ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) =>
% 0.48/0.70         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.48/0.70  thf('95', plain,
% 0.48/0.70      (![X64 : $i, X65 : $i, X66 : $i]:
% 0.48/0.70         (((k1_relat_1 @ X65) != (X64))
% 0.48/0.70          | ~ (zip_tseitin_0 @ (sk_D @ X65 @ X66 @ X64) @ X65 @ X66 @ X64)
% 0.48/0.70          | (zip_tseitin_1 @ X65 @ X66 @ X64)
% 0.48/0.70          | ~ (v1_funct_1 @ X65)
% 0.48/0.70          | ~ (v1_relat_1 @ X65))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.48/0.70  thf('96', plain,
% 0.48/0.70      (![X65 : $i, X66 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X65)
% 0.48/0.70          | ~ (v1_funct_1 @ X65)
% 0.48/0.70          | (zip_tseitin_1 @ X65 @ X66 @ (k1_relat_1 @ X65))
% 0.48/0.70          | ~ (zip_tseitin_0 @ (sk_D @ X65 @ X66 @ (k1_relat_1 @ X65)) @ X65 @ 
% 0.48/0.70               X66 @ (k1_relat_1 @ X65)))),
% 0.48/0.70      inference('simplify', [status(thm)], ['95'])).
% 0.48/0.70  thf('97', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ 
% 0.48/0.70             sk_D_1 @ X0 @ k1_xboole_0)
% 0.48/0.70          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.48/0.70          | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.70          | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['94', '96'])).
% 0.48/0.70  thf('98', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.48/0.70  thf('99', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.48/0.70  thf('100', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('101', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.70  thf('102', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ k1_xboole_0) @ sk_D_1 @ 
% 0.48/0.70             X0 @ k1_xboole_0)
% 0.48/0.70          | (zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.48/0.70  thf('103', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.48/0.70  thf('104', plain,
% 0.48/0.70      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.48/0.70         ((zip_tseitin_0 @ X57 @ X58 @ X59 @ X60) | (r2_hidden @ X57 @ X60))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.48/0.70  thf('105', plain,
% 0.48/0.70      (![X44 : $i, X45 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X44 @ X45) | ~ (r1_tarski @ X45 @ X44))),
% 0.48/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.48/0.70  thf('106', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.70         ((zip_tseitin_0 @ X1 @ X3 @ X2 @ X0) | ~ (r1_tarski @ X0 @ X1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['104', '105'])).
% 0.48/0.70  thf('107', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         (zip_tseitin_0 @ X0 @ X2 @ X1 @ k1_xboole_0)),
% 0.48/0.70      inference('sup-', [status(thm)], ['103', '106'])).
% 0.48/0.70  thf('108', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0)),
% 0.48/0.70      inference('demod', [status(thm)], ['102', '107'])).
% 0.48/0.70  thf('109', plain,
% 0.48/0.70      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.48/0.70         ((m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X62)))
% 0.48/0.70          | ~ (zip_tseitin_1 @ X61 @ X62 @ X63))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.70  thf('110', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (m1_subset_1 @ sk_D_1 @ 
% 0.48/0.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['108', '109'])).
% 0.48/0.70  thf(t113_zfmisc_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.48/0.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.48/0.70  thf('111', plain,
% 0.48/0.70      (![X19 : $i, X20 : $i]:
% 0.48/0.70         (((k2_zfmisc_1 @ X19 @ X20) = (k1_xboole_0))
% 0.48/0.70          | ((X19) != (k1_xboole_0)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.48/0.70  thf('112', plain,
% 0.48/0.70      (![X20 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['111'])).
% 0.48/0.70  thf('113', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['110', '112'])).
% 0.48/0.70  thf('114', plain,
% 0.48/0.70      (![X22 : $i, X23 : $i]:
% 0.48/0.70         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('115', plain, ((r1_tarski @ sk_D_1 @ k1_xboole_0)),
% 0.48/0.70      inference('sup-', [status(thm)], ['113', '114'])).
% 0.48/0.70  thf('116', plain,
% 0.48/0.70      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.48/0.70  thf('117', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['115', '116'])).
% 0.48/0.70  thf('118', plain,
% 0.48/0.70      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.48/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.70  thf(dt_k7_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.48/0.70  thf('119', plain,
% 0.48/0.70      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.48/0.70          | (m1_subset_1 @ (k7_relset_1 @ X50 @ X51 @ X49 @ X52) @ 
% 0.48/0.70             (k1_zfmisc_1 @ X51)))),
% 0.48/0.70      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.48/0.70  thf('120', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         (m1_subset_1 @ (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 0.48/0.70          (k1_zfmisc_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['118', '119'])).
% 0.48/0.70  thf('121', plain,
% 0.48/0.70      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.48/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.70  thf('122', plain,
% 0.48/0.70      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 0.48/0.70          | ((k7_relset_1 @ X54 @ X55 @ X53 @ X56) = (k9_relat_1 @ X53 @ X56)))),
% 0.48/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.48/0.70  thf('123', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.48/0.70           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 0.48/0.70      inference('sup-', [status(thm)], ['121', '122'])).
% 0.48/0.70  thf('124', plain,
% 0.48/0.70      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.48/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.70  thf('125', plain,
% 0.48/0.70      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.48/0.70         ((v4_relat_1 @ X46 @ X47)
% 0.48/0.70          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.70  thf('126', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.48/0.70      inference('sup-', [status(thm)], ['124', '125'])).
% 0.48/0.70  thf('127', plain,
% 0.48/0.70      (![X40 : $i, X41 : $i]:
% 0.48/0.70         (((X40) = (k7_relat_1 @ X40 @ X41))
% 0.48/0.70          | ~ (v4_relat_1 @ X40 @ X41)
% 0.48/0.70          | ~ (v1_relat_1 @ X40))),
% 0.48/0.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.48/0.70  thf('128', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ k1_xboole_0)
% 0.48/0.70          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['126', '127'])).
% 0.48/0.70  thf('129', plain,
% 0.48/0.70      (![X20 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['111'])).
% 0.48/0.70  thf('130', plain,
% 0.48/0.70      (![X34 : $i, X35 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X34 @ X35))),
% 0.48/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.48/0.70  thf('131', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.48/0.70      inference('sup+', [status(thm)], ['129', '130'])).
% 0.48/0.70  thf('132', plain,
% 0.48/0.70      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['128', '131'])).
% 0.48/0.70  thf('133', plain,
% 0.48/0.70      (![X38 : $i, X39 : $i]:
% 0.48/0.70         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 0.48/0.70          | ~ (v1_relat_1 @ X38))),
% 0.48/0.70      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.48/0.70  thf('134', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.48/0.70          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['132', '133'])).
% 0.48/0.70  thf('135', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.48/0.70      inference('sup+', [status(thm)], ['129', '130'])).
% 0.48/0.70  thf('136', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['134', '135'])).
% 0.48/0.70  thf('137', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.48/0.70           = (k2_relat_1 @ k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['123', '136'])).
% 0.48/0.70  thf('138', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (m1_subset_1 @ (k2_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['120', '137'])).
% 0.48/0.70  thf('139', plain,
% 0.48/0.70      (![X22 : $i, X23 : $i]:
% 0.48/0.70         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('140', plain,
% 0.48/0.70      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.48/0.70      inference('sup-', [status(thm)], ['138', '139'])).
% 0.48/0.70  thf('141', plain,
% 0.48/0.70      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.48/0.70  thf('142', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['140', '141'])).
% 0.48/0.70  thf('143', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['115', '116'])).
% 0.48/0.70  thf('144', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.48/0.70  thf('145', plain, ($false),
% 0.48/0.70      inference('demod', [status(thm)], ['93', '117', '142', '143', '144'])).
% 0.48/0.70  
% 0.48/0.70  % SZS output end Refutation
% 0.48/0.70  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
