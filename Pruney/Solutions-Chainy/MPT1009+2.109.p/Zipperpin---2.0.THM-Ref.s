%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Id8e3iD9Tw

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:04 EST 2020

% Result     : Theorem 2.83s
% Output     : Refutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 806 expanded)
%              Number of leaves         :   45 ( 266 expanded)
%              Depth                    :   18
%              Number of atoms          : 1266 (8186 expanded)
%              Number of equality atoms :   94 ( 351 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ( ( k7_relset_1 @ X68 @ X69 @ X67 @ X70 )
        = ( k9_relat_1 @ X67 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( v4_relat_1 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X66 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X55: $i,X56: $i] :
      ( ( X55
        = ( k7_relat_1 @ X55 @ X56 ) )
      | ~ ( v4_relat_1 @ X55 @ X56 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X49: $i,X50: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) )
        = ( k9_relat_1 @ X51 @ X52 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X59: $i] :
      ( ( ( k2_relat_1 @ X59 )
       != k1_xboole_0 )
      | ( X59 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('21',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('23',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('24',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) )
        = ( k9_relat_1 @ X51 @ X52 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21','22','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k11_relat_1 @ X53 @ X54 )
        = k1_xboole_0 )
      | ( r2_hidden @ X54 @ ( k1_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('31',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k11_relat_1 @ X53 @ X54 )
        = k1_xboole_0 )
      | ( r2_hidden @ X54 @ ( k1_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X32 @ X34 ) @ X35 )
      | ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( r2_hidden @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k11_relat_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v4_relat_1 @ X47 @ X48 )
      | ( r1_tarski @ ( k1_relat_1 @ X47 ) @ X48 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('42',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k11_relat_1 @ sk_D @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('47',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k11_relat_1 @ X45 @ X46 )
        = ( k9_relat_1 @ X45 @ ( k1_tarski @ X46 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k11_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k11_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','46','51'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k1_relat_1 @ X63 )
       != ( k1_tarski @ X62 ) )
      | ( ( k2_relat_1 @ X63 )
        = ( k1_tarski @ ( k1_funct_1 @ X63 @ X62 ) ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) )
        = ( k9_relat_1 @ X51 @ X52 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('62',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('63',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) )
        = ( k9_relat_1 @ X51 @ X52 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('64',plain,(
    ! [X60: $i,X61: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X60 @ X61 ) @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ( r1_tarski @ ( k2_relat_1 @ X58 ) @ ( k2_relat_1 @ X57 ) )
      | ~ ( r1_tarski @ X58 @ X57 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X60: $i,X61: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X60 @ X61 ) @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X37: $i,X39: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['62','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['61','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','84'])).

thf('86',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','85'])).

thf('87',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X60: $i,X61: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X60 @ X61 ) @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('89',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X49: $i,X50: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('94',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('95',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) )
        = ( k9_relat_1 @ X51 @ X52 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','96'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('104',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( v4_relat_1 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X66 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('105',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v4_relat_1 @ X47 @ X48 )
      | ( r1_tarski @ ( k1_relat_1 @ X47 ) @ X48 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','96'])).

thf('109',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('111',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k11_relat_1 @ X53 @ X54 )
        = k1_xboole_0 )
      | ( r2_hidden @ X54 @ ( k1_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','96'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('117',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( m1_subset_1 @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k11_relat_1 @ X45 @ X46 )
        = ( k9_relat_1 @ X45 @ ( k1_tarski @ X46 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k11_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','96'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k11_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('129',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','129'])).

thf('131',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['86'])).

thf('132',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['4','87','130','131','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Id8e3iD9Tw
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.83/3.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.83/3.06  % Solved by: fo/fo7.sh
% 2.83/3.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.83/3.06  % done 6596 iterations in 2.597s
% 2.83/3.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.83/3.06  % SZS output start Refutation
% 2.83/3.06  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 2.83/3.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.83/3.06  thf(sk_B_type, type, sk_B: $i).
% 2.83/3.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.83/3.06  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.83/3.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.83/3.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.83/3.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.83/3.06  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.83/3.06  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.83/3.06  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.83/3.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.83/3.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.83/3.06  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.83/3.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.83/3.06  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.83/3.06  thf(sk_A_type, type, sk_A: $i).
% 2.83/3.06  thf(sk_C_type, type, sk_C: $i).
% 2.83/3.06  thf(sk_D_type, type, sk_D: $i).
% 2.83/3.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.83/3.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.83/3.06  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 2.83/3.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.83/3.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.83/3.06  thf(t64_funct_2, conjecture,
% 2.83/3.06    (![A:$i,B:$i,C:$i,D:$i]:
% 2.83/3.06     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 2.83/3.06         ( m1_subset_1 @
% 2.83/3.06           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 2.83/3.06       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 2.83/3.06         ( r1_tarski @
% 2.83/3.06           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 2.83/3.06           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 2.83/3.06  thf(zf_stmt_0, negated_conjecture,
% 2.83/3.06    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.83/3.06        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 2.83/3.06            ( m1_subset_1 @
% 2.83/3.06              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 2.83/3.06          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 2.83/3.06            ( r1_tarski @
% 2.83/3.06              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 2.83/3.06              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 2.83/3.06    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 2.83/3.06  thf('0', plain,
% 2.83/3.06      (~ (r1_tarski @ 
% 2.83/3.06          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 2.83/3.06          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 2.83/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.06  thf('1', plain,
% 2.83/3.06      ((m1_subset_1 @ sk_D @ 
% 2.83/3.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.83/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.06  thf(redefinition_k7_relset_1, axiom,
% 2.83/3.06    (![A:$i,B:$i,C:$i,D:$i]:
% 2.83/3.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.83/3.06       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 2.83/3.06  thf('2', plain,
% 2.83/3.06      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 2.83/3.06         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 2.83/3.06          | ((k7_relset_1 @ X68 @ X69 @ X67 @ X70) = (k9_relat_1 @ X67 @ X70)))),
% 2.83/3.06      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 2.83/3.06  thf('3', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 2.83/3.06           = (k9_relat_1 @ sk_D @ X0))),
% 2.83/3.06      inference('sup-', [status(thm)], ['1', '2'])).
% 2.83/3.06  thf('4', plain,
% 2.83/3.06      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 2.83/3.06          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['0', '3'])).
% 2.83/3.06  thf('5', plain,
% 2.83/3.06      ((m1_subset_1 @ sk_D @ 
% 2.83/3.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.83/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.06  thf(cc2_relset_1, axiom,
% 2.83/3.06    (![A:$i,B:$i,C:$i]:
% 2.83/3.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.83/3.06       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.83/3.06  thf('6', plain,
% 2.83/3.06      (![X64 : $i, X65 : $i, X66 : $i]:
% 2.83/3.06         ((v4_relat_1 @ X64 @ X65)
% 2.83/3.06          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X66))))),
% 2.83/3.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.83/3.06  thf('7', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 2.83/3.06      inference('sup-', [status(thm)], ['5', '6'])).
% 2.83/3.06  thf(t209_relat_1, axiom,
% 2.83/3.06    (![A:$i,B:$i]:
% 2.83/3.06     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.83/3.06       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.83/3.06  thf('8', plain,
% 2.83/3.06      (![X55 : $i, X56 : $i]:
% 2.83/3.06         (((X55) = (k7_relat_1 @ X55 @ X56))
% 2.83/3.06          | ~ (v4_relat_1 @ X55 @ X56)
% 2.83/3.06          | ~ (v1_relat_1 @ X55))),
% 2.83/3.06      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.83/3.06  thf('9', plain,
% 2.83/3.06      ((~ (v1_relat_1 @ sk_D)
% 2.83/3.06        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 2.83/3.06      inference('sup-', [status(thm)], ['7', '8'])).
% 2.83/3.06  thf('10', plain,
% 2.83/3.06      ((m1_subset_1 @ sk_D @ 
% 2.83/3.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.83/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.06  thf(cc2_relat_1, axiom,
% 2.83/3.06    (![A:$i]:
% 2.83/3.06     ( ( v1_relat_1 @ A ) =>
% 2.83/3.06       ( ![B:$i]:
% 2.83/3.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.83/3.06  thf('11', plain,
% 2.83/3.06      (![X43 : $i, X44 : $i]:
% 2.83/3.06         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 2.83/3.06          | (v1_relat_1 @ X43)
% 2.83/3.06          | ~ (v1_relat_1 @ X44))),
% 2.83/3.06      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.83/3.06  thf('12', plain,
% 2.83/3.06      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 2.83/3.06        | (v1_relat_1 @ sk_D))),
% 2.83/3.06      inference('sup-', [status(thm)], ['10', '11'])).
% 2.83/3.06  thf(fc6_relat_1, axiom,
% 2.83/3.06    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.83/3.06  thf('13', plain,
% 2.83/3.06      (![X49 : $i, X50 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X49 @ X50))),
% 2.83/3.06      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.83/3.06  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf('15', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['9', '14'])).
% 2.83/3.06  thf(t148_relat_1, axiom,
% 2.83/3.06    (![A:$i,B:$i]:
% 2.83/3.06     ( ( v1_relat_1 @ B ) =>
% 2.83/3.06       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.83/3.06  thf('16', plain,
% 2.83/3.06      (![X51 : $i, X52 : $i]:
% 2.83/3.06         (((k2_relat_1 @ (k7_relat_1 @ X51 @ X52)) = (k9_relat_1 @ X51 @ X52))
% 2.83/3.06          | ~ (v1_relat_1 @ X51))),
% 2.83/3.06      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.83/3.06  thf(t64_relat_1, axiom,
% 2.83/3.06    (![A:$i]:
% 2.83/3.06     ( ( v1_relat_1 @ A ) =>
% 2.83/3.06       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 2.83/3.06           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.83/3.06         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 2.83/3.06  thf('17', plain,
% 2.83/3.06      (![X59 : $i]:
% 2.83/3.06         (((k2_relat_1 @ X59) != (k1_xboole_0))
% 2.83/3.06          | ((X59) = (k1_xboole_0))
% 2.83/3.06          | ~ (v1_relat_1 @ X59))),
% 2.83/3.06      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.83/3.06  thf('18', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 2.83/3.06          | ~ (v1_relat_1 @ X1)
% 2.83/3.06          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.83/3.06          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['16', '17'])).
% 2.83/3.06  thf('19', plain,
% 2.83/3.06      ((~ (v1_relat_1 @ sk_D)
% 2.83/3.06        | ((k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 2.83/3.06        | ~ (v1_relat_1 @ sk_D)
% 2.83/3.06        | ((k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['15', '18'])).
% 2.83/3.06  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf('21', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['9', '14'])).
% 2.83/3.06  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf('23', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['9', '14'])).
% 2.83/3.06  thf('24', plain,
% 2.83/3.06      (![X51 : $i, X52 : $i]:
% 2.83/3.06         (((k2_relat_1 @ (k7_relat_1 @ X51 @ X52)) = (k9_relat_1 @ X51 @ X52))
% 2.83/3.06          | ~ (v1_relat_1 @ X51))),
% 2.83/3.06      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.83/3.06  thf('25', plain,
% 2.83/3.06      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 2.83/3.06        | ~ (v1_relat_1 @ sk_D))),
% 2.83/3.06      inference('sup+', [status(thm)], ['23', '24'])).
% 2.83/3.06  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf('27', plain,
% 2.83/3.06      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['25', '26'])).
% 2.83/3.06  thf('28', plain,
% 2.83/3.06      ((((sk_D) = (k1_xboole_0)) | ((k2_relat_1 @ sk_D) != (k1_xboole_0)))),
% 2.83/3.06      inference('demod', [status(thm)], ['19', '20', '21', '22', '27'])).
% 2.83/3.06  thf(t69_enumset1, axiom,
% 2.83/3.06    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.83/3.06  thf('29', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 2.83/3.06      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.83/3.06  thf(t205_relat_1, axiom,
% 2.83/3.06    (![A:$i,B:$i]:
% 2.83/3.06     ( ( v1_relat_1 @ B ) =>
% 2.83/3.06       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 2.83/3.06         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 2.83/3.06  thf('30', plain,
% 2.83/3.06      (![X53 : $i, X54 : $i]:
% 2.83/3.06         (((k11_relat_1 @ X53 @ X54) = (k1_xboole_0))
% 2.83/3.06          | (r2_hidden @ X54 @ (k1_relat_1 @ X53))
% 2.83/3.06          | ~ (v1_relat_1 @ X53))),
% 2.83/3.06      inference('cnf', [status(esa)], [t205_relat_1])).
% 2.83/3.06  thf('31', plain,
% 2.83/3.06      (![X53 : $i, X54 : $i]:
% 2.83/3.06         (((k11_relat_1 @ X53 @ X54) = (k1_xboole_0))
% 2.83/3.06          | (r2_hidden @ X54 @ (k1_relat_1 @ X53))
% 2.83/3.06          | ~ (v1_relat_1 @ X53))),
% 2.83/3.06      inference('cnf', [status(esa)], [t205_relat_1])).
% 2.83/3.06  thf(t38_zfmisc_1, axiom,
% 2.83/3.06    (![A:$i,B:$i,C:$i]:
% 2.83/3.06     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 2.83/3.06       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 2.83/3.06  thf('32', plain,
% 2.83/3.06      (![X32 : $i, X34 : $i, X35 : $i]:
% 2.83/3.06         ((r1_tarski @ (k2_tarski @ X32 @ X34) @ X35)
% 2.83/3.06          | ~ (r2_hidden @ X34 @ X35)
% 2.83/3.06          | ~ (r2_hidden @ X32 @ X35))),
% 2.83/3.06      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 2.83/3.06  thf('33', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ X0)
% 2.83/3.06          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 2.83/3.06          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 2.83/3.06          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k1_relat_1 @ X0)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['31', '32'])).
% 2.83/3.06  thf('34', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ X0)
% 2.83/3.06          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 2.83/3.06          | (r1_tarski @ (k2_tarski @ X1 @ X2) @ (k1_relat_1 @ X0))
% 2.83/3.06          | ((k11_relat_1 @ X0 @ X2) = (k1_xboole_0))
% 2.83/3.06          | ~ (v1_relat_1 @ X0))),
% 2.83/3.06      inference('sup-', [status(thm)], ['30', '33'])).
% 2.83/3.06  thf('35', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.06         (((k11_relat_1 @ X0 @ X2) = (k1_xboole_0))
% 2.83/3.06          | (r1_tarski @ (k2_tarski @ X1 @ X2) @ (k1_relat_1 @ X0))
% 2.83/3.06          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 2.83/3.06          | ~ (v1_relat_1 @ X0))),
% 2.83/3.06      inference('simplify', [status(thm)], ['34'])).
% 2.83/3.06  thf('36', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         ((r1_tarski @ (k1_tarski @ X0) @ (k1_relat_1 @ X1))
% 2.83/3.06          | ~ (v1_relat_1 @ X1)
% 2.83/3.06          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 2.83/3.06          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.83/3.06      inference('sup+', [status(thm)], ['29', '35'])).
% 2.83/3.06  thf('37', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 2.83/3.06          | ~ (v1_relat_1 @ X1)
% 2.83/3.06          | (r1_tarski @ (k1_tarski @ X0) @ (k1_relat_1 @ X1)))),
% 2.83/3.06      inference('simplify', [status(thm)], ['36'])).
% 2.83/3.06  thf('38', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 2.83/3.06      inference('sup-', [status(thm)], ['5', '6'])).
% 2.83/3.06  thf(d18_relat_1, axiom,
% 2.83/3.06    (![A:$i,B:$i]:
% 2.83/3.06     ( ( v1_relat_1 @ B ) =>
% 2.83/3.06       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.83/3.06  thf('39', plain,
% 2.83/3.06      (![X47 : $i, X48 : $i]:
% 2.83/3.06         (~ (v4_relat_1 @ X47 @ X48)
% 2.83/3.06          | (r1_tarski @ (k1_relat_1 @ X47) @ X48)
% 2.83/3.06          | ~ (v1_relat_1 @ X47))),
% 2.83/3.06      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.83/3.06  thf('40', plain,
% 2.83/3.06      ((~ (v1_relat_1 @ sk_D)
% 2.83/3.06        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['38', '39'])).
% 2.83/3.06  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf('42', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 2.83/3.06      inference('demod', [status(thm)], ['40', '41'])).
% 2.83/3.06  thf(d10_xboole_0, axiom,
% 2.83/3.06    (![A:$i,B:$i]:
% 2.83/3.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.83/3.06  thf('43', plain,
% 2.83/3.06      (![X0 : $i, X2 : $i]:
% 2.83/3.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.83/3.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.83/3.06  thf('44', plain,
% 2.83/3.06      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D))
% 2.83/3.06        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['42', '43'])).
% 2.83/3.06  thf('45', plain,
% 2.83/3.06      ((~ (v1_relat_1 @ sk_D)
% 2.83/3.06        | ((k11_relat_1 @ sk_D @ sk_A) = (k1_xboole_0))
% 2.83/3.06        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['37', '44'])).
% 2.83/3.06  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf(d16_relat_1, axiom,
% 2.83/3.06    (![A:$i]:
% 2.83/3.06     ( ( v1_relat_1 @ A ) =>
% 2.83/3.06       ( ![B:$i]:
% 2.83/3.06         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 2.83/3.06  thf('47', plain,
% 2.83/3.06      (![X45 : $i, X46 : $i]:
% 2.83/3.06         (((k11_relat_1 @ X45 @ X46) = (k9_relat_1 @ X45 @ (k1_tarski @ X46)))
% 2.83/3.06          | ~ (v1_relat_1 @ X45))),
% 2.83/3.06      inference('cnf', [status(esa)], [d16_relat_1])).
% 2.83/3.06  thf('48', plain,
% 2.83/3.06      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['25', '26'])).
% 2.83/3.06  thf('49', plain,
% 2.83/3.06      ((((k2_relat_1 @ sk_D) = (k11_relat_1 @ sk_D @ sk_A))
% 2.83/3.06        | ~ (v1_relat_1 @ sk_D))),
% 2.83/3.06      inference('sup+', [status(thm)], ['47', '48'])).
% 2.83/3.06  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf('51', plain, (((k2_relat_1 @ sk_D) = (k11_relat_1 @ sk_D @ sk_A))),
% 2.83/3.06      inference('demod', [status(thm)], ['49', '50'])).
% 2.83/3.06  thf('52', plain,
% 2.83/3.06      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 2.83/3.06        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 2.83/3.06      inference('demod', [status(thm)], ['45', '46', '51'])).
% 2.83/3.06  thf(t14_funct_1, axiom,
% 2.83/3.06    (![A:$i,B:$i]:
% 2.83/3.06     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.83/3.06       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 2.83/3.06         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 2.83/3.06  thf('53', plain,
% 2.83/3.06      (![X62 : $i, X63 : $i]:
% 2.83/3.06         (((k1_relat_1 @ X63) != (k1_tarski @ X62))
% 2.83/3.06          | ((k2_relat_1 @ X63) = (k1_tarski @ (k1_funct_1 @ X63 @ X62)))
% 2.83/3.06          | ~ (v1_funct_1 @ X63)
% 2.83/3.06          | ~ (v1_relat_1 @ X63))),
% 2.83/3.06      inference('cnf', [status(esa)], [t14_funct_1])).
% 2.83/3.06  thf('54', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 2.83/3.06          | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 2.83/3.06          | ~ (v1_relat_1 @ X0)
% 2.83/3.06          | ~ (v1_funct_1 @ X0)
% 2.83/3.06          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 2.83/3.06      inference('sup-', [status(thm)], ['52', '53'])).
% 2.83/3.06  thf('55', plain,
% 2.83/3.06      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 2.83/3.06        | ~ (v1_funct_1 @ sk_D)
% 2.83/3.06        | ~ (v1_relat_1 @ sk_D)
% 2.83/3.06        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 2.83/3.06      inference('eq_res', [status(thm)], ['54'])).
% 2.83/3.06  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 2.83/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.06  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf('58', plain,
% 2.83/3.06      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 2.83/3.06        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 2.83/3.06      inference('demod', [status(thm)], ['55', '56', '57'])).
% 2.83/3.06  thf('59', plain,
% 2.83/3.06      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 2.83/3.06          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['0', '3'])).
% 2.83/3.06  thf('60', plain,
% 2.83/3.06      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 2.83/3.06        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['58', '59'])).
% 2.83/3.06  thf('61', plain,
% 2.83/3.06      (![X51 : $i, X52 : $i]:
% 2.83/3.06         (((k2_relat_1 @ (k7_relat_1 @ X51 @ X52)) = (k9_relat_1 @ X51 @ X52))
% 2.83/3.06          | ~ (v1_relat_1 @ X51))),
% 2.83/3.06      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.83/3.06  thf('62', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['9', '14'])).
% 2.83/3.06  thf('63', plain,
% 2.83/3.06      (![X51 : $i, X52 : $i]:
% 2.83/3.06         (((k2_relat_1 @ (k7_relat_1 @ X51 @ X52)) = (k9_relat_1 @ X51 @ X52))
% 2.83/3.06          | ~ (v1_relat_1 @ X51))),
% 2.83/3.06      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.83/3.06  thf(t88_relat_1, axiom,
% 2.83/3.06    (![A:$i,B:$i]:
% 2.83/3.06     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 2.83/3.06  thf('64', plain,
% 2.83/3.06      (![X60 : $i, X61 : $i]:
% 2.83/3.06         ((r1_tarski @ (k7_relat_1 @ X60 @ X61) @ X60) | ~ (v1_relat_1 @ X60))),
% 2.83/3.06      inference('cnf', [status(esa)], [t88_relat_1])).
% 2.83/3.06  thf(t25_relat_1, axiom,
% 2.83/3.06    (![A:$i]:
% 2.83/3.06     ( ( v1_relat_1 @ A ) =>
% 2.83/3.06       ( ![B:$i]:
% 2.83/3.06         ( ( v1_relat_1 @ B ) =>
% 2.83/3.06           ( ( r1_tarski @ A @ B ) =>
% 2.83/3.06             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 2.83/3.06               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 2.83/3.06  thf('65', plain,
% 2.83/3.06      (![X57 : $i, X58 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ X57)
% 2.83/3.06          | (r1_tarski @ (k2_relat_1 @ X58) @ (k2_relat_1 @ X57))
% 2.83/3.06          | ~ (r1_tarski @ X58 @ X57)
% 2.83/3.06          | ~ (v1_relat_1 @ X58))),
% 2.83/3.06      inference('cnf', [status(esa)], [t25_relat_1])).
% 2.83/3.06  thf('66', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ X0)
% 2.83/3.06          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 2.83/3.06          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 2.83/3.06             (k2_relat_1 @ X0))
% 2.83/3.06          | ~ (v1_relat_1 @ X0))),
% 2.83/3.06      inference('sup-', [status(thm)], ['64', '65'])).
% 2.83/3.06  thf('67', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 2.83/3.06           (k2_relat_1 @ X0))
% 2.83/3.06          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 2.83/3.06          | ~ (v1_relat_1 @ X0))),
% 2.83/3.06      inference('simplify', [status(thm)], ['66'])).
% 2.83/3.06  thf('68', plain,
% 2.83/3.06      (![X60 : $i, X61 : $i]:
% 2.83/3.06         ((r1_tarski @ (k7_relat_1 @ X60 @ X61) @ X60) | ~ (v1_relat_1 @ X60))),
% 2.83/3.06      inference('cnf', [status(esa)], [t88_relat_1])).
% 2.83/3.06  thf(t3_subset, axiom,
% 2.83/3.06    (![A:$i,B:$i]:
% 2.83/3.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.83/3.06  thf('69', plain,
% 2.83/3.06      (![X37 : $i, X39 : $i]:
% 2.83/3.06         ((m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X37 @ X39))),
% 2.83/3.06      inference('cnf', [status(esa)], [t3_subset])).
% 2.83/3.06  thf('70', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ X0)
% 2.83/3.06          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['68', '69'])).
% 2.83/3.06  thf('71', plain,
% 2.83/3.06      (![X43 : $i, X44 : $i]:
% 2.83/3.06         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 2.83/3.06          | (v1_relat_1 @ X43)
% 2.83/3.06          | ~ (v1_relat_1 @ X44))),
% 2.83/3.06      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.83/3.06  thf('72', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ X0)
% 2.83/3.06          | ~ (v1_relat_1 @ X0)
% 2.83/3.06          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['70', '71'])).
% 2.83/3.06  thf('73', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 2.83/3.06      inference('simplify', [status(thm)], ['72'])).
% 2.83/3.06  thf('74', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ X0)
% 2.83/3.06          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 2.83/3.06             (k2_relat_1 @ X0)))),
% 2.83/3.06      inference('clc', [status(thm)], ['67', '73'])).
% 2.83/3.06  thf('75', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.06         ((r1_tarski @ 
% 2.83/3.06           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 2.83/3.06           (k9_relat_1 @ X1 @ X0))
% 2.83/3.06          | ~ (v1_relat_1 @ X1)
% 2.83/3.06          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.83/3.06      inference('sup+', [status(thm)], ['63', '74'])).
% 2.83/3.06  thf('76', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 2.83/3.06      inference('simplify', [status(thm)], ['72'])).
% 2.83/3.06  thf('77', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ X1)
% 2.83/3.06          | (r1_tarski @ 
% 2.83/3.06             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 2.83/3.06             (k9_relat_1 @ X1 @ X0)))),
% 2.83/3.06      inference('clc', [status(thm)], ['75', '76'])).
% 2.83/3.06  thf('78', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 2.83/3.06           (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 2.83/3.06          | ~ (v1_relat_1 @ sk_D))),
% 2.83/3.06      inference('sup+', [status(thm)], ['62', '77'])).
% 2.83/3.06  thf('79', plain,
% 2.83/3.06      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['25', '26'])).
% 2.83/3.06  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf('81', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 2.83/3.06          (k2_relat_1 @ sk_D))),
% 2.83/3.06      inference('demod', [status(thm)], ['78', '79', '80'])).
% 2.83/3.06  thf('82', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 2.83/3.06          | ~ (v1_relat_1 @ sk_D))),
% 2.83/3.06      inference('sup+', [status(thm)], ['61', '81'])).
% 2.83/3.06  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.06      inference('demod', [status(thm)], ['12', '13'])).
% 2.83/3.06  thf('84', plain,
% 2.83/3.06      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 2.83/3.06      inference('demod', [status(thm)], ['82', '83'])).
% 2.83/3.06  thf('85', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 2.83/3.06      inference('demod', [status(thm)], ['60', '84'])).
% 2.83/3.06  thf('86', plain,
% 2.83/3.06      ((((sk_D) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 2.83/3.06      inference('demod', [status(thm)], ['28', '85'])).
% 2.83/3.06  thf('87', plain, (((sk_D) = (k1_xboole_0))),
% 2.83/3.06      inference('simplify', [status(thm)], ['86'])).
% 2.83/3.06  thf('88', plain,
% 2.83/3.06      (![X60 : $i, X61 : $i]:
% 2.83/3.06         ((r1_tarski @ (k7_relat_1 @ X60 @ X61) @ X60) | ~ (v1_relat_1 @ X60))),
% 2.83/3.06      inference('cnf', [status(esa)], [t88_relat_1])).
% 2.83/3.06  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.83/3.06  thf('89', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.83/3.06      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.83/3.06  thf('90', plain,
% 2.83/3.06      (![X0 : $i, X2 : $i]:
% 2.83/3.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.83/3.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.83/3.06  thf('91', plain,
% 2.83/3.06      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['89', '90'])).
% 2.83/3.06  thf('92', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ k1_xboole_0)
% 2.83/3.06          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['88', '91'])).
% 2.83/3.06  thf('93', plain,
% 2.83/3.06      (![X49 : $i, X50 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X49 @ X50))),
% 2.83/3.06      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.83/3.06  thf(t4_subset_1, axiom,
% 2.83/3.06    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.83/3.06  thf('94', plain,
% 2.83/3.06      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 2.83/3.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.83/3.06  thf('95', plain,
% 2.83/3.06      (![X43 : $i, X44 : $i]:
% 2.83/3.06         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 2.83/3.06          | (v1_relat_1 @ X43)
% 2.83/3.06          | ~ (v1_relat_1 @ X44))),
% 2.83/3.06      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.83/3.06  thf('96', plain,
% 2.83/3.06      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 2.83/3.06      inference('sup-', [status(thm)], ['94', '95'])).
% 2.83/3.06  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.83/3.06      inference('sup-', [status(thm)], ['93', '96'])).
% 2.83/3.06  thf('98', plain,
% 2.83/3.06      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.83/3.06      inference('demod', [status(thm)], ['92', '97'])).
% 2.83/3.06  thf('99', plain,
% 2.83/3.06      (![X51 : $i, X52 : $i]:
% 2.83/3.06         (((k2_relat_1 @ (k7_relat_1 @ X51 @ X52)) = (k9_relat_1 @ X51 @ X52))
% 2.83/3.06          | ~ (v1_relat_1 @ X51))),
% 2.83/3.06      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.83/3.06  thf('100', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 2.83/3.06          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.83/3.06      inference('sup+', [status(thm)], ['98', '99'])).
% 2.83/3.06  thf('101', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.83/3.06      inference('sup-', [status(thm)], ['93', '96'])).
% 2.83/3.06  thf('102', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         ((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 2.83/3.06      inference('demod', [status(thm)], ['100', '101'])).
% 2.83/3.06  thf('103', plain,
% 2.83/3.06      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 2.83/3.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.83/3.06  thf('104', plain,
% 2.83/3.06      (![X64 : $i, X65 : $i, X66 : $i]:
% 2.83/3.06         ((v4_relat_1 @ X64 @ X65)
% 2.83/3.06          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X66))))),
% 2.83/3.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.83/3.06  thf('105', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 2.83/3.06      inference('sup-', [status(thm)], ['103', '104'])).
% 2.83/3.06  thf('106', plain,
% 2.83/3.06      (![X47 : $i, X48 : $i]:
% 2.83/3.06         (~ (v4_relat_1 @ X47 @ X48)
% 2.83/3.06          | (r1_tarski @ (k1_relat_1 @ X47) @ X48)
% 2.83/3.06          | ~ (v1_relat_1 @ X47))),
% 2.83/3.06      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.83/3.06  thf('107', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         (~ (v1_relat_1 @ k1_xboole_0)
% 2.83/3.06          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 2.83/3.06      inference('sup-', [status(thm)], ['105', '106'])).
% 2.83/3.06  thf('108', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.83/3.06      inference('sup-', [status(thm)], ['93', '96'])).
% 2.83/3.06  thf('109', plain,
% 2.83/3.06      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 2.83/3.06      inference('demod', [status(thm)], ['107', '108'])).
% 2.83/3.06  thf('110', plain,
% 2.83/3.06      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.83/3.06      inference('sup-', [status(thm)], ['89', '90'])).
% 2.83/3.06  thf('111', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.83/3.06      inference('sup-', [status(thm)], ['109', '110'])).
% 2.83/3.06  thf('112', plain,
% 2.83/3.06      (![X53 : $i, X54 : $i]:
% 2.83/3.06         (((k11_relat_1 @ X53 @ X54) = (k1_xboole_0))
% 2.83/3.06          | (r2_hidden @ X54 @ (k1_relat_1 @ X53))
% 2.83/3.06          | ~ (v1_relat_1 @ X53))),
% 2.83/3.06      inference('cnf', [status(esa)], [t205_relat_1])).
% 2.83/3.06  thf('113', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         ((r2_hidden @ X0 @ k1_xboole_0)
% 2.83/3.06          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.83/3.06          | ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 2.83/3.06      inference('sup+', [status(thm)], ['111', '112'])).
% 2.83/3.06  thf('114', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.83/3.06      inference('sup-', [status(thm)], ['93', '96'])).
% 2.83/3.06  thf('115', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         ((r2_hidden @ X0 @ k1_xboole_0)
% 2.83/3.06          | ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 2.83/3.06      inference('demod', [status(thm)], ['113', '114'])).
% 2.83/3.06  thf('116', plain,
% 2.83/3.06      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 2.83/3.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.83/3.06  thf(t4_subset, axiom,
% 2.83/3.06    (![A:$i,B:$i,C:$i]:
% 2.83/3.06     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.83/3.06       ( m1_subset_1 @ A @ C ) ))).
% 2.83/3.06  thf('117', plain,
% 2.83/3.06      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.83/3.06         (~ (r2_hidden @ X40 @ X41)
% 2.83/3.06          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 2.83/3.06          | (m1_subset_1 @ X40 @ X42))),
% 2.83/3.06      inference('cnf', [status(esa)], [t4_subset])).
% 2.83/3.06  thf('118', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 2.83/3.06      inference('sup-', [status(thm)], ['116', '117'])).
% 2.83/3.06  thf('119', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         (((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 2.83/3.06          | (m1_subset_1 @ X0 @ X1))),
% 2.83/3.06      inference('sup-', [status(thm)], ['115', '118'])).
% 2.83/3.06  thf('120', plain,
% 2.83/3.06      (![X45 : $i, X46 : $i]:
% 2.83/3.06         (((k11_relat_1 @ X45 @ X46) = (k9_relat_1 @ X45 @ (k1_tarski @ X46)))
% 2.83/3.06          | ~ (v1_relat_1 @ X45))),
% 2.83/3.06      inference('cnf', [status(esa)], [d16_relat_1])).
% 2.83/3.06  thf('121', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         ((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 2.83/3.06      inference('demod', [status(thm)], ['100', '101'])).
% 2.83/3.06  thf('122', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         (((k2_relat_1 @ k1_xboole_0) = (k11_relat_1 @ k1_xboole_0 @ X0))
% 2.83/3.06          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.83/3.06      inference('sup+', [status(thm)], ['120', '121'])).
% 2.83/3.06  thf('123', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.83/3.06      inference('sup-', [status(thm)], ['93', '96'])).
% 2.83/3.06  thf('124', plain,
% 2.83/3.06      (![X0 : $i]:
% 2.83/3.06         ((k2_relat_1 @ k1_xboole_0) = (k11_relat_1 @ k1_xboole_0 @ X0))),
% 2.83/3.06      inference('demod', [status(thm)], ['122', '123'])).
% 2.83/3.06  thf('125', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 2.83/3.06          | (m1_subset_1 @ X0 @ X1))),
% 2.83/3.06      inference('sup+', [status(thm)], ['119', '124'])).
% 2.83/3.06  thf('126', plain,
% 2.83/3.06      (![X37 : $i, X38 : $i]:
% 2.83/3.06         ((r1_tarski @ X37 @ X38) | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 2.83/3.06      inference('cnf', [status(esa)], [t3_subset])).
% 2.83/3.06  thf('127', plain,
% 2.83/3.06      (![X0 : $i, X1 : $i]:
% 2.83/3.06         (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | (r1_tarski @ X1 @ X0))),
% 2.83/3.06      inference('sup-', [status(thm)], ['125', '126'])).
% 2.83/3.06  thf('128', plain,
% 2.83/3.06      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 2.83/3.06          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 2.83/3.06      inference('demod', [status(thm)], ['0', '3'])).
% 2.83/3.06  thf('129', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.83/3.06      inference('sup-', [status(thm)], ['127', '128'])).
% 2.83/3.06  thf('130', plain,
% 2.83/3.06      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 2.83/3.06      inference('demod', [status(thm)], ['102', '129'])).
% 2.83/3.06  thf('131', plain, (((sk_D) = (k1_xboole_0))),
% 2.83/3.06      inference('simplify', [status(thm)], ['86'])).
% 2.83/3.06  thf('132', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.83/3.06      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.83/3.06  thf('133', plain, ($false),
% 2.83/3.06      inference('demod', [status(thm)], ['4', '87', '130', '131', '132'])).
% 2.83/3.06  
% 2.83/3.06  % SZS output end Refutation
% 2.83/3.06  
% 2.83/3.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
