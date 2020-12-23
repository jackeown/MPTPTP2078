%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.loEUGa2UFu

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:32 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 176 expanded)
%              Number of leaves         :   42 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  853 (1985 expanded)
%              Number of equality atoms :   63 ( 138 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('5',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X57 @ X54 ) @ ( k2_relset_1 @ X55 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k2_relset_1 @ X50 @ X51 @ X49 )
        = ( k2_relat_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X16 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','24'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k11_relat_1 @ X30 @ X31 )
        = k1_xboole_0 )
      | ( r2_hidden @ X31 @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X16 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X43 @ X44 @ X45 ) @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('33',plain,(
    m1_subset_1 @ ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k1_relset_1 @ X47 @ X48 @ X46 )
        = ( k1_relat_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('44',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k11_relat_1 @ X24 @ X25 )
        = ( k9_relat_1 @ X24 @ ( k1_tarski @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v4_relat_1 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32
        = ( k7_relat_1 @ X32 @ X33 ) )
      | ~ ( v4_relat_1 @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('53',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) )
        = ( k9_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['46','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','45','60'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('62',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relat_1 @ X36 )
       != ( k1_tarski @ X35 ) )
      | ( ( k2_relat_1 @ X36 )
        = ( k1_tarski @ ( k1_funct_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('70',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['25','69','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.loEUGa2UFu
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:17:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.71/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.92  % Solved by: fo/fo7.sh
% 0.71/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.92  % done 805 iterations in 0.458s
% 0.71/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.92  % SZS output start Refutation
% 0.71/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.92  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.71/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.92  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.71/0.92  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.71/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.71/0.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.71/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.92  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.71/0.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.71/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.71/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.71/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.71/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.92  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.71/0.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.71/0.92  thf(t69_enumset1, axiom,
% 0.71/0.92    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.71/0.92  thf('0', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.71/0.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.71/0.92  thf(d2_tarski, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.71/0.92       ( ![D:$i]:
% 0.71/0.92         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.71/0.92  thf('1', plain,
% 0.71/0.92      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.71/0.92         (((X4) != (X3))
% 0.71/0.92          | (r2_hidden @ X4 @ X5)
% 0.71/0.92          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.71/0.92      inference('cnf', [status(esa)], [d2_tarski])).
% 0.71/0.92  thf('2', plain,
% 0.71/0.92      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 0.71/0.92      inference('simplify', [status(thm)], ['1'])).
% 0.71/0.92  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.71/0.92      inference('sup+', [status(thm)], ['0', '2'])).
% 0.71/0.92  thf(t62_funct_2, conjecture,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.71/0.92         ( m1_subset_1 @
% 0.71/0.92           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.71/0.92       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.71/0.92         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.71/0.92           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.71/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.71/0.92        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.71/0.92            ( m1_subset_1 @
% 0.71/0.92              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.71/0.92          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.71/0.92            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.71/0.92              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.71/0.92    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.71/0.92  thf('4', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(t6_funct_2, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.92     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.71/0.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.92       ( ( r2_hidden @ C @ A ) =>
% 0.71/0.92         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.71/0.92           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.71/0.92  thf('5', plain,
% 0.71/0.92      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.71/0.92         (~ (r2_hidden @ X54 @ X55)
% 0.71/0.92          | ((X56) = (k1_xboole_0))
% 0.71/0.92          | ~ (v1_funct_1 @ X57)
% 0.71/0.92          | ~ (v1_funct_2 @ X57 @ X55 @ X56)
% 0.71/0.92          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 0.71/0.92          | (r2_hidden @ (k1_funct_1 @ X57 @ X54) @ 
% 0.71/0.92             (k2_relset_1 @ X55 @ X56 @ X57)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.71/0.92  thf('6', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.71/0.92           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.71/0.92          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.71/0.92          | ~ (v1_funct_1 @ sk_C)
% 0.71/0.92          | ((sk_B_1) = (k1_xboole_0))
% 0.71/0.92          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['4', '5'])).
% 0.71/0.92  thf('7', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(redefinition_k2_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.71/0.92  thf('8', plain,
% 0.71/0.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.71/0.92         (((k2_relset_1 @ X50 @ X51 @ X49) = (k2_relat_1 @ X49))
% 0.71/0.92          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51))))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.71/0.92  thf('9', plain,
% 0.71/0.92      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.71/0.92         = (k2_relat_1 @ sk_C))),
% 0.71/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.71/0.92  thf('10', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('12', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.71/0.92          | ((sk_B_1) = (k1_xboole_0))
% 0.71/0.92          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.71/0.92      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 0.71/0.92  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('14', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.71/0.92          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.71/0.92      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.71/0.92  thf('15', plain,
% 0.71/0.92      ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.71/0.92      inference('sup-', [status(thm)], ['3', '14'])).
% 0.71/0.92  thf(t63_subset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( r2_hidden @ A @ B ) =>
% 0.71/0.92       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.71/0.92  thf('16', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i]:
% 0.71/0.92         ((m1_subset_1 @ (k1_tarski @ X16) @ (k1_zfmisc_1 @ X17))
% 0.71/0.92          | ~ (r2_hidden @ X16 @ X17))),
% 0.71/0.92      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.71/0.92  thf('17', plain,
% 0.71/0.92      ((m1_subset_1 @ (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['15', '16'])).
% 0.71/0.92  thf(t3_subset, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.71/0.92  thf('18', plain,
% 0.71/0.92      (![X18 : $i, X19 : $i]:
% 0.71/0.92         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.92  thf('19', plain,
% 0.71/0.92      ((r1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.71/0.92        (k2_relat_1 @ sk_C))),
% 0.71/0.92      inference('sup-', [status(thm)], ['17', '18'])).
% 0.71/0.92  thf(d10_xboole_0, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.71/0.92  thf('20', plain,
% 0.71/0.92      (![X0 : $i, X2 : $i]:
% 0.71/0.92         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.71/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.71/0.92  thf('21', plain,
% 0.71/0.92      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.71/0.92           (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.71/0.92        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['19', '20'])).
% 0.71/0.92  thf('22', plain,
% 0.71/0.92      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.71/0.92         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('23', plain,
% 0.71/0.92      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.71/0.92         = (k2_relat_1 @ sk_C))),
% 0.71/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.71/0.92  thf('24', plain,
% 0.71/0.92      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.71/0.92      inference('demod', [status(thm)], ['22', '23'])).
% 0.71/0.92  thf('25', plain,
% 0.71/0.92      (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.71/0.92          (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.71/0.92      inference('simplify_reflect-', [status(thm)], ['21', '24'])).
% 0.71/0.92  thf(t205_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( v1_relat_1 @ B ) =>
% 0.71/0.92       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.71/0.92         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.71/0.92  thf('26', plain,
% 0.71/0.92      (![X30 : $i, X31 : $i]:
% 0.71/0.92         (((k11_relat_1 @ X30 @ X31) = (k1_xboole_0))
% 0.71/0.92          | (r2_hidden @ X31 @ (k1_relat_1 @ X30))
% 0.71/0.92          | ~ (v1_relat_1 @ X30))),
% 0.71/0.92      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.71/0.92  thf('27', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i]:
% 0.71/0.92         ((m1_subset_1 @ (k1_tarski @ X16) @ (k1_zfmisc_1 @ X17))
% 0.71/0.92          | ~ (r2_hidden @ X16 @ X17))),
% 0.71/0.92      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.71/0.92  thf('28', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ X0)
% 0.71/0.92          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.71/0.92          | (m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ (k1_relat_1 @ X0))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.71/0.92  thf('29', plain,
% 0.71/0.92      (![X18 : $i, X19 : $i]:
% 0.71/0.92         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.92  thf('30', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         (((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.71/0.92          | ~ (v1_relat_1 @ X0)
% 0.71/0.92          | (r1_tarski @ (k1_tarski @ X1) @ (k1_relat_1 @ X0)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['28', '29'])).
% 0.71/0.92  thf('31', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(dt_k1_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.71/0.92  thf('32', plain,
% 0.71/0.92      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.71/0.92         ((m1_subset_1 @ (k1_relset_1 @ X43 @ X44 @ X45) @ (k1_zfmisc_1 @ X43))
% 0.71/0.92          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.71/0.92      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.71/0.92  thf('33', plain,
% 0.71/0.92      ((m1_subset_1 @ (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C) @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['31', '32'])).
% 0.71/0.92  thf('34', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(redefinition_k1_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.71/0.92  thf('35', plain,
% 0.71/0.92      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.71/0.92         (((k1_relset_1 @ X47 @ X48 @ X46) = (k1_relat_1 @ X46))
% 0.71/0.92          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.92  thf('36', plain,
% 0.71/0.92      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.71/0.92         = (k1_relat_1 @ sk_C))),
% 0.71/0.92      inference('sup-', [status(thm)], ['34', '35'])).
% 0.71/0.92  thf('37', plain,
% 0.71/0.92      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.71/0.92      inference('demod', [status(thm)], ['33', '36'])).
% 0.71/0.92  thf('38', plain,
% 0.71/0.92      (![X18 : $i, X19 : $i]:
% 0.71/0.92         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.92  thf('39', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['37', '38'])).
% 0.71/0.92  thf('40', plain,
% 0.71/0.92      (![X0 : $i, X2 : $i]:
% 0.71/0.92         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.71/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.71/0.92  thf('41', plain,
% 0.71/0.92      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C))
% 0.71/0.92        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['39', '40'])).
% 0.71/0.92  thf('42', plain,
% 0.71/0.92      ((~ (v1_relat_1 @ sk_C)
% 0.71/0.92        | ((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.71/0.92        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['30', '41'])).
% 0.71/0.92  thf('43', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(cc1_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( v1_relat_1 @ C ) ))).
% 0.71/0.92  thf('44', plain,
% 0.71/0.92      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.71/0.92         ((v1_relat_1 @ X37)
% 0.71/0.92          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.71/0.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.71/0.92  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.71/0.92      inference('sup-', [status(thm)], ['43', '44'])).
% 0.71/0.92  thf(d16_relat_1, axiom,
% 0.71/0.92    (![A:$i]:
% 0.71/0.92     ( ( v1_relat_1 @ A ) =>
% 0.71/0.92       ( ![B:$i]:
% 0.71/0.92         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.71/0.92  thf('46', plain,
% 0.71/0.92      (![X24 : $i, X25 : $i]:
% 0.71/0.92         (((k11_relat_1 @ X24 @ X25) = (k9_relat_1 @ X24 @ (k1_tarski @ X25)))
% 0.71/0.92          | ~ (v1_relat_1 @ X24))),
% 0.71/0.92      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.71/0.92  thf('47', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(cc2_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.71/0.92  thf('48', plain,
% 0.71/0.92      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.71/0.92         ((v4_relat_1 @ X40 @ X41)
% 0.71/0.92          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.71/0.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.71/0.92  thf('49', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['47', '48'])).
% 0.71/0.92  thf(t209_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.71/0.92       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.71/0.92  thf('50', plain,
% 0.71/0.92      (![X32 : $i, X33 : $i]:
% 0.71/0.92         (((X32) = (k7_relat_1 @ X32 @ X33))
% 0.71/0.92          | ~ (v4_relat_1 @ X32 @ X33)
% 0.71/0.92          | ~ (v1_relat_1 @ X32))),
% 0.71/0.92      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.71/0.92  thf('51', plain,
% 0.71/0.92      ((~ (v1_relat_1 @ sk_C)
% 0.71/0.92        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.71/0.92  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.71/0.92      inference('sup-', [status(thm)], ['43', '44'])).
% 0.71/0.92  thf('53', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.71/0.92      inference('demod', [status(thm)], ['51', '52'])).
% 0.71/0.92  thf(t148_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( v1_relat_1 @ B ) =>
% 0.71/0.92       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.71/0.92  thf('54', plain,
% 0.71/0.92      (![X28 : $i, X29 : $i]:
% 0.71/0.92         (((k2_relat_1 @ (k7_relat_1 @ X28 @ X29)) = (k9_relat_1 @ X28 @ X29))
% 0.71/0.92          | ~ (v1_relat_1 @ X28))),
% 0.71/0.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.71/0.92  thf('55', plain,
% 0.71/0.92      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.71/0.92        | ~ (v1_relat_1 @ sk_C))),
% 0.71/0.92      inference('sup+', [status(thm)], ['53', '54'])).
% 0.71/0.92  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.71/0.92      inference('sup-', [status(thm)], ['43', '44'])).
% 0.71/0.92  thf('57', plain,
% 0.71/0.92      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.71/0.92      inference('demod', [status(thm)], ['55', '56'])).
% 0.71/0.92  thf('58', plain,
% 0.71/0.92      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.71/0.92        | ~ (v1_relat_1 @ sk_C))),
% 0.71/0.92      inference('sup+', [status(thm)], ['46', '57'])).
% 0.71/0.92  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.71/0.92      inference('sup-', [status(thm)], ['43', '44'])).
% 0.71/0.92  thf('60', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.71/0.92      inference('demod', [status(thm)], ['58', '59'])).
% 0.71/0.92  thf('61', plain,
% 0.71/0.92      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.71/0.92        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.71/0.92      inference('demod', [status(thm)], ['42', '45', '60'])).
% 0.71/0.92  thf(t14_funct_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.71/0.92       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.71/0.92         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.71/0.92  thf('62', plain,
% 0.71/0.92      (![X35 : $i, X36 : $i]:
% 0.71/0.92         (((k1_relat_1 @ X36) != (k1_tarski @ X35))
% 0.71/0.92          | ((k2_relat_1 @ X36) = (k1_tarski @ (k1_funct_1 @ X36 @ X35)))
% 0.71/0.92          | ~ (v1_funct_1 @ X36)
% 0.71/0.92          | ~ (v1_relat_1 @ X36))),
% 0.71/0.92      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.71/0.92  thf('63', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.71/0.92          | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.71/0.92          | ~ (v1_relat_1 @ X0)
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['61', '62'])).
% 0.71/0.92  thf('64', plain,
% 0.71/0.92      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.71/0.92        | ~ (v1_funct_1 @ sk_C)
% 0.71/0.92        | ~ (v1_relat_1 @ sk_C)
% 0.71/0.92        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.71/0.92      inference('eq_res', [status(thm)], ['63'])).
% 0.71/0.92  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.71/0.92      inference('sup-', [status(thm)], ['43', '44'])).
% 0.71/0.92  thf('67', plain,
% 0.71/0.92      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.71/0.92        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.71/0.92      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.71/0.92  thf('68', plain,
% 0.71/0.92      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.71/0.92      inference('demod', [status(thm)], ['22', '23'])).
% 0.71/0.92  thf('69', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.71/0.92      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.71/0.92  thf(t4_subset_1, axiom,
% 0.71/0.92    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.71/0.92  thf('70', plain,
% 0.71/0.92      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.71/0.92      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.71/0.92  thf('71', plain,
% 0.71/0.92      (![X18 : $i, X19 : $i]:
% 0.71/0.92         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.92  thf('72', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.71/0.92      inference('sup-', [status(thm)], ['70', '71'])).
% 0.71/0.92  thf('73', plain, ($false),
% 0.71/0.92      inference('demod', [status(thm)], ['25', '69', '72'])).
% 0.71/0.92  
% 0.71/0.92  % SZS output end Refutation
% 0.71/0.92  
% 0.71/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
