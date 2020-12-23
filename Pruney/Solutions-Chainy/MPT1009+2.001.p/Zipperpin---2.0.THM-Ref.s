%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eRq145W2gi

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:48 EST 2020

% Result     : Theorem 3.70s
% Output     : Refutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 646 expanded)
%              Number of leaves         :   48 ( 218 expanded)
%              Depth                    :   16
%              Number of atoms          : 1054 (6491 expanded)
%              Number of equality atoms :   62 ( 230 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( ( k7_relset_1 @ X51 @ X52 @ X50 @ X53 )
        = ( k9_relat_1 @ X50 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('5',plain,(
    ! [X54: $i] :
      ( ( X54 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X54 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v4_relat_1 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) @ X33 )
      | ~ ( v4_relat_1 @ X32 @ X34 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X35: $i,X36: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v4_relat_1 @ X29 @ X30 )
      | ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) )
      | ~ ( v4_relat_1 @ X32 @ X34 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('23',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X43: $i] :
      ( ( ( k1_relat_1 @ X43 )
       != k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_D @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('35',plain,(
    ! [X44: $i] :
      ( ( ( k7_relat_1 @ X44 @ ( k1_relat_1 @ X44 ) )
        = X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('37',plain,
    ( ( v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('39',plain,(
    v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41
        = ( k7_relat_1 @ X41 @ X42 ) )
      | ~ ( v4_relat_1 @ X41 @ X42 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('43',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_D = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('46',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v4_relat_1 @ X29 @ X30 )
      | ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('49',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
        = ( k1_tarski @ X17 ) )
      | ( X18 = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k1_relat_1 @ X46 )
       != ( k1_tarski @ X45 ) )
      | ( ( k2_relat_1 @ X46 )
        = ( k1_tarski @ ( k1_funct_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('61',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41
        = ( k7_relat_1 @ X41 @ X42 ) )
      | ~ ( v4_relat_1 @ X41 @ X42 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('64',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X39 @ X40 ) )
        = ( k9_relat_1 @ X39 @ X40 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('66',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X37 @ X38 ) @ ( k2_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('68',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( v4_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) )
      | ~ ( v4_relat_1 @ X32 @ X34 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['64','77'])).

thf('79',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('80',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X39 @ X40 ) )
        = ( k9_relat_1 @ X39 @ X40 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('81',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','85'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','86','87'])).

thf('89',plain,(
    ! [X54: $i] :
      ( ( X54 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X54 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('90',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('92',plain,(
    ! [X31: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('93',plain,(
    ! [X54: $i] :
      ( ( X54 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X54 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X37 @ X38 ) @ ( k2_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','108'])).

thf('110',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','86','87'])).

thf('111',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','108'])).

thf('114',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['4','88','109','110','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eRq145W2gi
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:40:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.70/3.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.70/3.89  % Solved by: fo/fo7.sh
% 3.70/3.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.70/3.89  % done 5647 iterations in 3.431s
% 3.70/3.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.70/3.89  % SZS output start Refutation
% 3.70/3.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.70/3.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.70/3.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.70/3.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.70/3.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.70/3.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.70/3.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.70/3.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.70/3.89  thf(sk_A_type, type, sk_A: $i).
% 3.70/3.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.70/3.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.70/3.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.70/3.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.70/3.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.70/3.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.70/3.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.70/3.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.70/3.89  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.70/3.89  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.70/3.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.70/3.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.70/3.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.70/3.89  thf(sk_D_type, type, sk_D: $i).
% 3.70/3.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.70/3.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.70/3.89  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 3.70/3.89  thf(t64_funct_2, conjecture,
% 3.70/3.89    (![A:$i,B:$i,C:$i,D:$i]:
% 3.70/3.89     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 3.70/3.89         ( m1_subset_1 @
% 3.70/3.89           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 3.70/3.89       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 3.70/3.89         ( r1_tarski @
% 3.70/3.89           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 3.70/3.89           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 3.70/3.89  thf(zf_stmt_0, negated_conjecture,
% 3.70/3.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.70/3.89        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 3.70/3.89            ( m1_subset_1 @
% 3.70/3.89              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 3.70/3.89          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 3.70/3.89            ( r1_tarski @
% 3.70/3.89              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 3.70/3.89              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 3.70/3.89    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 3.70/3.89  thf('0', plain,
% 3.70/3.89      (~ (r1_tarski @ 
% 3.70/3.89          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_D @ sk_C_1) @ 
% 3.70/3.89          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 3.70/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.89  thf('1', plain,
% 3.70/3.89      ((m1_subset_1 @ sk_D @ 
% 3.70/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 3.70/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.89  thf(redefinition_k7_relset_1, axiom,
% 3.70/3.89    (![A:$i,B:$i,C:$i,D:$i]:
% 3.70/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.70/3.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 3.70/3.89  thf('2', plain,
% 3.70/3.89      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 3.70/3.89         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 3.70/3.89          | ((k7_relset_1 @ X51 @ X52 @ X50 @ X53) = (k9_relat_1 @ X50 @ X53)))),
% 3.70/3.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.70/3.89  thf('3', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_D @ X0)
% 3.70/3.89           = (k9_relat_1 @ sk_D @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['1', '2'])).
% 3.70/3.89  thf('4', plain,
% 3.70/3.89      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ 
% 3.70/3.89          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 3.70/3.89      inference('demod', [status(thm)], ['0', '3'])).
% 3.70/3.89  thf(t6_mcart_1, axiom,
% 3.70/3.89    (![A:$i]:
% 3.70/3.89     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.70/3.89          ( ![B:$i]:
% 3.70/3.89            ( ~( ( r2_hidden @ B @ A ) & 
% 3.70/3.89                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 3.70/3.89                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 3.70/3.89                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 3.70/3.89                       ( r2_hidden @ G @ B ) ) =>
% 3.70/3.89                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 3.70/3.89  thf('5', plain,
% 3.70/3.89      (![X54 : $i]:
% 3.70/3.89         (((X54) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X54) @ X54))),
% 3.70/3.89      inference('cnf', [status(esa)], [t6_mcart_1])).
% 3.70/3.89  thf('6', plain,
% 3.70/3.89      ((m1_subset_1 @ sk_D @ 
% 3.70/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 3.70/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.89  thf(cc2_relset_1, axiom,
% 3.70/3.89    (![A:$i,B:$i,C:$i]:
% 3.70/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.70/3.89       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.70/3.89  thf('7', plain,
% 3.70/3.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 3.70/3.89         ((v4_relat_1 @ X47 @ X48)
% 3.70/3.89          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 3.70/3.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.70/3.89  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 3.70/3.89      inference('sup-', [status(thm)], ['6', '7'])).
% 3.70/3.89  thf(fc23_relat_1, axiom,
% 3.70/3.89    (![A:$i,B:$i,C:$i]:
% 3.70/3.89     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 3.70/3.89       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 3.70/3.89         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 3.70/3.89         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 3.70/3.89  thf('9', plain,
% 3.70/3.89      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.70/3.89         ((v4_relat_1 @ (k7_relat_1 @ X32 @ X33) @ X33)
% 3.70/3.89          | ~ (v4_relat_1 @ X32 @ X34)
% 3.70/3.89          | ~ (v1_relat_1 @ X32))),
% 3.70/3.89      inference('cnf', [status(esa)], [fc23_relat_1])).
% 3.70/3.89  thf('10', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['8', '9'])).
% 3.70/3.89  thf('11', plain,
% 3.70/3.89      ((m1_subset_1 @ sk_D @ 
% 3.70/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 3.70/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.89  thf(cc2_relat_1, axiom,
% 3.70/3.89    (![A:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ A ) =>
% 3.70/3.89       ( ![B:$i]:
% 3.70/3.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.70/3.89  thf('12', plain,
% 3.70/3.89      (![X27 : $i, X28 : $i]:
% 3.70/3.89         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 3.70/3.89          | (v1_relat_1 @ X27)
% 3.70/3.89          | ~ (v1_relat_1 @ X28))),
% 3.70/3.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.70/3.89  thf('13', plain,
% 3.70/3.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 3.70/3.89        | (v1_relat_1 @ sk_D))),
% 3.70/3.89      inference('sup-', [status(thm)], ['11', '12'])).
% 3.70/3.89  thf(fc6_relat_1, axiom,
% 3.70/3.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.70/3.89  thf('14', plain,
% 3.70/3.89      (![X35 : $i, X36 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X35 @ X36))),
% 3.70/3.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.70/3.89  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.89      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.89  thf('16', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 3.70/3.89      inference('demod', [status(thm)], ['10', '15'])).
% 3.70/3.89  thf(d18_relat_1, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ B ) =>
% 3.70/3.89       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.70/3.89  thf('17', plain,
% 3.70/3.89      (![X29 : $i, X30 : $i]:
% 3.70/3.89         (~ (v4_relat_1 @ X29 @ X30)
% 3.70/3.89          | (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 3.70/3.89          | ~ (v1_relat_1 @ X29))),
% 3.70/3.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.70/3.89  thf('18', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.70/3.89          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['16', '17'])).
% 3.70/3.89  thf('19', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 3.70/3.89      inference('sup-', [status(thm)], ['6', '7'])).
% 3.70/3.89  thf('20', plain,
% 3.70/3.89      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.70/3.89         ((v1_relat_1 @ (k7_relat_1 @ X32 @ X33))
% 3.70/3.89          | ~ (v4_relat_1 @ X32 @ X34)
% 3.70/3.89          | ~ (v1_relat_1 @ X32))),
% 3.70/3.89      inference('cnf', [status(esa)], [fc23_relat_1])).
% 3.70/3.89  thf('21', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 3.70/3.89      inference('sup-', [status(thm)], ['19', '20'])).
% 3.70/3.89  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.89      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.89  thf('23', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.70/3.89      inference('demod', [status(thm)], ['21', '22'])).
% 3.70/3.89  thf('24', plain,
% 3.70/3.89      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 3.70/3.89      inference('demod', [status(thm)], ['18', '23'])).
% 3.70/3.89  thf(t3_subset, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.70/3.89  thf('25', plain,
% 3.70/3.89      (![X20 : $i, X22 : $i]:
% 3.70/3.89         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 3.70/3.89      inference('cnf', [status(esa)], [t3_subset])).
% 3.70/3.89  thf('26', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (m1_subset_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 3.70/3.89          (k1_zfmisc_1 @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['24', '25'])).
% 3.70/3.89  thf(t5_subset, axiom,
% 3.70/3.89    (![A:$i,B:$i,C:$i]:
% 3.70/3.89     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.70/3.89          ( v1_xboole_0 @ C ) ) ))).
% 3.70/3.89  thf('27', plain,
% 3.70/3.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.70/3.89         (~ (r2_hidden @ X23 @ X24)
% 3.70/3.89          | ~ (v1_xboole_0 @ X25)
% 3.70/3.89          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 3.70/3.89      inference('cnf', [status(esa)], [t5_subset])).
% 3.70/3.89  thf('28', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (~ (v1_xboole_0 @ X0)
% 3.70/3.89          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))))),
% 3.70/3.90      inference('sup-', [status(thm)], ['26', '27'])).
% 3.70/3.90  thf('29', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         (((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k1_xboole_0))
% 3.70/3.90          | ~ (v1_xboole_0 @ X0))),
% 3.70/3.90      inference('sup-', [status(thm)], ['5', '28'])).
% 3.70/3.90  thf(t64_relat_1, axiom,
% 3.70/3.90    (![A:$i]:
% 3.70/3.90     ( ( v1_relat_1 @ A ) =>
% 3.70/3.90       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 3.70/3.90           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.70/3.90         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 3.70/3.90  thf('30', plain,
% 3.70/3.90      (![X43 : $i]:
% 3.70/3.90         (((k1_relat_1 @ X43) != (k1_xboole_0))
% 3.70/3.90          | ((X43) = (k1_xboole_0))
% 3.70/3.90          | ~ (v1_relat_1 @ X43))),
% 3.70/3.90      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.70/3.90  thf('31', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         (((k1_xboole_0) != (k1_xboole_0))
% 3.70/3.90          | ~ (v1_xboole_0 @ X0)
% 3.70/3.90          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.70/3.90          | ((k7_relat_1 @ sk_D @ X0) = (k1_xboole_0)))),
% 3.70/3.90      inference('sup-', [status(thm)], ['29', '30'])).
% 3.70/3.90  thf('32', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.70/3.90      inference('demod', [status(thm)], ['21', '22'])).
% 3.70/3.90  thf('33', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         (((k1_xboole_0) != (k1_xboole_0))
% 3.70/3.90          | ~ (v1_xboole_0 @ X0)
% 3.70/3.90          | ((k7_relat_1 @ sk_D @ X0) = (k1_xboole_0)))),
% 3.70/3.90      inference('demod', [status(thm)], ['31', '32'])).
% 3.70/3.90  thf('34', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         (((k7_relat_1 @ sk_D @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.70/3.90      inference('simplify', [status(thm)], ['33'])).
% 3.70/3.90  thf(t98_relat_1, axiom,
% 3.70/3.90    (![A:$i]:
% 3.70/3.90     ( ( v1_relat_1 @ A ) =>
% 3.70/3.90       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 3.70/3.90  thf('35', plain,
% 3.70/3.90      (![X44 : $i]:
% 3.70/3.90         (((k7_relat_1 @ X44 @ (k1_relat_1 @ X44)) = (X44))
% 3.70/3.90          | ~ (v1_relat_1 @ X44))),
% 3.70/3.90      inference('cnf', [status(esa)], [t98_relat_1])).
% 3.70/3.90  thf('36', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 3.70/3.90      inference('demod', [status(thm)], ['10', '15'])).
% 3.70/3.90  thf('37', plain,
% 3.70/3.90      (((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 3.70/3.90      inference('sup+', [status(thm)], ['35', '36'])).
% 3.70/3.90  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.90      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.90  thf('39', plain, ((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))),
% 3.70/3.90      inference('demod', [status(thm)], ['37', '38'])).
% 3.70/3.90  thf(t209_relat_1, axiom,
% 3.70/3.90    (![A:$i,B:$i]:
% 3.70/3.90     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 3.70/3.90       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 3.70/3.90  thf('40', plain,
% 3.70/3.90      (![X41 : $i, X42 : $i]:
% 3.70/3.90         (((X41) = (k7_relat_1 @ X41 @ X42))
% 3.70/3.90          | ~ (v4_relat_1 @ X41 @ X42)
% 3.70/3.90          | ~ (v1_relat_1 @ X41))),
% 3.70/3.90      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.70/3.90  thf('41', plain,
% 3.70/3.90      ((~ (v1_relat_1 @ sk_D)
% 3.70/3.90        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 3.70/3.90      inference('sup-', [status(thm)], ['39', '40'])).
% 3.70/3.90  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.90      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.90  thf('43', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 3.70/3.90      inference('demod', [status(thm)], ['41', '42'])).
% 3.70/3.90  thf('44', plain,
% 3.70/3.90      ((((sk_D) = (k1_xboole_0)) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_D)))),
% 3.70/3.90      inference('sup+', [status(thm)], ['34', '43'])).
% 3.70/3.90  thf('45', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 3.70/3.90      inference('sup-', [status(thm)], ['6', '7'])).
% 3.70/3.90  thf('46', plain,
% 3.70/3.90      (![X29 : $i, X30 : $i]:
% 3.70/3.90         (~ (v4_relat_1 @ X29 @ X30)
% 3.70/3.90          | (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 3.70/3.90          | ~ (v1_relat_1 @ X29))),
% 3.70/3.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.70/3.90  thf('47', plain,
% 3.70/3.90      ((~ (v1_relat_1 @ sk_D)
% 3.70/3.90        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 3.70/3.90      inference('sup-', [status(thm)], ['45', '46'])).
% 3.70/3.90  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.90      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.90  thf('49', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 3.70/3.90      inference('demod', [status(thm)], ['47', '48'])).
% 3.70/3.90  thf(l3_zfmisc_1, axiom,
% 3.70/3.90    (![A:$i,B:$i]:
% 3.70/3.90     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 3.70/3.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 3.70/3.90  thf('50', plain,
% 3.70/3.90      (![X17 : $i, X18 : $i]:
% 3.70/3.90         (((X18) = (k1_tarski @ X17))
% 3.70/3.90          | ((X18) = (k1_xboole_0))
% 3.70/3.90          | ~ (r1_tarski @ X18 @ (k1_tarski @ X17)))),
% 3.70/3.90      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 3.70/3.90  thf('51', plain,
% 3.70/3.90      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 3.70/3.90        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.70/3.90      inference('sup-', [status(thm)], ['49', '50'])).
% 3.70/3.90  thf(t14_funct_1, axiom,
% 3.70/3.90    (![A:$i,B:$i]:
% 3.70/3.90     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.70/3.90       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 3.70/3.90         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 3.70/3.90  thf('52', plain,
% 3.70/3.90      (![X45 : $i, X46 : $i]:
% 3.70/3.90         (((k1_relat_1 @ X46) != (k1_tarski @ X45))
% 3.70/3.90          | ((k2_relat_1 @ X46) = (k1_tarski @ (k1_funct_1 @ X46 @ X45)))
% 3.70/3.90          | ~ (v1_funct_1 @ X46)
% 3.70/3.90          | ~ (v1_relat_1 @ X46))),
% 3.70/3.90      inference('cnf', [status(esa)], [t14_funct_1])).
% 3.70/3.90  thf('53', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 3.70/3.90          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 3.70/3.90          | ~ (v1_relat_1 @ X0)
% 3.70/3.90          | ~ (v1_funct_1 @ X0)
% 3.70/3.90          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 3.70/3.90      inference('sup-', [status(thm)], ['51', '52'])).
% 3.70/3.90  thf('54', plain,
% 3.70/3.90      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 3.70/3.90        | ~ (v1_funct_1 @ sk_D)
% 3.70/3.90        | ~ (v1_relat_1 @ sk_D)
% 3.70/3.90        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 3.70/3.90      inference('eq_res', [status(thm)], ['53'])).
% 3.70/3.90  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 3.70/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.90  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.90      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.90  thf('57', plain,
% 3.70/3.90      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 3.70/3.90        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 3.70/3.90      inference('demod', [status(thm)], ['54', '55', '56'])).
% 3.70/3.90  thf('58', plain,
% 3.70/3.90      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ 
% 3.70/3.90          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 3.70/3.90      inference('demod', [status(thm)], ['0', '3'])).
% 3.70/3.90  thf('59', plain,
% 3.70/3.90      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))
% 3.70/3.90        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 3.70/3.90      inference('sup-', [status(thm)], ['57', '58'])).
% 3.70/3.90  thf('60', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 3.70/3.90      inference('sup-', [status(thm)], ['6', '7'])).
% 3.70/3.90  thf('61', plain,
% 3.70/3.90      (![X41 : $i, X42 : $i]:
% 3.70/3.90         (((X41) = (k7_relat_1 @ X41 @ X42))
% 3.70/3.90          | ~ (v4_relat_1 @ X41 @ X42)
% 3.70/3.90          | ~ (v1_relat_1 @ X41))),
% 3.70/3.90      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.70/3.90  thf('62', plain,
% 3.70/3.90      ((~ (v1_relat_1 @ sk_D)
% 3.70/3.90        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 3.70/3.90      inference('sup-', [status(thm)], ['60', '61'])).
% 3.70/3.90  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.90      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.90  thf('64', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 3.70/3.90      inference('demod', [status(thm)], ['62', '63'])).
% 3.70/3.90  thf(t148_relat_1, axiom,
% 3.70/3.90    (![A:$i,B:$i]:
% 3.70/3.90     ( ( v1_relat_1 @ B ) =>
% 3.70/3.90       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.70/3.90  thf('65', plain,
% 3.70/3.90      (![X39 : $i, X40 : $i]:
% 3.70/3.90         (((k2_relat_1 @ (k7_relat_1 @ X39 @ X40)) = (k9_relat_1 @ X39 @ X40))
% 3.70/3.90          | ~ (v1_relat_1 @ X39))),
% 3.70/3.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.70/3.90  thf(t144_relat_1, axiom,
% 3.70/3.90    (![A:$i,B:$i]:
% 3.70/3.90     ( ( v1_relat_1 @ B ) =>
% 3.70/3.90       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 3.70/3.90  thf('66', plain,
% 3.70/3.90      (![X37 : $i, X38 : $i]:
% 3.70/3.90         ((r1_tarski @ (k9_relat_1 @ X37 @ X38) @ (k2_relat_1 @ X37))
% 3.70/3.90          | ~ (v1_relat_1 @ X37))),
% 3.70/3.90      inference('cnf', [status(esa)], [t144_relat_1])).
% 3.70/3.90  thf('67', plain,
% 3.70/3.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.70/3.90         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 3.70/3.90           (k9_relat_1 @ X1 @ X0))
% 3.70/3.90          | ~ (v1_relat_1 @ X1)
% 3.70/3.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.70/3.90      inference('sup+', [status(thm)], ['65', '66'])).
% 3.70/3.90  thf(d3_tarski, axiom,
% 3.70/3.90    (![A:$i,B:$i]:
% 3.70/3.90     ( ( r1_tarski @ A @ B ) <=>
% 3.70/3.90       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.70/3.90  thf('68', plain,
% 3.70/3.90      (![X4 : $i, X6 : $i]:
% 3.70/3.90         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.70/3.90      inference('cnf', [status(esa)], [d3_tarski])).
% 3.70/3.90  thf('69', plain,
% 3.70/3.90      (![X4 : $i, X6 : $i]:
% 3.70/3.90         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 3.70/3.90      inference('cnf', [status(esa)], [d3_tarski])).
% 3.70/3.90  thf('70', plain,
% 3.70/3.90      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 3.70/3.90      inference('sup-', [status(thm)], ['68', '69'])).
% 3.70/3.90  thf('71', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.70/3.90      inference('simplify', [status(thm)], ['70'])).
% 3.70/3.90  thf('72', plain,
% 3.70/3.90      (![X29 : $i, X30 : $i]:
% 3.70/3.90         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 3.70/3.90          | (v4_relat_1 @ X29 @ X30)
% 3.70/3.90          | ~ (v1_relat_1 @ X29))),
% 3.70/3.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.70/3.90  thf('73', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 3.70/3.90      inference('sup-', [status(thm)], ['71', '72'])).
% 3.70/3.90  thf('74', plain,
% 3.70/3.90      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.70/3.90         ((v1_relat_1 @ (k7_relat_1 @ X32 @ X33))
% 3.70/3.90          | ~ (v4_relat_1 @ X32 @ X34)
% 3.70/3.90          | ~ (v1_relat_1 @ X32))),
% 3.70/3.90      inference('cnf', [status(esa)], [fc23_relat_1])).
% 3.70/3.90  thf('75', plain,
% 3.70/3.90      (![X0 : $i, X1 : $i]:
% 3.70/3.90         (~ (v1_relat_1 @ X0)
% 3.70/3.90          | ~ (v1_relat_1 @ X0)
% 3.70/3.90          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 3.70/3.90      inference('sup-', [status(thm)], ['73', '74'])).
% 3.70/3.90  thf('76', plain,
% 3.70/3.90      (![X0 : $i, X1 : $i]:
% 3.70/3.90         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 3.70/3.90      inference('simplify', [status(thm)], ['75'])).
% 3.70/3.90  thf('77', plain,
% 3.70/3.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.70/3.90         (~ (v1_relat_1 @ X1)
% 3.70/3.90          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 3.70/3.90             (k9_relat_1 @ X1 @ X0)))),
% 3.70/3.90      inference('clc', [status(thm)], ['67', '76'])).
% 3.70/3.90  thf('78', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ 
% 3.70/3.90           (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 3.70/3.90          | ~ (v1_relat_1 @ sk_D))),
% 3.70/3.90      inference('sup+', [status(thm)], ['64', '77'])).
% 3.70/3.90  thf('79', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 3.70/3.90      inference('demod', [status(thm)], ['62', '63'])).
% 3.70/3.90  thf('80', plain,
% 3.70/3.90      (![X39 : $i, X40 : $i]:
% 3.70/3.90         (((k2_relat_1 @ (k7_relat_1 @ X39 @ X40)) = (k9_relat_1 @ X39 @ X40))
% 3.70/3.90          | ~ (v1_relat_1 @ X39))),
% 3.70/3.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.70/3.90  thf('81', plain,
% 3.70/3.90      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 3.70/3.90        | ~ (v1_relat_1 @ sk_D))),
% 3.70/3.90      inference('sup+', [status(thm)], ['79', '80'])).
% 3.70/3.90  thf('82', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.90      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.90  thf('83', plain,
% 3.70/3.90      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 3.70/3.90      inference('demod', [status(thm)], ['81', '82'])).
% 3.70/3.90  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.90      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.90  thf('85', plain,
% 3.70/3.90      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 3.70/3.90      inference('demod', [status(thm)], ['78', '83', '84'])).
% 3.70/3.90  thf('86', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 3.70/3.90      inference('demod', [status(thm)], ['59', '85'])).
% 3.70/3.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.70/3.90  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.70/3.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.70/3.90  thf('88', plain, (((sk_D) = (k1_xboole_0))),
% 3.70/3.90      inference('demod', [status(thm)], ['44', '86', '87'])).
% 3.70/3.90  thf('89', plain,
% 3.70/3.90      (![X54 : $i]:
% 3.70/3.90         (((X54) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X54) @ X54))),
% 3.70/3.90      inference('cnf', [status(esa)], [t6_mcart_1])).
% 3.70/3.90  thf(cc1_relat_1, axiom,
% 3.70/3.90    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 3.70/3.90  thf('90', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 3.70/3.90      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.70/3.90  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.70/3.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.70/3.90  thf(fc11_relat_1, axiom,
% 3.70/3.90    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 3.70/3.90  thf('92', plain,
% 3.70/3.90      (![X31 : $i]:
% 3.70/3.90         ((v1_xboole_0 @ (k2_relat_1 @ X31)) | ~ (v1_xboole_0 @ X31))),
% 3.70/3.90      inference('cnf', [status(esa)], [fc11_relat_1])).
% 3.70/3.90  thf('93', plain,
% 3.70/3.90      (![X54 : $i]:
% 3.70/3.90         (((X54) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X54) @ X54))),
% 3.70/3.90      inference('cnf', [status(esa)], [t6_mcart_1])).
% 3.70/3.90  thf(d1_xboole_0, axiom,
% 3.70/3.90    (![A:$i]:
% 3.70/3.90     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.70/3.90  thf('94', plain,
% 3.70/3.90      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.70/3.90      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.70/3.90  thf('95', plain,
% 3.70/3.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.70/3.90      inference('sup-', [status(thm)], ['93', '94'])).
% 3.70/3.90  thf('96', plain,
% 3.70/3.90      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 3.70/3.90      inference('sup-', [status(thm)], ['92', '95'])).
% 3.70/3.90  thf('97', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.70/3.90      inference('sup-', [status(thm)], ['91', '96'])).
% 3.70/3.90  thf('98', plain,
% 3.70/3.90      (![X37 : $i, X38 : $i]:
% 3.70/3.90         ((r1_tarski @ (k9_relat_1 @ X37 @ X38) @ (k2_relat_1 @ X37))
% 3.70/3.90          | ~ (v1_relat_1 @ X37))),
% 3.70/3.90      inference('cnf', [status(esa)], [t144_relat_1])).
% 3.70/3.90  thf('99', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 3.70/3.90          | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.70/3.90      inference('sup+', [status(thm)], ['97', '98'])).
% 3.70/3.90  thf('100', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.70/3.90          | (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 3.70/3.90      inference('sup-', [status(thm)], ['90', '99'])).
% 3.70/3.90  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.70/3.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.70/3.90  thf('102', plain,
% 3.70/3.90      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 3.70/3.90      inference('demod', [status(thm)], ['100', '101'])).
% 3.70/3.90  thf('103', plain,
% 3.70/3.90      (![X20 : $i, X22 : $i]:
% 3.70/3.90         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 3.70/3.90      inference('cnf', [status(esa)], [t3_subset])).
% 3.70/3.90  thf('104', plain,
% 3.70/3.90      (![X0 : $i]:
% 3.70/3.90         (m1_subset_1 @ (k9_relat_1 @ k1_xboole_0 @ X0) @ 
% 3.70/3.90          (k1_zfmisc_1 @ k1_xboole_0))),
% 3.70/3.90      inference('sup-', [status(thm)], ['102', '103'])).
% 3.70/3.90  thf('105', plain,
% 3.70/3.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.70/3.90         (~ (r2_hidden @ X23 @ X24)
% 3.70/3.90          | ~ (v1_xboole_0 @ X25)
% 3.70/3.90          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 3.70/3.90      inference('cnf', [status(esa)], [t5_subset])).
% 3.70/3.90  thf('106', plain,
% 3.70/3.90      (![X0 : $i, X1 : $i]:
% 3.70/3.90         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.70/3.90          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ k1_xboole_0 @ X0)))),
% 3.70/3.90      inference('sup-', [status(thm)], ['104', '105'])).
% 3.70/3.90  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.70/3.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.70/3.90  thf('108', plain,
% 3.70/3.90      (![X0 : $i, X1 : $i]:
% 3.70/3.90         ~ (r2_hidden @ X1 @ (k9_relat_1 @ k1_xboole_0 @ X0))),
% 3.70/3.90      inference('demod', [status(thm)], ['106', '107'])).
% 3.70/3.90  thf('109', plain,
% 3.70/3.90      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.70/3.90      inference('sup-', [status(thm)], ['89', '108'])).
% 3.70/3.90  thf('110', plain, (((sk_D) = (k1_xboole_0))),
% 3.70/3.90      inference('demod', [status(thm)], ['44', '86', '87'])).
% 3.70/3.90  thf('111', plain,
% 3.70/3.90      (![X4 : $i, X6 : $i]:
% 3.70/3.90         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.70/3.90      inference('cnf', [status(esa)], [d3_tarski])).
% 3.70/3.90  thf('112', plain,
% 3.70/3.90      (![X0 : $i, X1 : $i]:
% 3.70/3.90         ~ (r2_hidden @ X1 @ (k9_relat_1 @ k1_xboole_0 @ X0))),
% 3.70/3.90      inference('demod', [status(thm)], ['106', '107'])).
% 3.70/3.90  thf('113', plain,
% 3.70/3.90      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.70/3.90      inference('sup-', [status(thm)], ['89', '108'])).
% 3.70/3.90  thf('114', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 3.70/3.90      inference('demod', [status(thm)], ['112', '113'])).
% 3.70/3.90  thf('115', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.70/3.90      inference('sup-', [status(thm)], ['111', '114'])).
% 3.70/3.90  thf('116', plain, ($false),
% 3.70/3.90      inference('demod', [status(thm)], ['4', '88', '109', '110', '115'])).
% 3.70/3.90  
% 3.70/3.90  % SZS output end Refutation
% 3.70/3.90  
% 3.70/3.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
