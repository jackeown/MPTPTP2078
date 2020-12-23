%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GaC3SzwGgu

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 135 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  792 (1861 expanded)
%              Number of equality atoms :   70 ( 143 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t49_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) )
                = k1_xboole_0 ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) )
                  = k1_xboole_0 ) )
        <=> ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_funct_2])).

thf('0',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X25: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k1_tarski @ X11 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X11 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_C @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k8_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k10_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) )
   <= ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B ) )
   <= ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B ) )
   <= ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X25: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X25: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X25 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ~ ! [X25: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X25 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
   <= ( r2_hidden @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('42',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('43',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('45',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X10 ) )
      | ( ( k10_relat_1 @ X10 @ ( k1_tarski @ X11 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_D @ sk_B ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','37','39','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GaC3SzwGgu
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 79 iterations in 0.033s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(t49_funct_2, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( ![D:$i]:
% 0.20/0.53           ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.53                ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.20/0.53                  ( k1_xboole_0 ) ) ) ) ) <=>
% 0.20/0.53         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.53            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53          ( ( ![D:$i]:
% 0.20/0.53              ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.53                   ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.20/0.53                     ( k1_xboole_0 ) ) ) ) ) <=>
% 0.20/0.53            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t49_funct_2])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.20/0.53        | (r2_hidden @ sk_D @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (((r2_hidden @ sk_D @ sk_B)) | 
% 0.20/0.53       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X25 : $i]:
% 0.20/0.53         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))
% 0.20/0.53          | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53              != (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X25 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      ((![X25 : $i]:
% 0.20/0.53          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53             != (k1_xboole_0))
% 0.20/0.53           | ~ (r2_hidden @ X25 @ sk_B))) | 
% 0.20/0.53       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf(t142_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.53         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X10 @ (k1_tarski @ X11)) = (k1_xboole_0))
% 0.20/0.53          | (r2_hidden @ X11 @ (k2_relat_1 @ X10))
% 0.20/0.53          | ~ (v1_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k10_relat_1 @ X0 @ (k1_tarski @ (sk_C @ (k2_relat_1 @ X0) @ X1)))
% 0.20/0.53              = (k1_xboole_0))
% 0.20/0.53          | (r1_tarski @ X1 @ (k2_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.53          | ((k8_relset_1 @ X22 @ X23 @ X21 @ X24) = (k10_relat_1 @ X21 @ X24)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.20/0.53           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((![X25 : $i]:
% 0.20/0.53          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53             != (k1_xboole_0))
% 0.20/0.53           | ~ (r2_hidden @ X25 @ sk_B)))
% 0.20/0.53         <= ((![X25 : $i]:
% 0.20/0.53                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53                   != (k1_xboole_0))
% 0.20/0.53                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.20/0.53         <= ((![X25 : $i]:
% 0.20/0.53                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53                   != (k1_xboole_0))
% 0.20/0.53                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53           | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.53           | ~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ sk_B)))
% 0.20/0.53         <= ((![X25 : $i]:
% 0.20/0.53                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53                   != (k1_xboole_0))
% 0.20/0.53                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( v1_relat_1 @ C ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.53         ((v1_relat_1 @ X12)
% 0.20/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.53  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53           | ~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ sk_B)))
% 0.20/0.53         <= ((![X25 : $i]:
% 0.20/0.53                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53                   != (k1_xboole_0))
% 0.20/0.53                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ sk_B)
% 0.20/0.53           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))))
% 0.20/0.53         <= ((![X25 : $i]:
% 0.20/0.53                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53                   != (k1_xboole_0))
% 0.20/0.53                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))))
% 0.20/0.53         <= ((![X25 : $i]:
% 0.20/0.53                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53                   != (k1_xboole_0))
% 0.20/0.53                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.53         <= ((![X25 : $i]:
% 0.20/0.53                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53                   != (k1_xboole_0))
% 0.20/0.53                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         ((v5_relat_1 @ X15 @ X17)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('23', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf(d19_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (v5_relat_1 @ X8 @ X9)
% 0.20/0.53          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.20/0.53          | ~ (v1_relat_1 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X4 : $i, X6 : $i]:
% 0.20/0.53         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((((sk_B) = (k2_relat_1 @ sk_C_1)))
% 0.20/0.53         <= ((![X25 : $i]:
% 0.20/0.53                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53                   != (k1_xboole_0))
% 0.20/0.53                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B)))
% 0.20/0.53         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((((k2_relat_1 @ sk_C_1) != (sk_B)))
% 0.20/0.53         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((((sk_B) != (sk_B)))
% 0.20/0.53         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.53             (![X25 : $i]:
% 0.20/0.53                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53                   != (k1_xboole_0))
% 0.20/0.53                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (~
% 0.20/0.53       (![X25 : $i]:
% 0.20/0.53          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X25))
% 0.20/0.53             != (k1_xboole_0))
% 0.20/0.53           | ~ (r2_hidden @ X25 @ sk_B))) | 
% 0.20/0.53       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.20/0.53        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.53            = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.53          = (k1_xboole_0))) | 
% 0.20/0.53       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (((r2_hidden @ sk_D @ sk_B)) <= (((r2_hidden @ sk_D @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.20/0.53           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.53          = (k1_xboole_0)))
% 0.20/0.53         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.53                = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['38'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((((k10_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D)) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.53                = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))
% 0.20/0.53         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((((k2_relat_1 @ sk_C_1) = (sk_B)))
% 0.20/0.53         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X11 @ (k2_relat_1 @ X10))
% 0.20/0.53          | ((k10_relat_1 @ X10 @ (k1_tarski @ X11)) != (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.53           | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.53           | ((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))))
% 0.20/0.53         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.53           | ((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))))
% 0.20/0.53         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.53      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_D @ sk_B)))
% 0.20/0.53         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.53             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.53                = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_D @ sk_B))
% 0.20/0.53         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.53             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.53                = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.53          = (k1_xboole_0))) | 
% 0.20/0.53       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_D @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '52'])).
% 0.20/0.53  thf('54', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '3', '37', '39', '53'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
