%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LCWARicKwh

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:19 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 231 expanded)
%              Number of leaves         :   40 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  823 (2626 expanded)
%              Number of equality atoms :   49 ( 127 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( X27 = k1_xboole_0 )
      | ( X27
       != ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k1_funct_1 @ X26 @ X25 )
        = k1_xboole_0 )
      | ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ ( sk_C @ X19 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('9',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X45 @ X42 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('18',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_2 ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k1_funct_1 @ X26 @ X25 )
        = k1_xboole_0 )
      | ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ X29 ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_funct_1 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['24','39'])).

thf('41',plain,
    ( ( k1_funct_1 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('42',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k11_relat_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('44',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ X29 ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k11_relat_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('49',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
    | ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('53',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['51','52'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ X15 @ ( k1_tarski @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('61',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['54','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k11_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','68'])).

thf('70',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','69'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('71',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('72',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('73',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('74',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('sup-',[status(thm)],['70','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LCWARicKwh
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:41:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 156 iterations in 0.078s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.55  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.37/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.37/0.55  thf(d4_funct_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.55       ( ![B:$i,C:$i]:
% 0.37/0.55         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.37/0.55             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.37/0.55               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.55           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.37/0.55             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.37/0.55               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.55         ((r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.37/0.55          | ((X27) = (k1_xboole_0))
% 0.37/0.55          | ((X27) != (k1_funct_1 @ X26 @ X25))
% 0.37/0.55          | ~ (v1_funct_1 @ X26)
% 0.37/0.55          | ~ (v1_relat_1 @ X26))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X25 : $i, X26 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X26)
% 0.37/0.55          | ~ (v1_funct_1 @ X26)
% 0.37/0.55          | ((k1_funct_1 @ X26 @ X25) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ X25 @ (k1_relat_1 @ X26)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.55  thf(t18_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ B ) =>
% 0.37/0.55       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.37/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X19 : $i, X20 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_C @ X19) @ (k2_relat_1 @ X19))
% 0.37/0.55          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 0.37/0.55          | ~ (v1_relat_1 @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | (r2_hidden @ (sk_C @ X0) @ (k2_relat_1 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_C @ X0) @ (k2_relat_1 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.37/0.55  thf(existence_m1_subset_1, axiom,
% 0.37/0.55    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.37/0.55  thf('5', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B @ X12) @ X12)),
% 0.37/0.55      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.37/0.55  thf(t2_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i]:
% 0.37/0.55         ((r2_hidden @ X13 @ X14)
% 0.37/0.55          | (v1_xboole_0 @ X14)
% 0.37/0.55          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf(t61_funct_2, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.55         ( m1_subset_1 @
% 0.37/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.55         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.55            ( m1_subset_1 @
% 0.37/0.55              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.55          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.55            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t7_funct_2, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.55       ( ( r2_hidden @ C @ A ) =>
% 0.37/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.55           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X42 @ X43)
% 0.37/0.55          | ((X44) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_funct_1 @ X45)
% 0.37/0.55          | ~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.37/0.55          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ X45 @ X42) @ X44))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_2)
% 0.37/0.55          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.37/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.55          | ((sk_B_2) = (k1_xboole_0))
% 0.37/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_2)
% 0.37/0.55          | ((sk_B_2) = (k1_xboole_0))
% 0.37/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.37/0.55  thf('14', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_2)
% 0.37/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.37/0.55        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.37/0.55           sk_B_2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '15'])).
% 0.37/0.55  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.37/0.55  thf('17', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.37/0.55        sk_B_2)),
% 0.37/0.55      inference('clc', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (((r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C_1)
% 0.37/0.55        | (r2_hidden @ (sk_C @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['4', '18'])).
% 0.37/0.55  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(cc1_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( v1_relat_1 @ C ) ))).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.55         ((v1_relat_1 @ X32)
% 0.37/0.55          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.55  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (((r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.37/0.55        | (r2_hidden @ (sk_C @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))),
% 0.37/0.55      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.37/0.55  thf('25', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(cc2_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.37/0.55         ((v5_relat_1 @ X35 @ X37)
% 0.37/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.55  thf('28', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X25 : $i, X26 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X26)
% 0.37/0.55          | ~ (v1_funct_1 @ X26)
% 0.37/0.55          | ((k1_funct_1 @ X26 @ X25) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ X25 @ (k1_relat_1 @ X26)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.55  thf(t172_funct_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.55           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ X30 @ X29) @ X31)
% 0.37/0.55          | ~ (v1_funct_1 @ X30)
% 0.37/0.55          | ~ (v5_relat_1 @ X30 @ X31)
% 0.37/0.55          | ~ (v1_relat_1 @ X30))),
% 0.37/0.55      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v5_relat_1 @ X0 @ X2)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.37/0.55          | ~ (v5_relat_1 @ X0 @ X2)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_funct_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.55          | ~ (v1_relat_1 @ sk_C_1)
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '32'])).
% 0.37/0.55  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_funct_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_2))),
% 0.37/0.55      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.37/0.55  thf('37', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('38', plain, (((k1_funct_1 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.55  thf('39', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf('40', plain, ((r2_hidden @ (sk_C @ sk_C_1) @ (k2_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('clc', [status(thm)], ['24', '39'])).
% 0.37/0.55  thf('41', plain, (((k1_funct_1 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.55  thf('42', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf(t205_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ B ) =>
% 0.37/0.55       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.37/0.55         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i]:
% 0.37/0.55         (((k11_relat_1 @ X21 @ X22) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.37/0.55          | ~ (v1_relat_1 @ X21))),
% 0.37/0.55      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ X30 @ X29) @ X31)
% 0.37/0.55          | ~ (v1_funct_1 @ X30)
% 0.37/0.55          | ~ (v5_relat_1 @ X30 @ X31)
% 0.37/0.55          | ~ (v1_relat_1 @ X30))),
% 0.37/0.55      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X0)
% 0.37/0.55          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v5_relat_1 @ X0 @ X2)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (v5_relat_1 @ X0 @ X2)
% 0.37/0.55          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ sk_C_1)
% 0.37/0.55          | ((k11_relat_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['42', '46'])).
% 0.37/0.55  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('49', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k11_relat_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_2))),
% 0.37/0.55      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (((r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.37/0.55        | ((k11_relat_1 @ sk_C_1 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['41', '50'])).
% 0.37/0.55  thf('52', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf('53', plain, (((k11_relat_1 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('clc', [status(thm)], ['51', '52'])).
% 0.37/0.55  thf(d16_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.37/0.55  thf('54', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i]:
% 0.37/0.55         (((k11_relat_1 @ X15 @ X16) = (k9_relat_1 @ X15 @ (k1_tarski @ X16)))
% 0.37/0.55          | ~ (v1_relat_1 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.37/0.55         ((v4_relat_1 @ X35 @ X36)
% 0.37/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.55  thf('57', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.55  thf(t209_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.37/0.55       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      (![X23 : $i, X24 : $i]:
% 0.37/0.55         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.37/0.55          | ~ (v4_relat_1 @ X23 @ X24)
% 0.37/0.55          | ~ (v1_relat_1 @ X23))),
% 0.37/0.55      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ sk_C_1)
% 0.37/0.55        | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.55  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('61', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['59', '60'])).
% 0.37/0.55  thf(t148_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ B ) =>
% 0.37/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.37/0.55  thf('62', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i]:
% 0.37/0.55         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 0.37/0.55          | ~ (v1_relat_1 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.37/0.55  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      ((((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['54', '65'])).
% 0.37/0.55  thf('67', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('68', plain, (((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.37/0.55  thf('69', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['53', '68'])).
% 0.37/0.55  thf('70', plain, ((r2_hidden @ (sk_C @ sk_C_1) @ k1_xboole_0)),
% 0.37/0.55      inference('demod', [status(thm)], ['40', '69'])).
% 0.37/0.55  thf(t113_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.55  thf('71', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i]:
% 0.37/0.55         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.37/0.55  thf(t152_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i]: ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.37/0.55  thf('74', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.37/0.55  thf('75', plain, ($false), inference('sup-', [status(thm)], ['70', '74'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
