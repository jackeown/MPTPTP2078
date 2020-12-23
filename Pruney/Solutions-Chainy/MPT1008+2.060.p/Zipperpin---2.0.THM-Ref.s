%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F1yOgfLAWx

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:39 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 471 expanded)
%              Number of leaves         :   36 ( 151 expanded)
%              Depth                    :   21
%              Number of atoms          :  803 (5977 expanded)
%              Number of equality atoms :   94 ( 574 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('0',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( X35 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X36 @ X33 ) @ ( k2_relset_1 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X9
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9
        = ( k1_tarski @ X7 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != ( k1_tarski @ X14 ) )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_tarski @ ( k1_funct_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('40',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('47',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('48',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','46','47','48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != ( k1_tarski @ X14 ) )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_tarski @ ( k1_funct_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('58',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('61',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('62',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','63'])).

thf('65',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('67',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('68',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('69',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('70',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F1yOgfLAWx
% 0.16/0.37  % Computer   : n020.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:42:07 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 278 iterations in 0.125s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.61  thf(t6_mcart_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.61          ( ![B:$i]:
% 0.38/0.61            ( ~( ( r2_hidden @ B @ A ) & 
% 0.38/0.61                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.38/0.61                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.38/0.61                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.38/0.61                       ( r2_hidden @ G @ B ) ) =>
% 0.38/0.61                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf('0', plain,
% 0.38/0.61      (![X27 : $i]:
% 0.38/0.61         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.38/0.61      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.38/0.61  thf(t62_funct_2, conjecture,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.61         ( m1_subset_1 @
% 0.38/0.61           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.61       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.61         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.38/0.61           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.61            ( m1_subset_1 @
% 0.38/0.61              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.61          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.61            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.38/0.61              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.38/0.61  thf('1', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t6_funct_2, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.61       ( ( r2_hidden @ C @ A ) =>
% 0.38/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.61           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X33 @ X34)
% 0.38/0.61          | ((X35) = (k1_xboole_0))
% 0.38/0.61          | ~ (v1_funct_1 @ X36)
% 0.38/0.61          | ~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.38/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.38/0.61          | (r2_hidden @ (k1_funct_1 @ X36 @ X33) @ 
% 0.38/0.61             (k2_relset_1 @ X34 @ X35 @ X36)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.38/0.61           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.38/0.61          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.38/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61          | ((sk_B_1) = (k1_xboole_0))
% 0.38/0.61          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.61         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.38/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.38/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.38/0.61         = (k2_relat_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.61  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.38/0.61          | ((sk_B_1) = (k1_xboole_0))
% 0.38/0.61          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.38/0.61  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.38/0.61          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.38/0.61      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.61        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.38/0.61           (k2_relat_1 @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['0', '11'])).
% 0.38/0.61  thf(t7_ordinal1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.38/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.61        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.38/0.61             (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A)))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(cc2_relset_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.61         ((v4_relat_1 @ X21 @ X22)
% 0.38/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.38/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.61  thf('17', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.61  thf(d18_relat_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( v1_relat_1 @ B ) =>
% 0.38/0.61       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i]:
% 0.38/0.61         (~ (v4_relat_1 @ X11 @ X12)
% 0.38/0.61          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.38/0.61          | ~ (v1_relat_1 @ X11))),
% 0.38/0.61      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(cc1_relset_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.61       ( v1_relat_1 @ C ) ))).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.61         ((v1_relat_1 @ X18)
% 0.38/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.38/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.61  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['19', '22'])).
% 0.38/0.61  thf(t69_enumset1, axiom,
% 0.38/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.61  thf('24', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.61  thf(l45_zfmisc_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.38/0.61       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.38/0.61            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.61         (((X9) = (k2_tarski @ X7 @ X8))
% 0.38/0.61          | ((X9) = (k1_tarski @ X8))
% 0.38/0.61          | ((X9) = (k1_tarski @ X7))
% 0.38/0.61          | ((X9) = (k1_xboole_0))
% 0.38/0.61          | ~ (r1_tarski @ X9 @ (k2_tarski @ X7 @ X8)))),
% 0.38/0.61      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.38/0.61          | ((X1) = (k1_xboole_0))
% 0.38/0.61          | ((X1) = (k1_tarski @ X0))
% 0.38/0.61          | ((X1) = (k1_tarski @ X0))
% 0.38/0.61          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.61          | ((X1) = (k1_tarski @ X0))
% 0.38/0.61          | ((X1) = (k1_xboole_0))
% 0.38/0.61          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.38/0.61        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.38/0.61        | ((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['23', '27'])).
% 0.38/0.61  thf('29', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.38/0.61        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.38/0.61        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.38/0.61        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.61  thf(t14_funct_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.61       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.38/0.61         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X14 : $i, X15 : $i]:
% 0.38/0.61         (((k1_relat_1 @ X15) != (k1_tarski @ X14))
% 0.38/0.61          | ((k2_relat_1 @ X15) = (k1_tarski @ (k1_funct_1 @ X15 @ X14)))
% 0.38/0.61          | ~ (v1_funct_1 @ X15)
% 0.38/0.61          | ~ (v1_relat_1 @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.38/0.61          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.38/0.61          | ~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.38/0.61      inference('eq_res', [status(thm)], ['33'])).
% 0.38/0.61  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.38/0.61        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.38/0.61  thf('38', plain,
% 0.38/0.61      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.38/0.61         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.38/0.61         = (k2_relat_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.61  thf('41', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.38/0.61      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.38/0.61  thf(t64_relat_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( v1_relat_1 @ A ) =>
% 0.38/0.61       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.61           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.61         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      (![X13 : $i]:
% 0.38/0.61         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 0.38/0.61          | ((X13) = (k1_xboole_0))
% 0.38/0.61          | ~ (v1_relat_1 @ X13))),
% 0.38/0.61      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.61  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.61  thf('46', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.61  thf(t60_relat_1, axiom,
% 0.38/0.61    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.38/0.61     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.61  thf('47', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.61  thf('48', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.61  thf('49', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.61  thf('50', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['14', '46', '47', '48', '49'])).
% 0.38/0.61  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (![X14 : $i, X15 : $i]:
% 0.38/0.61         (((k1_relat_1 @ X15) != (k1_tarski @ X14))
% 0.38/0.61          | ((k2_relat_1 @ X15) = (k1_tarski @ (k1_funct_1 @ X15 @ X14)))
% 0.38/0.61          | ~ (v1_funct_1 @ X15)
% 0.38/0.61          | ~ (v1_relat_1 @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.38/0.61  thf('53', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.38/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.61          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.38/0.61          | ((k2_relat_1 @ k1_xboole_0)
% 0.38/0.61              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.61  thf('54', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.61  thf('55', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.38/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.61          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.38/0.61          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.38/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.38/0.61  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('57', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.61  thf('58', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.38/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.61  thf('59', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.38/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.61          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.38/0.61      inference('demod', [status(thm)], ['55', '58'])).
% 0.38/0.61  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('61', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.61  thf('62', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.61      inference('demod', [status(thm)], ['60', '61'])).
% 0.38/0.61  thf('63', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.38/0.61          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.38/0.61      inference('demod', [status(thm)], ['59', '62'])).
% 0.38/0.61  thf('64', plain,
% 0.38/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.61        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['50', '63'])).
% 0.38/0.61  thf('65', plain,
% 0.38/0.61      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['64'])).
% 0.38/0.61  thf('66', plain,
% 0.38/0.61      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.61  thf('67', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.61  thf('68', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.61  thf('69', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.61  thf('70', plain,
% 0.38/0.61      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.38/0.61  thf('71', plain, ($false),
% 0.38/0.61      inference('simplify_reflect-', [status(thm)], ['65', '70'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
