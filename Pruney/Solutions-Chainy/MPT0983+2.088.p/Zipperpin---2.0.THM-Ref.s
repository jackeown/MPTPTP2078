%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3KJKSq8G2C

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:15 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 328 expanded)
%              Number of leaves         :   41 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          : 1120 (6422 expanded)
%              Number of equality atoms :   41 (  78 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('4',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('16',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','18'])).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('20',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['30','33','34','35','36'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ X27 )
       != X26 )
      | ( v2_funct_2 @ X27 @ X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('39',plain,(
    ! [X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v5_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
      | ( v2_funct_2 @ X27 @ ( k2_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['30','33','34','35','36'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['40','43','44','47'])).

thf('49',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('50',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('52',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['22','52'])).

thf('54',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('61',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('68',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('72',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('74',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39 ) )
      | ( v2_funct_1 @ X43 )
      | ( X41 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X40 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('86',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('87',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('90',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','88','90','91'])).

thf('93',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['54','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['53','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3KJKSq8G2C
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:32:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.12/3.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.12/3.31  % Solved by: fo/fo7.sh
% 3.12/3.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.12/3.31  % done 2986 iterations in 2.837s
% 3.12/3.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.12/3.31  % SZS output start Refutation
% 3.12/3.31  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.12/3.31  thf(sk_A_type, type, sk_A: $i).
% 3.12/3.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.12/3.31  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.12/3.31  thf(sk_D_type, type, sk_D: $i).
% 3.12/3.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.12/3.31  thf(sk_C_type, type, sk_C: $i).
% 3.12/3.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.12/3.31  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.12/3.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.12/3.31  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.12/3.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.12/3.31  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.12/3.31  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.12/3.31  thf(sk_B_type, type, sk_B: $i > $i).
% 3.12/3.31  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.12/3.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.12/3.31  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.12/3.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.12/3.31  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.12/3.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.12/3.31  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.12/3.31  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.12/3.31  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.12/3.31  thf(l13_xboole_0, axiom,
% 3.12/3.31    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.12/3.31  thf('0', plain,
% 3.12/3.31      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.12/3.31      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.12/3.31  thf(d1_xboole_0, axiom,
% 3.12/3.31    (![A:$i]:
% 3.12/3.31     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.12/3.31  thf('1', plain,
% 3.12/3.31      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.12/3.31      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.12/3.31  thf(t113_zfmisc_1, axiom,
% 3.12/3.31    (![A:$i,B:$i]:
% 3.12/3.31     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.12/3.31       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.12/3.31  thf('2', plain,
% 3.12/3.31      (![X5 : $i, X6 : $i]:
% 3.12/3.31         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.12/3.31      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.12/3.31  thf('3', plain,
% 3.12/3.31      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.12/3.31      inference('simplify', [status(thm)], ['2'])).
% 3.12/3.31  thf(t29_relset_1, axiom,
% 3.12/3.31    (![A:$i]:
% 3.12/3.31     ( m1_subset_1 @
% 3.12/3.31       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.12/3.31  thf('4', plain,
% 3.12/3.31      (![X25 : $i]:
% 3.12/3.31         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 3.12/3.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.12/3.31      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.12/3.31  thf(redefinition_k6_partfun1, axiom,
% 3.12/3.31    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.12/3.31  thf('5', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.12/3.31      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.12/3.31  thf('6', plain,
% 3.12/3.31      (![X25 : $i]:
% 3.12/3.31         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 3.12/3.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.12/3.31      inference('demod', [status(thm)], ['4', '5'])).
% 3.12/3.31  thf(t5_subset, axiom,
% 3.12/3.31    (![A:$i,B:$i,C:$i]:
% 3.12/3.31     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.12/3.31          ( v1_xboole_0 @ C ) ) ))).
% 3.12/3.31  thf('7', plain,
% 3.12/3.31      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.12/3.31         (~ (r2_hidden @ X7 @ X8)
% 3.12/3.31          | ~ (v1_xboole_0 @ X9)
% 3.12/3.31          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 3.12/3.31      inference('cnf', [status(esa)], [t5_subset])).
% 3.12/3.31  thf('8', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i]:
% 3.12/3.31         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 3.12/3.31          | ~ (r2_hidden @ X1 @ (k6_partfun1 @ X0)))),
% 3.12/3.31      inference('sup-', [status(thm)], ['6', '7'])).
% 3.12/3.31  thf('9', plain,
% 3.12/3.31      (![X0 : $i]:
% 3.12/3.31         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.12/3.31          | ~ (r2_hidden @ X0 @ (k6_partfun1 @ k1_xboole_0)))),
% 3.12/3.31      inference('sup-', [status(thm)], ['3', '8'])).
% 3.12/3.31  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.12/3.31  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.12/3.31      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.12/3.31  thf('11', plain,
% 3.12/3.31      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_partfun1 @ k1_xboole_0))),
% 3.12/3.31      inference('demod', [status(thm)], ['9', '10'])).
% 3.12/3.31  thf('12', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 3.12/3.31      inference('sup-', [status(thm)], ['1', '11'])).
% 3.12/3.31  thf('13', plain,
% 3.12/3.31      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.12/3.31      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.12/3.31  thf('14', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.12/3.31      inference('sup-', [status(thm)], ['12', '13'])).
% 3.12/3.31  thf(fc4_funct_1, axiom,
% 3.12/3.31    (![A:$i]:
% 3.12/3.31     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.12/3.31       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.12/3.31  thf('15', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 3.12/3.31      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.12/3.31  thf('16', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.12/3.31      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.12/3.31  thf('17', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 3.12/3.31      inference('demod', [status(thm)], ['15', '16'])).
% 3.12/3.31  thf('18', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.12/3.31      inference('sup+', [status(thm)], ['14', '17'])).
% 3.12/3.31  thf('19', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.12/3.31      inference('sup+', [status(thm)], ['0', '18'])).
% 3.12/3.31  thf(t29_funct_2, conjecture,
% 3.12/3.31    (![A:$i,B:$i,C:$i]:
% 3.12/3.31     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.12/3.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.12/3.31       ( ![D:$i]:
% 3.12/3.31         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.12/3.31             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.12/3.31           ( ( r2_relset_1 @
% 3.12/3.31               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.12/3.31               ( k6_partfun1 @ A ) ) =>
% 3.12/3.31             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.12/3.31  thf(zf_stmt_0, negated_conjecture,
% 3.12/3.31    (~( ![A:$i,B:$i,C:$i]:
% 3.12/3.31        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.12/3.31            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.12/3.31          ( ![D:$i]:
% 3.12/3.31            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.12/3.31                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.12/3.31              ( ( r2_relset_1 @
% 3.12/3.31                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.12/3.31                  ( k6_partfun1 @ A ) ) =>
% 3.12/3.31                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.12/3.31    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.12/3.31  thf('20', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('21', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.12/3.31      inference('split', [status(esa)], ['20'])).
% 3.12/3.31  thf('22', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.12/3.31      inference('sup-', [status(thm)], ['19', '21'])).
% 3.12/3.31  thf('23', plain,
% 3.12/3.31      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.12/3.31        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.12/3.31        (k6_partfun1 @ sk_A))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('24', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf(t24_funct_2, axiom,
% 3.12/3.31    (![A:$i,B:$i,C:$i]:
% 3.12/3.31     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.12/3.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.12/3.31       ( ![D:$i]:
% 3.12/3.31         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.12/3.31             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.12/3.31           ( ( r2_relset_1 @
% 3.12/3.31               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.12/3.31               ( k6_partfun1 @ B ) ) =>
% 3.12/3.31             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.12/3.31  thf('25', plain,
% 3.12/3.31      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.12/3.31         (~ (v1_funct_1 @ X35)
% 3.12/3.31          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 3.12/3.31          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.12/3.31          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 3.12/3.31               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 3.12/3.31               (k6_partfun1 @ X36))
% 3.12/3.31          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 3.12/3.31          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 3.12/3.31          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 3.12/3.31          | ~ (v1_funct_1 @ X38))),
% 3.12/3.31      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.12/3.31  thf('26', plain,
% 3.12/3.31      (![X0 : $i]:
% 3.12/3.31         (~ (v1_funct_1 @ X0)
% 3.12/3.31          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.12/3.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.12/3.31          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.12/3.31          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.12/3.31               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.12/3.31               (k6_partfun1 @ sk_A))
% 3.12/3.31          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.12/3.31          | ~ (v1_funct_1 @ sk_C))),
% 3.12/3.31      inference('sup-', [status(thm)], ['24', '25'])).
% 3.12/3.31  thf('27', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('29', plain,
% 3.12/3.31      (![X0 : $i]:
% 3.12/3.31         (~ (v1_funct_1 @ X0)
% 3.12/3.31          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.12/3.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.12/3.31          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.12/3.31          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.12/3.31               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.12/3.31               (k6_partfun1 @ sk_A)))),
% 3.12/3.31      inference('demod', [status(thm)], ['26', '27', '28'])).
% 3.12/3.31  thf('30', plain,
% 3.12/3.31      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 3.12/3.31        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.12/3.31        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.12/3.31        | ~ (v1_funct_1 @ sk_D))),
% 3.12/3.31      inference('sup-', [status(thm)], ['23', '29'])).
% 3.12/3.31  thf('31', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf(redefinition_k2_relset_1, axiom,
% 3.12/3.31    (![A:$i,B:$i,C:$i]:
% 3.12/3.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.12/3.31       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.12/3.31  thf('32', plain,
% 3.12/3.31      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.12/3.31         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 3.12/3.31          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.12/3.31      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.12/3.31  thf('33', plain,
% 3.12/3.31      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.12/3.31      inference('sup-', [status(thm)], ['31', '32'])).
% 3.12/3.31  thf('34', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('37', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.12/3.31      inference('demod', [status(thm)], ['30', '33', '34', '35', '36'])).
% 3.12/3.31  thf(d3_funct_2, axiom,
% 3.12/3.31    (![A:$i,B:$i]:
% 3.12/3.31     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.12/3.31       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.12/3.31  thf('38', plain,
% 3.12/3.31      (![X26 : $i, X27 : $i]:
% 3.12/3.31         (((k2_relat_1 @ X27) != (X26))
% 3.12/3.31          | (v2_funct_2 @ X27 @ X26)
% 3.12/3.31          | ~ (v5_relat_1 @ X27 @ X26)
% 3.12/3.31          | ~ (v1_relat_1 @ X27))),
% 3.12/3.31      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.12/3.31  thf('39', plain,
% 3.12/3.31      (![X27 : $i]:
% 3.12/3.31         (~ (v1_relat_1 @ X27)
% 3.12/3.31          | ~ (v5_relat_1 @ X27 @ (k2_relat_1 @ X27))
% 3.12/3.31          | (v2_funct_2 @ X27 @ (k2_relat_1 @ X27)))),
% 3.12/3.31      inference('simplify', [status(thm)], ['38'])).
% 3.12/3.31  thf('40', plain,
% 3.12/3.31      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.12/3.31        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.12/3.31        | ~ (v1_relat_1 @ sk_D))),
% 3.12/3.31      inference('sup-', [status(thm)], ['37', '39'])).
% 3.12/3.31  thf('41', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf(cc2_relset_1, axiom,
% 3.12/3.31    (![A:$i,B:$i,C:$i]:
% 3.12/3.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.12/3.31       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.12/3.31  thf('42', plain,
% 3.12/3.31      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.12/3.31         ((v5_relat_1 @ X15 @ X17)
% 3.12/3.31          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.12/3.31      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.12/3.31  thf('43', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.12/3.31      inference('sup-', [status(thm)], ['41', '42'])).
% 3.12/3.31  thf('44', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.12/3.31      inference('demod', [status(thm)], ['30', '33', '34', '35', '36'])).
% 3.12/3.31  thf('45', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf(cc1_relset_1, axiom,
% 3.12/3.31    (![A:$i,B:$i,C:$i]:
% 3.12/3.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.12/3.31       ( v1_relat_1 @ C ) ))).
% 3.12/3.31  thf('46', plain,
% 3.12/3.31      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.12/3.31         ((v1_relat_1 @ X12)
% 3.12/3.31          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.12/3.31      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.12/3.31  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 3.12/3.31      inference('sup-', [status(thm)], ['45', '46'])).
% 3.12/3.31  thf('48', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.12/3.31      inference('demod', [status(thm)], ['40', '43', '44', '47'])).
% 3.12/3.31  thf('49', plain,
% 3.12/3.31      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.12/3.31      inference('split', [status(esa)], ['20'])).
% 3.12/3.31  thf('50', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.12/3.31      inference('sup-', [status(thm)], ['48', '49'])).
% 3.12/3.31  thf('51', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.12/3.31      inference('split', [status(esa)], ['20'])).
% 3.12/3.31  thf('52', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.12/3.31      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 3.12/3.31  thf('53', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.12/3.31      inference('simpl_trail', [status(thm)], ['22', '52'])).
% 3.12/3.31  thf('54', plain,
% 3.12/3.31      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.12/3.31      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.12/3.31  thf('55', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('56', plain,
% 3.12/3.31      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.12/3.31         (~ (r2_hidden @ X7 @ X8)
% 3.12/3.31          | ~ (v1_xboole_0 @ X9)
% 3.12/3.31          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 3.12/3.31      inference('cnf', [status(esa)], [t5_subset])).
% 3.12/3.31  thf('57', plain,
% 3.12/3.31      (![X0 : $i]:
% 3.12/3.31         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.12/3.31          | ~ (r2_hidden @ X0 @ sk_C))),
% 3.12/3.31      inference('sup-', [status(thm)], ['55', '56'])).
% 3.12/3.31  thf('58', plain,
% 3.12/3.31      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.12/3.31        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.12/3.31        (k6_partfun1 @ sk_A))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('59', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('60', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf(dt_k1_partfun1, axiom,
% 3.12/3.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.12/3.31     ( ( ( v1_funct_1 @ E ) & 
% 3.12/3.31         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.12/3.31         ( v1_funct_1 @ F ) & 
% 3.12/3.31         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.12/3.31       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.12/3.31         ( m1_subset_1 @
% 3.12/3.31           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.12/3.31           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.12/3.31  thf('61', plain,
% 3.12/3.31      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.12/3.31         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.12/3.31          | ~ (v1_funct_1 @ X28)
% 3.12/3.31          | ~ (v1_funct_1 @ X31)
% 3.12/3.31          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.12/3.31          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 3.12/3.31             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 3.12/3.31      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.12/3.31  thf('62', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.31         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.12/3.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.12/3.31          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.12/3.31          | ~ (v1_funct_1 @ X1)
% 3.12/3.31          | ~ (v1_funct_1 @ sk_C))),
% 3.12/3.31      inference('sup-', [status(thm)], ['60', '61'])).
% 3.12/3.31  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('64', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.31         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.12/3.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.12/3.31          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.12/3.31          | ~ (v1_funct_1 @ X1))),
% 3.12/3.31      inference('demod', [status(thm)], ['62', '63'])).
% 3.12/3.31  thf('65', plain,
% 3.12/3.31      ((~ (v1_funct_1 @ sk_D)
% 3.12/3.31        | (m1_subset_1 @ 
% 3.12/3.31           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.12/3.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.12/3.31      inference('sup-', [status(thm)], ['59', '64'])).
% 3.12/3.31  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('67', plain,
% 3.12/3.31      ((m1_subset_1 @ 
% 3.12/3.31        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.12/3.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.12/3.31      inference('demod', [status(thm)], ['65', '66'])).
% 3.12/3.31  thf(redefinition_r2_relset_1, axiom,
% 3.12/3.31    (![A:$i,B:$i,C:$i,D:$i]:
% 3.12/3.31     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.12/3.31         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.12/3.31       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.12/3.31  thf('68', plain,
% 3.12/3.31      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.12/3.31         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.12/3.31          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.12/3.31          | ((X21) = (X24))
% 3.12/3.31          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 3.12/3.31      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.12/3.31  thf('69', plain,
% 3.12/3.31      (![X0 : $i]:
% 3.12/3.31         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.12/3.31             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 3.12/3.31          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 3.12/3.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.12/3.31      inference('sup-', [status(thm)], ['67', '68'])).
% 3.12/3.31  thf('70', plain,
% 3.12/3.31      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.12/3.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.12/3.31        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.12/3.31            = (k6_partfun1 @ sk_A)))),
% 3.12/3.31      inference('sup-', [status(thm)], ['58', '69'])).
% 3.12/3.31  thf('71', plain,
% 3.12/3.31      (![X25 : $i]:
% 3.12/3.31         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 3.12/3.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.12/3.31      inference('demod', [status(thm)], ['4', '5'])).
% 3.12/3.31  thf('72', plain,
% 3.12/3.31      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.12/3.31         = (k6_partfun1 @ sk_A))),
% 3.12/3.31      inference('demod', [status(thm)], ['70', '71'])).
% 3.12/3.31  thf('73', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf(t26_funct_2, axiom,
% 3.12/3.31    (![A:$i,B:$i,C:$i,D:$i]:
% 3.12/3.31     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.12/3.31         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.12/3.31       ( ![E:$i]:
% 3.12/3.31         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.12/3.31             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.12/3.31           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.12/3.31             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.12/3.31               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.12/3.31  thf('74', plain,
% 3.12/3.31      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.12/3.31         (~ (v1_funct_1 @ X39)
% 3.12/3.31          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 3.12/3.31          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.12/3.31          | ~ (v2_funct_1 @ (k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39))
% 3.12/3.31          | (v2_funct_1 @ X43)
% 3.12/3.31          | ((X41) = (k1_xboole_0))
% 3.12/3.31          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 3.12/3.31          | ~ (v1_funct_2 @ X43 @ X42 @ X40)
% 3.12/3.31          | ~ (v1_funct_1 @ X43))),
% 3.12/3.31      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.12/3.31  thf('75', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i]:
% 3.12/3.31         (~ (v1_funct_1 @ X0)
% 3.12/3.31          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.12/3.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.12/3.31          | ((sk_A) = (k1_xboole_0))
% 3.12/3.31          | (v2_funct_1 @ X0)
% 3.12/3.31          | ~ (v2_funct_1 @ 
% 3.12/3.31               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 3.12/3.31          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.12/3.31          | ~ (v1_funct_1 @ sk_D))),
% 3.12/3.31      inference('sup-', [status(thm)], ['73', '74'])).
% 3.12/3.31  thf('76', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('78', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i]:
% 3.12/3.31         (~ (v1_funct_1 @ X0)
% 3.12/3.31          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.12/3.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.12/3.31          | ((sk_A) = (k1_xboole_0))
% 3.12/3.31          | (v2_funct_1 @ X0)
% 3.12/3.31          | ~ (v2_funct_1 @ 
% 3.12/3.31               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 3.12/3.31      inference('demod', [status(thm)], ['75', '76', '77'])).
% 3.12/3.31  thf('79', plain,
% 3.12/3.31      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.12/3.31        | (v2_funct_1 @ sk_C)
% 3.12/3.31        | ((sk_A) = (k1_xboole_0))
% 3.12/3.31        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.12/3.31        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.12/3.31        | ~ (v1_funct_1 @ sk_C))),
% 3.12/3.31      inference('sup-', [status(thm)], ['72', '78'])).
% 3.12/3.31  thf('80', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 3.12/3.31      inference('demod', [status(thm)], ['15', '16'])).
% 3.12/3.31  thf('81', plain,
% 3.12/3.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('84', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.12/3.31      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 3.12/3.31  thf('85', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.12/3.31      inference('split', [status(esa)], ['20'])).
% 3.12/3.31  thf('86', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.12/3.31      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 3.12/3.31  thf('87', plain, (~ (v2_funct_1 @ sk_C)),
% 3.12/3.31      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 3.12/3.31  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 3.12/3.31      inference('clc', [status(thm)], ['84', '87'])).
% 3.12/3.31  thf('89', plain,
% 3.12/3.31      (![X5 : $i, X6 : $i]:
% 3.12/3.31         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 3.12/3.31      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.12/3.31  thf('90', plain,
% 3.12/3.31      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 3.12/3.31      inference('simplify', [status(thm)], ['89'])).
% 3.12/3.31  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.12/3.31      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.12/3.31  thf('92', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 3.12/3.31      inference('demod', [status(thm)], ['57', '88', '90', '91'])).
% 3.12/3.31  thf('93', plain, ((v1_xboole_0 @ sk_C)),
% 3.12/3.31      inference('sup-', [status(thm)], ['54', '92'])).
% 3.12/3.31  thf('94', plain, ($false), inference('demod', [status(thm)], ['53', '93'])).
% 3.12/3.31  
% 3.12/3.31  % SZS output end Refutation
% 3.12/3.31  
% 3.12/3.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
