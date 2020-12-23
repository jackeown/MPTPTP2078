%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N66ZaDSepU

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:44 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 134 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  763 (1947 expanded)
%              Number of equality atoms :   31 ( 120 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t73_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ( ( ( k2_relset_1 @ A @ A @ B )
                = A )
              & ( ( k2_relset_1 @ A @ A @ C )
                = A ) )
           => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
              = A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
           => ( ( ( ( k2_relset_1 @ A @ A @ B )
                  = A )
                & ( ( k2_relset_1 @ A @ A @ C )
                  = A ) )
             => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
                = A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k4_relset_1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B )
    = ( k5_relat_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','30'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) @ X12 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('57',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['12','57'])).

thf('59',plain,(
    ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B )
    = ( k5_relat_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('61',plain,(
    ( k2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N66ZaDSepU
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.46/1.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.46/1.70  % Solved by: fo/fo7.sh
% 1.46/1.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.46/1.70  % done 627 iterations in 1.235s
% 1.46/1.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.46/1.70  % SZS output start Refutation
% 1.46/1.70  thf(sk_B_type, type, sk_B: $i).
% 1.46/1.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.46/1.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.46/1.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.46/1.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.46/1.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.46/1.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.46/1.70  thf(sk_A_type, type, sk_A: $i).
% 1.46/1.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.46/1.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.46/1.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.46/1.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.46/1.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.46/1.70  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.46/1.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.46/1.70  thf(t73_funct_2, conjecture,
% 1.46/1.70    (![A:$i,B:$i]:
% 1.46/1.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 1.46/1.70       ( ![C:$i]:
% 1.46/1.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 1.46/1.70           ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 1.46/1.70               ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 1.46/1.70             ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 1.46/1.70               ( A ) ) ) ) ) ))).
% 1.46/1.70  thf(zf_stmt_0, negated_conjecture,
% 1.46/1.70    (~( ![A:$i,B:$i]:
% 1.46/1.70        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 1.46/1.70          ( ![C:$i]:
% 1.46/1.70            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 1.46/1.70              ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 1.46/1.70                  ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 1.46/1.70                ( ( k2_relset_1 @
% 1.46/1.70                    A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 1.46/1.70                  ( A ) ) ) ) ) ) )),
% 1.46/1.70    inference('cnf.neg', [status(esa)], [t73_funct_2])).
% 1.46/1.70  thf('0', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('1', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf(dt_k4_relset_1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.46/1.70     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.46/1.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.46/1.70       ( m1_subset_1 @
% 1.46/1.70         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.46/1.70         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.46/1.70  thf('2', plain,
% 1.46/1.70      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.46/1.70         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.46/1.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.46/1.70          | (m1_subset_1 @ (k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 1.46/1.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 1.46/1.70      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.46/1.70  thf('3', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.70         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.46/1.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.46/1.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.46/1.70      inference('sup-', [status(thm)], ['1', '2'])).
% 1.46/1.70  thf('4', plain,
% 1.46/1.70      ((m1_subset_1 @ 
% 1.46/1.70        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B) @ 
% 1.46/1.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('sup-', [status(thm)], ['0', '3'])).
% 1.46/1.70  thf('5', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('6', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf(redefinition_k4_relset_1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.46/1.70     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.46/1.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.46/1.70       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.46/1.70  thf('7', plain,
% 1.46/1.70      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.46/1.70         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.46/1.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.46/1.70          | ((k4_relset_1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 1.46/1.70              = (k5_relat_1 @ X33 @ X36)))),
% 1.46/1.70      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.46/1.70  thf('8', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.70         (((k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C_1 @ X0)
% 1.46/1.70            = (k5_relat_1 @ sk_C_1 @ X0))
% 1.46/1.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.46/1.70      inference('sup-', [status(thm)], ['6', '7'])).
% 1.46/1.70  thf('9', plain,
% 1.46/1.70      (((k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B)
% 1.46/1.70         = (k5_relat_1 @ sk_C_1 @ sk_B))),
% 1.46/1.70      inference('sup-', [status(thm)], ['5', '8'])).
% 1.46/1.70  thf('10', plain,
% 1.46/1.70      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_B) @ 
% 1.46/1.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('demod', [status(thm)], ['4', '9'])).
% 1.46/1.70  thf(redefinition_k2_relset_1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i]:
% 1.46/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.46/1.70  thf('11', plain,
% 1.46/1.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.46/1.70         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 1.46/1.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.46/1.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.46/1.70  thf('12', plain,
% 1.46/1.70      (((k2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B))
% 1.46/1.70         = (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))),
% 1.46/1.70      inference('sup-', [status(thm)], ['10', '11'])).
% 1.46/1.70  thf(d3_tarski, axiom,
% 1.46/1.70    (![A:$i,B:$i]:
% 1.46/1.70     ( ( r1_tarski @ A @ B ) <=>
% 1.46/1.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.46/1.70  thf('13', plain,
% 1.46/1.70      (![X1 : $i, X3 : $i]:
% 1.46/1.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.46/1.70      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.70  thf('14', plain,
% 1.46/1.70      (![X1 : $i, X3 : $i]:
% 1.46/1.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.46/1.70      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.70  thf('15', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf(l3_subset_1, axiom,
% 1.46/1.70    (![A:$i,B:$i]:
% 1.46/1.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.46/1.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.46/1.70  thf('16', plain,
% 1.46/1.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.46/1.70         (~ (r2_hidden @ X7 @ X8)
% 1.46/1.70          | (r2_hidden @ X7 @ X9)
% 1.46/1.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.46/1.70      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.46/1.70  thf('17', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.46/1.70          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.46/1.70      inference('sup-', [status(thm)], ['15', '16'])).
% 1.46/1.70  thf('18', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((r1_tarski @ sk_B @ X0)
% 1.46/1.70          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('sup-', [status(thm)], ['14', '17'])).
% 1.46/1.70  thf('19', plain,
% 1.46/1.70      (![X1 : $i, X3 : $i]:
% 1.46/1.70         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.46/1.70      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.70  thf('20', plain,
% 1.46/1.70      (((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.46/1.70        | (r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('sup-', [status(thm)], ['18', '19'])).
% 1.46/1.70  thf('21', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 1.46/1.70      inference('simplify', [status(thm)], ['20'])).
% 1.46/1.70  thf(t25_relat_1, axiom,
% 1.46/1.70    (![A:$i]:
% 1.46/1.70     ( ( v1_relat_1 @ A ) =>
% 1.46/1.70       ( ![B:$i]:
% 1.46/1.70         ( ( v1_relat_1 @ B ) =>
% 1.46/1.70           ( ( r1_tarski @ A @ B ) =>
% 1.46/1.70             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.46/1.70               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.46/1.70  thf('22', plain,
% 1.46/1.70      (![X16 : $i, X17 : $i]:
% 1.46/1.70         (~ (v1_relat_1 @ X16)
% 1.46/1.70          | (r1_tarski @ (k1_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 1.46/1.70          | ~ (r1_tarski @ X17 @ X16)
% 1.46/1.70          | ~ (v1_relat_1 @ X17))),
% 1.46/1.70      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.46/1.70  thf('23', plain,
% 1.46/1.70      ((~ (v1_relat_1 @ sk_B)
% 1.46/1.70        | (r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 1.46/1.70           (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.46/1.70        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('sup-', [status(thm)], ['21', '22'])).
% 1.46/1.70  thf('24', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf(cc1_relset_1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i]:
% 1.46/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.70       ( v1_relat_1 @ C ) ))).
% 1.46/1.70  thf('25', plain,
% 1.46/1.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.46/1.70         ((v1_relat_1 @ X21)
% 1.46/1.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.46/1.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.46/1.70  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.70      inference('sup-', [status(thm)], ['24', '25'])).
% 1.46/1.70  thf(fc6_relat_1, axiom,
% 1.46/1.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.46/1.70  thf('27', plain,
% 1.46/1.70      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 1.46/1.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.46/1.70  thf('28', plain,
% 1.46/1.70      ((r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 1.46/1.70        (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('demod', [status(thm)], ['23', '26', '27'])).
% 1.46/1.70  thf('29', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.70         (~ (r2_hidden @ X0 @ X1)
% 1.46/1.70          | (r2_hidden @ X0 @ X2)
% 1.46/1.70          | ~ (r1_tarski @ X1 @ X2))),
% 1.46/1.70      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.70  thf('30', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((r2_hidden @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.46/1.70          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 1.46/1.70      inference('sup-', [status(thm)], ['28', '29'])).
% 1.46/1.70  thf('31', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.46/1.70          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.46/1.70             (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.46/1.70      inference('sup-', [status(thm)], ['13', '30'])).
% 1.46/1.70  thf(t193_relat_1, axiom,
% 1.46/1.70    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 1.46/1.70  thf('32', plain,
% 1.46/1.70      (![X12 : $i, X13 : $i]:
% 1.46/1.70         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13)) @ X12)),
% 1.46/1.70      inference('cnf', [status(esa)], [t193_relat_1])).
% 1.46/1.70  thf('33', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.70         (~ (r2_hidden @ X0 @ X1)
% 1.46/1.70          | (r2_hidden @ X0 @ X2)
% 1.46/1.70          | ~ (r1_tarski @ X1 @ X2))),
% 1.46/1.70      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.70  thf('34', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.70         ((r2_hidden @ X2 @ X0)
% 1.46/1.70          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 1.46/1.70      inference('sup-', [status(thm)], ['32', '33'])).
% 1.46/1.70  thf('35', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.46/1.70          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 1.46/1.70      inference('sup-', [status(thm)], ['31', '34'])).
% 1.46/1.70  thf('36', plain,
% 1.46/1.70      (![X1 : $i, X3 : $i]:
% 1.46/1.70         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.46/1.70      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.70  thf('37', plain,
% 1.46/1.70      (((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.46/1.70        | (r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.46/1.70      inference('sup-', [status(thm)], ['35', '36'])).
% 1.46/1.70  thf('38', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.46/1.70      inference('simplify', [status(thm)], ['37'])).
% 1.46/1.70  thf('39', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('40', plain,
% 1.46/1.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.46/1.70         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 1.46/1.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.46/1.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.46/1.70  thf('41', plain,
% 1.46/1.70      (((k2_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.46/1.70      inference('sup-', [status(thm)], ['39', '40'])).
% 1.46/1.70  thf('42', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_C_1) = (sk_A))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('43', plain, (((k2_relat_1 @ sk_C_1) = (sk_A))),
% 1.46/1.70      inference('sup+', [status(thm)], ['41', '42'])).
% 1.46/1.70  thf(t47_relat_1, axiom,
% 1.46/1.70    (![A:$i]:
% 1.46/1.70     ( ( v1_relat_1 @ A ) =>
% 1.46/1.70       ( ![B:$i]:
% 1.46/1.70         ( ( v1_relat_1 @ B ) =>
% 1.46/1.70           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.46/1.70             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.46/1.70  thf('44', plain,
% 1.46/1.70      (![X18 : $i, X19 : $i]:
% 1.46/1.70         (~ (v1_relat_1 @ X18)
% 1.46/1.70          | ((k2_relat_1 @ (k5_relat_1 @ X18 @ X19)) = (k2_relat_1 @ X19))
% 1.46/1.70          | ~ (r1_tarski @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X18))
% 1.46/1.70          | ~ (v1_relat_1 @ X19))),
% 1.46/1.70      inference('cnf', [status(esa)], [t47_relat_1])).
% 1.46/1.70  thf('45', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 1.46/1.70          | ~ (v1_relat_1 @ X0)
% 1.46/1.70          | ((k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ X0)) = (k2_relat_1 @ X0))
% 1.46/1.70          | ~ (v1_relat_1 @ sk_C_1))),
% 1.46/1.70      inference('sup-', [status(thm)], ['43', '44'])).
% 1.46/1.70  thf('46', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('47', plain,
% 1.46/1.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.46/1.70         ((v1_relat_1 @ X21)
% 1.46/1.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.46/1.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.46/1.70  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 1.46/1.70      inference('sup-', [status(thm)], ['46', '47'])).
% 1.46/1.70  thf('49', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 1.46/1.70          | ~ (v1_relat_1 @ X0)
% 1.46/1.70          | ((k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ X0)) = (k2_relat_1 @ X0)))),
% 1.46/1.70      inference('demod', [status(thm)], ['45', '48'])).
% 1.46/1.70  thf('50', plain,
% 1.46/1.70      ((((k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 1.46/1.70        | ~ (v1_relat_1 @ sk_B))),
% 1.46/1.70      inference('sup-', [status(thm)], ['38', '49'])).
% 1.46/1.70  thf('51', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('52', plain,
% 1.46/1.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.46/1.70         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 1.46/1.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.46/1.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.46/1.70  thf('53', plain,
% 1.46/1.70      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 1.46/1.70      inference('sup-', [status(thm)], ['51', '52'])).
% 1.46/1.70  thf('54', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('55', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.46/1.70      inference('sup+', [status(thm)], ['53', '54'])).
% 1.46/1.70  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.70      inference('sup-', [status(thm)], ['24', '25'])).
% 1.46/1.70  thf('57', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)) = (sk_A))),
% 1.46/1.70      inference('demod', [status(thm)], ['50', '55', '56'])).
% 1.46/1.70  thf('58', plain,
% 1.46/1.70      (((k2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B)) = (sk_A))),
% 1.46/1.70      inference('demod', [status(thm)], ['12', '57'])).
% 1.46/1.70  thf('59', plain,
% 1.46/1.70      (((k2_relset_1 @ sk_A @ sk_A @ 
% 1.46/1.70         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B)) != (
% 1.46/1.70         sk_A))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('60', plain,
% 1.46/1.70      (((k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B)
% 1.46/1.70         = (k5_relat_1 @ sk_C_1 @ sk_B))),
% 1.46/1.70      inference('sup-', [status(thm)], ['5', '8'])).
% 1.46/1.70  thf('61', plain,
% 1.46/1.70      (((k2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B)) != (sk_A))),
% 1.46/1.70      inference('demod', [status(thm)], ['59', '60'])).
% 1.46/1.70  thf('62', plain, ($false),
% 1.46/1.70      inference('simplify_reflect-', [status(thm)], ['58', '61'])).
% 1.46/1.70  
% 1.46/1.70  % SZS output end Refutation
% 1.46/1.70  
% 1.46/1.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
