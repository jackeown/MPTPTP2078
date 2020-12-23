%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qbHJwEg3jy

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:51 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  160 (2222 expanded)
%              Number of leaves         :   38 ( 631 expanded)
%              Depth                    :   31
%              Number of atoms          : 1376 (36123 expanded)
%              Number of equality atoms :  129 (2377 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t77_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
      <=> ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( ( k1_funct_1 @ sk_B_1 @ X35 )
       != ( k1_funct_1 @ sk_B_1 @ X34 ) )
      | ~ ( r2_hidden @ X34 @ sk_A )
      | ~ ( r2_hidden @ X35 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['11','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('20',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X15: $i] :
      ( ( ( k1_funct_1 @ X15 @ ( sk_B @ X15 ) )
        = ( k1_funct_1 @ X15 @ ( sk_C_1 @ X15 ) ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('23',plain,
    ( ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ~ ( v1_funct_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_B @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('35',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','36'])).

thf('38',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_1 @ X35 )
           != ( k1_funct_1 @ sk_B_1 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i] :
      ( ( ( sk_B @ X15 )
       != ( sk_C_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('41',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_1 @ X35 )
           != ( k1_funct_1 @ sk_B_1 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('43',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_1 @ X35 )
           != ( k1_funct_1 @ sk_B_1 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_1 @ X35 )
           != ( k1_funct_1 @ sk_B_1 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ~ ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_1 @ X35 )
           != ( k1_funct_1 @ sk_B_1 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','47','48'])).

thf('50',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','47','48'])).

thf('53',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('55',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X33 ) @ ( k1_funct_1 @ X33 @ X30 ) )
        = X30 )
      | ~ ( v2_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('58',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['5','47'])).

thf('59',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59','60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['53','62'])).

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

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( X13 = k1_xboole_0 )
      | ( X13
       != ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k1_funct_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X18 ) )
      | ( X19
        = ( k1_funct_1 @ ( k2_funct_1 @ X18 ) @ ( k1_funct_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( X1
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['69'])).

thf('72',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['5','47','71'])).

thf('73',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( X1
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('75',plain,
    ( ( sk_D
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) ) )
    | ( ( k1_funct_1 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['70','72'])).

thf('77',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('79',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('80',plain,
    ( ( sk_D
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) ) )
    | ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,
    ( ( sk_D = sk_C_2 )
    | ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('84',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('85',plain,
    ( ( sk_D = sk_C_2 )
    | ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( sk_D = sk_C_2 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_C_2 != sk_D )
   <= ( sk_C_2 != sk_D ) ),
    inference(split,[status(esa)],['87'])).

thf('89',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['87'])).

thf('90',plain,(
    sk_C_2 != sk_D ),
    inference('sat_resolution*',[status(thm)],['5','47','89'])).

thf('91',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['88','90'])).

thf('92',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ k1_xboole_0 )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['63','92'])).

thf('94',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['94'])).

thf('97',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','47','96'])).

thf('98',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59','60','61'])).

thf('100',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['70','72'])).

thf('102',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['86','91'])).

thf('103',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ k1_xboole_0 )
      = sk_D ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','104'])).

thf('106',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['88','90'])).

thf('108',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf(t25_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('109',plain,(
    ! [X28: $i,X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t25_relset_1])).

thf('110',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('114',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('115',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('116',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('117',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['115','116'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('118',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['113','117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['50','108','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qbHJwEg3jy
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:10:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 238 iterations in 0.125s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.56  thf(t77_funct_2, conjecture,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.56       ( ( v2_funct_1 @ B ) <=>
% 0.36/0.56         ( ![C:$i,D:$i]:
% 0.36/0.56           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.36/0.56               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.36/0.56             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i]:
% 0.36/0.56        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.56            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.56          ( ( v2_funct_1 @ B ) <=>
% 0.36/0.56            ( ![C:$i,D:$i]:
% 0.36/0.56              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.36/0.56                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.36/0.56                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.36/0.56  thf('0', plain, (((r2_hidden @ sk_C_2 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf(t7_ordinal1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X20 : $i, X21 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.36/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X34 : $i, X35 : $i]:
% 0.36/0.56         (((X35) = (X34))
% 0.36/0.56          | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56          | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56          | ~ (r2_hidden @ X35 @ sk_A)
% 0.36/0.56          | (v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (((v2_funct_1 @ sk_B_1)) | 
% 0.36/0.56       (![X34 : $i, X35 : $i]:
% 0.36/0.56          (((X35) = (X34))
% 0.36/0.56           | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56           | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56           | ~ (r2_hidden @ X35 @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['4'])).
% 0.36/0.56  thf(d8_funct_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.56       ( ( v2_funct_1 @ A ) <=>
% 0.36/0.56         ( ![B:$i,C:$i]:
% 0.36/0.56           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.36/0.56               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.36/0.56               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.36/0.56             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (![X15 : $i]:
% 0.36/0.56         ((r2_hidden @ (sk_C_1 @ X15) @ (k1_relat_1 @ X15))
% 0.36/0.56          | (v2_funct_1 @ X15)
% 0.36/0.56          | ~ (v1_funct_1 @ X15)
% 0.36/0.56          | ~ (v1_relat_1 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(cc2_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.56         ((v4_relat_1 @ X25 @ X26)
% 0.36/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.56  thf('9', plain, ((v4_relat_1 @ sk_B_1 @ sk_A)),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf(d18_relat_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( v1_relat_1 @ B ) =>
% 0.36/0.56       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         (~ (v4_relat_1 @ X7 @ X8)
% 0.36/0.56          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.36/0.56          | ~ (v1_relat_1 @ X7))),
% 0.36/0.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      ((~ (v1_relat_1 @ sk_B_1) | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(cc1_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( v1_relat_1 @ C ) ))).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.56         ((v1_relat_1 @ X22)
% 0.36/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.56  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.36/0.56      inference('demod', [status(thm)], ['11', '14'])).
% 0.36/0.56  thf(d3_tarski, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | (r2_hidden @ X0 @ X2)
% 0.36/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      ((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.56        | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.56        | (v2_funct_1 @ sk_B_1)
% 0.36/0.56        | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['6', '17'])).
% 0.36/0.56  thf('19', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('20', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      (![X15 : $i]:
% 0.36/0.56         (((k1_funct_1 @ X15 @ (sk_B @ X15))
% 0.36/0.56            = (k1_funct_1 @ X15 @ (sk_C_1 @ X15)))
% 0.36/0.56          | (v2_funct_1 @ X15)
% 0.36/0.56          | ~ (v1_funct_1 @ X15)
% 0.36/0.56          | ~ (v1_relat_1 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      ((![X34 : $i, X35 : $i]:
% 0.36/0.56          (((X35) = (X34))
% 0.36/0.56           | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56           | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56           | ~ (r2_hidden @ X35 @ sk_A)))
% 0.36/0.56         <= ((![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('split', [status(esa)], ['4'])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.36/0.56             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.36/0.56           | ~ (v1_relat_1 @ sk_B_1)
% 0.36/0.56           | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.56           | (v2_funct_1 @ sk_B_1)
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.56           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.36/0.56           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.36/0.56         <= ((![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.56  thf('25', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('26', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.36/0.56             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.36/0.56           | (v2_funct_1 @ sk_B_1)
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.56           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.36/0.56           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.36/0.56         <= ((![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((v2_funct_1 @ sk_B_1)
% 0.36/0.56           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.56           | (v2_funct_1 @ sk_B_1)
% 0.36/0.56           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.36/0.56               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.36/0.56         <= ((![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['21', '27'])).
% 0.36/0.56  thf('29', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.36/0.56             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.56           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.36/0.56           | (v2_funct_1 @ sk_B_1)))
% 0.36/0.56         <= ((![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      ((((v2_funct_1 @ sk_B_1)
% 0.36/0.56         | ((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1))
% 0.36/0.56         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.36/0.56         <= ((![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('eq_res', [status(thm)], ['29'])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X15 : $i]:
% 0.36/0.56         ((r2_hidden @ (sk_B @ X15) @ (k1_relat_1 @ X15))
% 0.36/0.56          | (v2_funct_1 @ X15)
% 0.36/0.56          | ~ (v1_funct_1 @ X15)
% 0.36/0.56          | ~ (v1_relat_1 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      ((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.56        | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.56        | (v2_funct_1 @ sk_B_1)
% 0.36/0.56        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.56  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('35', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.36/0.56         <= ((![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('clc', [status(thm)], ['30', '36'])).
% 0.36/0.56  thf('38', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      ((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)))
% 0.36/0.56         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.36/0.56             (![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.56  thf('40', plain,
% 0.36/0.56      (![X15 : $i]:
% 0.36/0.56         (((sk_B @ X15) != (sk_C_1 @ X15))
% 0.36/0.56          | (v2_funct_1 @ X15)
% 0.36/0.56          | ~ (v1_funct_1 @ X15)
% 0.36/0.56          | ~ (v1_relat_1 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.36/0.56         | ~ (v1_relat_1 @ sk_B_1)
% 0.36/0.56         | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.56         | (v2_funct_1 @ sk_B_1)))
% 0.36/0.56         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.36/0.56             (![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.56  thf('42', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('43', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.36/0.56         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.36/0.56             (![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.36/0.56  thf('45', plain,
% 0.36/0.56      (((v2_funct_1 @ sk_B_1))
% 0.36/0.56         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.36/0.56             (![X34 : $i, X35 : $i]:
% 0.36/0.56                (((X35) = (X34))
% 0.36/0.56                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.36/0.56  thf('46', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      (~
% 0.36/0.56       (![X34 : $i, X35 : $i]:
% 0.36/0.56          (((X35) = (X34))
% 0.36/0.56           | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.36/0.56           | ~ (r2_hidden @ X34 @ sk_A)
% 0.36/0.56           | ~ (r2_hidden @ X35 @ sk_A))) | 
% 0.36/0.56       ((v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.56  thf('48', plain, (((r2_hidden @ sk_C_2 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('49', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['5', '47', '48'])).
% 0.36/0.56  thf('50', plain, (~ (r1_tarski @ sk_A @ sk_C_2)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['3', '49'])).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('52', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['5', '47', '48'])).
% 0.36/0.56  thf('53', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['51', '52'])).
% 0.36/0.56  thf('54', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t32_funct_2, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.56       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.36/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.56           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.36/0.56             ( C ) ) ) ) ))).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X30 @ X31)
% 0.36/0.56          | ((X32) = (k1_xboole_0))
% 0.36/0.56          | ~ (v1_funct_1 @ X33)
% 0.36/0.56          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.36/0.56          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.36/0.56          | ((k1_funct_1 @ (k2_funct_1 @ X33) @ (k1_funct_1 @ X33 @ X30))
% 0.36/0.56              = (X30))
% 0.36/0.56          | ~ (v2_funct_1 @ X33))),
% 0.36/0.56      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.36/0.56  thf('56', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v2_funct_1 @ sk_B_1)
% 0.36/0.56          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.36/0.56              = (X0))
% 0.36/0.56          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.36/0.56          | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.56          | ((sk_A) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.56  thf('57', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['4'])).
% 0.36/0.56  thf('58', plain, (((v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['5', '47'])).
% 0.36/0.56  thf('59', plain, ((v2_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('60', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('61', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.36/0.56            = (X0))
% 0.36/0.56          | ((sk_A) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['56', '59', '60', '61'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))
% 0.36/0.56        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.36/0.56            = (sk_C_2)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['53', '62'])).
% 0.36/0.56  thf(d4_funct_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.56       ( ![B:$i,C:$i]:
% 0.36/0.56         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.36/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.36/0.56               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.56           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.36/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.36/0.56               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.56         ((r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.36/0.56          | ((X13) = (k1_xboole_0))
% 0.36/0.56          | ((X13) != (k1_funct_1 @ X12 @ X11))
% 0.36/0.56          | ~ (v1_funct_1 @ X12)
% 0.36/0.56          | ~ (v1_relat_1 @ X12))),
% 0.36/0.56      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      (![X11 : $i, X12 : $i]:
% 0.36/0.56         (~ (v1_relat_1 @ X12)
% 0.36/0.56          | ~ (v1_funct_1 @ X12)
% 0.36/0.56          | ((k1_funct_1 @ X12 @ X11) = (k1_xboole_0))
% 0.36/0.56          | (r2_hidden @ X11 @ (k1_relat_1 @ X12)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.56  thf(t56_funct_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.56       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.36/0.56         ( ( ( A ) =
% 0.36/0.56             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.36/0.56           ( ( A ) =
% 0.36/0.56             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.36/0.56  thf('66', plain,
% 0.36/0.56      (![X18 : $i, X19 : $i]:
% 0.36/0.56         (~ (v2_funct_1 @ X18)
% 0.36/0.56          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X18))
% 0.36/0.56          | ((X19)
% 0.36/0.56              = (k1_funct_1 @ (k2_funct_1 @ X18) @ (k1_funct_1 @ X18 @ X19)))
% 0.36/0.56          | ~ (v1_funct_1 @ X18)
% 0.36/0.56          | ~ (v1_relat_1 @ X18))),
% 0.36/0.56      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.36/0.56  thf('67', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.36/0.56          | ~ (v1_funct_1 @ X0)
% 0.36/0.56          | ~ (v1_relat_1 @ X0)
% 0.36/0.56          | ~ (v1_relat_1 @ X0)
% 0.36/0.56          | ~ (v1_funct_1 @ X0)
% 0.36/0.56          | ((X1) = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1)))
% 0.36/0.56          | ~ (v2_funct_1 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.56  thf('68', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (~ (v2_funct_1 @ X0)
% 0.36/0.56          | ((X1) = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1)))
% 0.36/0.56          | ~ (v1_relat_1 @ X0)
% 0.36/0.56          | ~ (v1_funct_1 @ X0)
% 0.36/0.56          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['67'])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.36/0.56        | ~ (v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.36/0.56         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.36/0.56      inference('split', [status(esa)], ['69'])).
% 0.36/0.56  thf('71', plain,
% 0.36/0.56      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.36/0.56       ~ ((v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('split', [status(esa)], ['69'])).
% 0.36/0.56  thf('72', plain,
% 0.36/0.56      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['5', '47', '71'])).
% 0.36/0.56  thf('73', plain,
% 0.36/0.56      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['70', '72'])).
% 0.36/0.56  thf('74', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (~ (v2_funct_1 @ X0)
% 0.36/0.56          | ((X1) = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1)))
% 0.36/0.56          | ~ (v1_relat_1 @ X0)
% 0.36/0.56          | ~ (v1_funct_1 @ X0)
% 0.36/0.56          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['67'])).
% 0.36/0.56  thf('75', plain,
% 0.36/0.56      ((((sk_D)
% 0.36/0.56          = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.36/0.56             (k1_funct_1 @ sk_B_1 @ sk_C_2)))
% 0.36/0.56        | ((k1_funct_1 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 0.36/0.56        | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.56        | ~ (v1_relat_1 @ sk_B_1)
% 0.36/0.56        | ~ (v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('sup+', [status(thm)], ['73', '74'])).
% 0.36/0.56  thf('76', plain,
% 0.36/0.56      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['70', '72'])).
% 0.36/0.56  thf('77', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('78', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('79', plain, ((v2_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('80', plain,
% 0.36/0.56      ((((sk_D)
% 0.36/0.56          = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.36/0.56             (k1_funct_1 @ sk_B_1 @ sk_C_2)))
% 0.36/0.56        | ((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.36/0.56  thf('81', plain,
% 0.36/0.56      ((((sk_D) = (sk_C_2))
% 0.36/0.56        | ((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))
% 0.36/0.56        | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.56        | ~ (v1_relat_1 @ sk_B_1)
% 0.36/0.56        | ~ (v2_funct_1 @ sk_B_1)
% 0.36/0.56        | ((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['68', '80'])).
% 0.36/0.56  thf('82', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('83', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('84', plain, ((v2_funct_1 @ sk_B_1)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('85', plain,
% 0.36/0.56      ((((sk_D) = (sk_C_2))
% 0.36/0.56        | ((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))
% 0.36/0.56        | ((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.36/0.56  thf('86', plain,
% 0.36/0.56      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_xboole_0)) | ((sk_D) = (sk_C_2)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['85'])).
% 0.36/0.56  thf('87', plain, ((((sk_C_2) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('88', plain, ((((sk_C_2) != (sk_D))) <= (~ (((sk_C_2) = (sk_D))))),
% 0.36/0.56      inference('split', [status(esa)], ['87'])).
% 0.36/0.56  thf('89', plain, (~ (((sk_C_2) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('split', [status(esa)], ['87'])).
% 0.36/0.56  thf('90', plain, (~ (((sk_C_2) = (sk_D)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['5', '47', '89'])).
% 0.36/0.56  thf('91', plain, (((sk_C_2) != (sk_D))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['88', '90'])).
% 0.36/0.56  thf('92', plain, (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['86', '91'])).
% 0.36/0.56  thf('93', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))
% 0.36/0.56        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ k1_xboole_0) = (sk_C_2)))),
% 0.36/0.56      inference('demod', [status(thm)], ['63', '92'])).
% 0.36/0.56  thf('94', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('95', plain,
% 0.36/0.56      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['94'])).
% 0.36/0.56  thf('96', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.36/0.56      inference('split', [status(esa)], ['94'])).
% 0.36/0.56  thf('97', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['5', '47', '96'])).
% 0.36/0.56  thf('98', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['95', '97'])).
% 0.36/0.56  thf('99', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.36/0.56            = (X0))
% 0.36/0.56          | ((sk_A) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['56', '59', '60', '61'])).
% 0.36/0.56  thf('100', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))
% 0.36/0.56        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.36/0.56            = (sk_D)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['98', '99'])).
% 0.36/0.56  thf('101', plain,
% 0.36/0.56      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['70', '72'])).
% 0.36/0.56  thf('102', plain, (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['86', '91'])).
% 0.36/0.56  thf('103', plain, (((k1_xboole_0) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.36/0.56      inference('demod', [status(thm)], ['101', '102'])).
% 0.36/0.56  thf('104', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))
% 0.36/0.56        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ k1_xboole_0) = (sk_D)))),
% 0.36/0.56      inference('demod', [status(thm)], ['100', '103'])).
% 0.36/0.56  thf('105', plain,
% 0.36/0.56      ((((sk_C_2) = (sk_D))
% 0.36/0.56        | ((sk_A) = (k1_xboole_0))
% 0.36/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['93', '104'])).
% 0.36/0.56  thf('106', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['105'])).
% 0.36/0.56  thf('107', plain, (((sk_C_2) != (sk_D))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['88', '90'])).
% 0.36/0.56  thf('108', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 0.36/0.56  thf(t25_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.36/0.56  thf('109', plain,
% 0.36/0.56      (![X28 : $i, X29 : $i]:
% 0.36/0.56         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t25_relset_1])).
% 0.36/0.56  thf('110', plain,
% 0.36/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.56         ((v4_relat_1 @ X25 @ X26)
% 0.36/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.56  thf('111', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['109', '110'])).
% 0.36/0.56  thf('112', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         (~ (v4_relat_1 @ X7 @ X8)
% 0.36/0.56          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.36/0.56          | ~ (v1_relat_1 @ X7))),
% 0.36/0.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.36/0.56  thf('113', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.56          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['111', '112'])).
% 0.36/0.56  thf(t113_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.56  thf('114', plain,
% 0.36/0.56      (![X5 : $i, X6 : $i]:
% 0.36/0.56         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.56  thf('115', plain,
% 0.36/0.56      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['114'])).
% 0.36/0.56  thf(fc6_relat_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.56  thf('116', plain,
% 0.36/0.56      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.56  thf('117', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.56      inference('sup+', [status(thm)], ['115', '116'])).
% 0.36/0.56  thf(t60_relat_1, axiom,
% 0.36/0.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.56  thf('118', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.56  thf('119', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.56      inference('demod', [status(thm)], ['113', '117', '118'])).
% 0.36/0.56  thf('120', plain, ($false),
% 0.36/0.56      inference('demod', [status(thm)], ['50', '108', '119'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
