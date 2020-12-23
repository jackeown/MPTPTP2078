%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NNCcAns7Tz

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  141 (1868 expanded)
%              Number of leaves         :   31 ( 525 expanded)
%              Depth                    :   31
%              Number of atoms          : 1162 (31652 expanded)
%              Number of equality atoms :   95 (2134 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( ( k1_funct_1 @ sk_B_1 @ X35 )
       != ( k1_funct_1 @ sk_B_1 @ X34 ) )
      | ~ ( r2_hidden @ X34 @ sk_A )
      | ~ ( r2_hidden @ X35 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

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

thf('4',plain,(
    ! [X16: $i] :
      ( ( r2_hidden @ ( sk_C @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( ( k1_funct_1 @ X16 @ ( sk_B @ X16 ) )
        = ( k1_funct_1 @ X16 @ ( sk_C @ X16 ) ) )
      | ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('21',plain,
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
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ~ ( v1_funct_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('24',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
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
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    ! [X16: $i] :
      ( ( r2_hidden @ ( sk_B @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('33',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_1 @ X35 )
         != ( k1_funct_1 @ sk_B_1 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_1 @ X35 )
           != ( k1_funct_1 @ sk_B_1 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X16: $i] :
      ( ( ( sk_B @ X16 )
       != ( sk_C @ X16 ) )
      | ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('40',plain,
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
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('42',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
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
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_1 @ X35 )
           != ( k1_funct_1 @ sk_B_1 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('46',plain,
    ( ~ ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_1 @ X35 )
           != ( k1_funct_1 @ sk_B_1 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','46','47'])).

thf('49',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('51',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('52',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','46','51'])).

thf('53',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['50','52'])).

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
    inference(split,[status(esa)],['2'])).

thf('58',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','46'])).

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
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59','60','61'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['67'])).

thf('70',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','46','69'])).

thf('71',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['75'])).

thf('78',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','46','77'])).

thf('79',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['74','79'])).

thf('81',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['49','80'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('82',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['86'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('88',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('90',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['50','52'])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['74','79'])).

thf('97',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( X0 = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_D = sk_C_1 ),
    inference('sup-',[status(thm)],['94','105'])).

thf('107',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NNCcAns7Tz
% 0.13/0.36  % Computer   : n014.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:19:07 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 221 iterations in 0.092s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.54  thf(sk_C_type, type, sk_C: $i > $i).
% 0.23/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.23/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.54  thf(t77_funct_2, conjecture,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.23/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.54       ( ( v2_funct_1 @ B ) <=>
% 0.23/0.54         ( ![C:$i,D:$i]:
% 0.23/0.54           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.23/0.54               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.23/0.54             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i,B:$i]:
% 0.23/0.54        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.23/0.54            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.54          ( ( v2_funct_1 @ B ) <=>
% 0.23/0.54            ( ![C:$i,D:$i]:
% 0.23/0.54              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.23/0.54                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.23/0.54                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.23/0.54  thf('0', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (![X34 : $i, X35 : $i]:
% 0.23/0.54         (((X35) = (X34))
% 0.23/0.54          | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54          | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54          | ~ (r2_hidden @ X35 @ sk_A)
% 0.23/0.54          | (v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      (((v2_funct_1 @ sk_B_1)) | 
% 0.23/0.54       (![X34 : $i, X35 : $i]:
% 0.23/0.54          (((X35) = (X34))
% 0.23/0.54           | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54           | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54           | ~ (r2_hidden @ X35 @ sk_A)))),
% 0.23/0.54      inference('split', [status(esa)], ['2'])).
% 0.23/0.54  thf(d8_funct_1, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.54       ( ( v2_funct_1 @ A ) <=>
% 0.23/0.54         ( ![B:$i,C:$i]:
% 0.23/0.54           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.23/0.54               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.23/0.54               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.23/0.54             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.23/0.54  thf('4', plain,
% 0.23/0.54      (![X16 : $i]:
% 0.23/0.54         ((r2_hidden @ (sk_C @ X16) @ (k1_relat_1 @ X16))
% 0.23/0.54          | (v2_funct_1 @ X16)
% 0.23/0.54          | ~ (v1_funct_1 @ X16)
% 0.23/0.54          | ~ (v1_relat_1 @ X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(dt_k1_relset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.54       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.23/0.54         ((m1_subset_1 @ (k1_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X24))
% 0.23/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.23/0.54        (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.23/0.54         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.23/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['7', '10'])).
% 0.23/0.54  thf(l3_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X6 @ X7)
% 0.23/0.54          | (r2_hidden @ X6 @ X8)
% 0.23/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      ((~ (v1_relat_1 @ sk_B_1)
% 0.23/0.54        | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.54        | (v2_funct_1 @ sk_B_1)
% 0.23/0.54        | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['4', '13'])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(cc1_relset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.54       ( v1_relat_1 @ C ) ))).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.54         ((v1_relat_1 @ X21)
% 0.23/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.23/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.54  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X16 : $i]:
% 0.23/0.54         (((k1_funct_1 @ X16 @ (sk_B @ X16))
% 0.23/0.54            = (k1_funct_1 @ X16 @ (sk_C @ X16)))
% 0.23/0.54          | (v2_funct_1 @ X16)
% 0.23/0.54          | ~ (v1_funct_1 @ X16)
% 0.23/0.54          | ~ (v1_relat_1 @ X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      ((![X34 : $i, X35 : $i]:
% 0.23/0.54          (((X35) = (X34))
% 0.23/0.54           | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54           | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54           | ~ (r2_hidden @ X35 @ sk_A)))
% 0.23/0.54         <= ((![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('split', [status(esa)], ['2'])).
% 0.23/0.54  thf('22', plain,
% 0.23/0.54      ((![X0 : $i]:
% 0.23/0.54          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.23/0.54             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.23/0.54           | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.54           | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.54           | (v2_funct_1 @ sk_B_1)
% 0.23/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.54           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.23/0.54           | ((X0) = (sk_C @ sk_B_1))))
% 0.23/0.54         <= ((![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.54  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('24', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      ((![X0 : $i]:
% 0.23/0.54          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.23/0.54             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.23/0.54           | (v2_funct_1 @ sk_B_1)
% 0.23/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.54           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.23/0.54           | ((X0) = (sk_C @ sk_B_1))))
% 0.23/0.54         <= ((![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      ((![X0 : $i]:
% 0.23/0.54          ((v2_funct_1 @ sk_B_1)
% 0.23/0.54           | ((X0) = (sk_C @ sk_B_1))
% 0.23/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.54           | (v2_funct_1 @ sk_B_1)
% 0.23/0.54           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.23/0.54               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.23/0.54         <= ((![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '25'])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      ((![X0 : $i]:
% 0.23/0.54          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.23/0.54             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.23/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.54           | ((X0) = (sk_C @ sk_B_1))
% 0.23/0.54           | (v2_funct_1 @ sk_B_1)))
% 0.23/0.54         <= ((![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      ((((v2_funct_1 @ sk_B_1)
% 0.23/0.54         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.23/0.54         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.23/0.54         <= ((![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('eq_res', [status(thm)], ['27'])).
% 0.23/0.54  thf('29', plain,
% 0.23/0.54      (![X16 : $i]:
% 0.23/0.54         ((r2_hidden @ (sk_B @ X16) @ (k1_relat_1 @ X16))
% 0.23/0.54          | (v2_funct_1 @ X16)
% 0.23/0.54          | ~ (v1_funct_1 @ X16)
% 0.23/0.54          | ~ (v1_relat_1 @ X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.23/0.54  thf('30', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      ((~ (v1_relat_1 @ sk_B_1)
% 0.23/0.54        | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.54        | (v2_funct_1 @ sk_B_1)
% 0.23/0.54        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.23/0.54  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('33', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.23/0.54  thf('35', plain,
% 0.23/0.54      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.23/0.54         <= ((![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('clc', [status(thm)], ['28', '34'])).
% 0.23/0.54  thf('36', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('37', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.23/0.54      inference('split', [status(esa)], ['36'])).
% 0.23/0.54  thf('38', plain,
% 0.23/0.54      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.23/0.54         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.23/0.54             (![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['35', '37'])).
% 0.23/0.54  thf('39', plain,
% 0.23/0.54      (![X16 : $i]:
% 0.23/0.54         (((sk_B @ X16) != (sk_C @ X16))
% 0.23/0.54          | (v2_funct_1 @ X16)
% 0.23/0.54          | ~ (v1_funct_1 @ X16)
% 0.23/0.54          | ~ (v1_relat_1 @ X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.23/0.54  thf('40', plain,
% 0.23/0.54      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.23/0.54         | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.54         | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.54         | (v2_funct_1 @ sk_B_1)))
% 0.23/0.54         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.23/0.54             (![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.23/0.54  thf('41', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('43', plain,
% 0.23/0.54      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.23/0.54         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.23/0.54             (![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.23/0.54  thf('44', plain,
% 0.23/0.54      (((v2_funct_1 @ sk_B_1))
% 0.23/0.54         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.23/0.54             (![X34 : $i, X35 : $i]:
% 0.23/0.54                (((X35) = (X34))
% 0.23/0.54                 | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.23/0.54      inference('simplify', [status(thm)], ['43'])).
% 0.23/0.54  thf('45', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.23/0.54      inference('split', [status(esa)], ['36'])).
% 0.23/0.54  thf('46', plain,
% 0.23/0.54      (~
% 0.23/0.54       (![X34 : $i, X35 : $i]:
% 0.23/0.54          (((X35) = (X34))
% 0.23/0.54           | ((k1_funct_1 @ sk_B_1 @ X35) != (k1_funct_1 @ sk_B_1 @ X34))
% 0.23/0.54           | ~ (r2_hidden @ X34 @ sk_A)
% 0.23/0.54           | ~ (r2_hidden @ X35 @ sk_A))) | 
% 0.23/0.54       ((v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.23/0.54  thf('47', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('48', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['3', '46', '47'])).
% 0.23/0.54  thf('49', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 0.23/0.54  thf('50', plain,
% 0.23/0.54      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.23/0.54      inference('split', [status(esa)], ['36'])).
% 0.23/0.54  thf('51', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('split', [status(esa)], ['36'])).
% 0.23/0.54  thf('52', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['3', '46', '51'])).
% 0.23/0.54  thf('53', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['50', '52'])).
% 0.23/0.54  thf('54', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(t32_funct_2, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.54       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.23/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.23/0.54           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.23/0.54             ( C ) ) ) ) ))).
% 0.23/0.54  thf('55', plain,
% 0.23/0.54      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X30 @ X31)
% 0.23/0.54          | ((X32) = (k1_xboole_0))
% 0.23/0.54          | ~ (v1_funct_1 @ X33)
% 0.23/0.54          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.23/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.23/0.54          | ((k1_funct_1 @ (k2_funct_1 @ X33) @ (k1_funct_1 @ X33 @ X30))
% 0.23/0.54              = (X30))
% 0.23/0.54          | ~ (v2_funct_1 @ X33))),
% 0.23/0.54      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.23/0.54  thf('56', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (v2_funct_1 @ sk_B_1)
% 0.23/0.54          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.23/0.54              = (X0))
% 0.23/0.54          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.23/0.54          | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.54          | ((sk_A) = (k1_xboole_0))
% 0.23/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.23/0.54  thf('57', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.23/0.54      inference('split', [status(esa)], ['2'])).
% 0.23/0.54  thf('58', plain, (((v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['3', '46'])).
% 0.23/0.54  thf('59', plain, ((v2_funct_1 @ sk_B_1)),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.23/0.54  thf('60', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('61', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('62', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.23/0.54            = (X0))
% 0.23/0.54          | ((sk_A) = (k1_xboole_0))
% 0.23/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['56', '59', '60', '61'])).
% 0.23/0.54  thf('63', plain,
% 0.23/0.54      ((((sk_A) = (k1_xboole_0))
% 0.23/0.54        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.23/0.54            = (sk_C_1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['53', '62'])).
% 0.23/0.54  thf('64', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 0.23/0.54  thf('65', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.23/0.54            = (X0))
% 0.23/0.54          | ((sk_A) = (k1_xboole_0))
% 0.23/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['56', '59', '60', '61'])).
% 0.23/0.54  thf('66', plain,
% 0.23/0.54      ((((sk_A) = (k1_xboole_0))
% 0.23/0.54        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.23/0.54            = (sk_D)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.23/0.54  thf('67', plain,
% 0.23/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.23/0.54        | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('68', plain,
% 0.23/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.23/0.54         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.23/0.54      inference('split', [status(esa)], ['67'])).
% 0.23/0.54  thf('69', plain,
% 0.23/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.23/0.54       ~ ((v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('split', [status(esa)], ['67'])).
% 0.23/0.54  thf('70', plain,
% 0.23/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['3', '46', '69'])).
% 0.23/0.54  thf('71', plain,
% 0.23/0.54      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 0.23/0.54  thf('72', plain,
% 0.23/0.54      ((((sk_A) = (k1_xboole_0))
% 0.23/0.54        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.23/0.54            = (sk_D)))),
% 0.23/0.54      inference('demod', [status(thm)], ['66', '71'])).
% 0.23/0.54  thf('73', plain,
% 0.23/0.54      ((((sk_C_1) = (sk_D))
% 0.23/0.54        | ((sk_A) = (k1_xboole_0))
% 0.23/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.54      inference('sup+', [status(thm)], ['63', '72'])).
% 0.23/0.54  thf('74', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['73'])).
% 0.23/0.54  thf('75', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('76', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.23/0.54      inference('split', [status(esa)], ['75'])).
% 0.23/0.54  thf('77', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.23/0.54      inference('split', [status(esa)], ['75'])).
% 0.23/0.54  thf('78', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['3', '46', '77'])).
% 0.23/0.54  thf('79', plain, (((sk_C_1) != (sk_D))),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 0.23/0.54  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['74', '79'])).
% 0.23/0.54  thf('81', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.23/0.54      inference('demod', [status(thm)], ['49', '80'])).
% 0.23/0.54  thf(t4_subset_1, axiom,
% 0.23/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.54  thf('82', plain,
% 0.23/0.54      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.23/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.54  thf('83', plain,
% 0.23/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X6 @ X7)
% 0.23/0.54          | (r2_hidden @ X6 @ X8)
% 0.23/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.23/0.54  thf('84', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['82', '83'])).
% 0.23/0.54  thf('85', plain, (![X0 : $i]: (r2_hidden @ sk_D @ X0)),
% 0.23/0.54      inference('sup-', [status(thm)], ['81', '84'])).
% 0.23/0.54  thf(d10_xboole_0, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.54  thf('86', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.54  thf('87', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.54      inference('simplify', [status(thm)], ['86'])).
% 0.23/0.54  thf(t3_subset, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.54  thf('88', plain,
% 0.23/0.54      (![X10 : $i, X12 : $i]:
% 0.23/0.54         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.23/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.54  thf('89', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['87', '88'])).
% 0.23/0.54  thf(t4_subset, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.23/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.23/0.54  thf('90', plain,
% 0.23/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X13 @ X14)
% 0.23/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.23/0.54          | (m1_subset_1 @ X13 @ X15))),
% 0.23/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.23/0.54  thf('91', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.23/0.54  thf('92', plain, (![X0 : $i]: (m1_subset_1 @ sk_D @ X0)),
% 0.23/0.54      inference('sup-', [status(thm)], ['85', '91'])).
% 0.23/0.54  thf('93', plain,
% 0.23/0.54      (![X10 : $i, X11 : $i]:
% 0.23/0.54         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.54  thf('94', plain, (![X0 : $i]: (r1_tarski @ sk_D @ X0)),
% 0.23/0.54      inference('sup-', [status(thm)], ['92', '93'])).
% 0.23/0.54  thf('95', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['50', '52'])).
% 0.23/0.54  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['74', '79'])).
% 0.23/0.54  thf('97', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.23/0.54      inference('demod', [status(thm)], ['95', '96'])).
% 0.23/0.54  thf('98', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['82', '83'])).
% 0.23/0.54  thf('99', plain, (![X0 : $i]: (r2_hidden @ sk_C_1 @ X0)),
% 0.23/0.54      inference('sup-', [status(thm)], ['97', '98'])).
% 0.23/0.54  thf('100', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.23/0.54  thf('101', plain, (![X0 : $i]: (m1_subset_1 @ sk_C_1 @ X0)),
% 0.23/0.54      inference('sup-', [status(thm)], ['99', '100'])).
% 0.23/0.54  thf('102', plain,
% 0.23/0.54      (![X10 : $i, X11 : $i]:
% 0.23/0.54         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.54  thf('103', plain, (![X0 : $i]: (r1_tarski @ sk_C_1 @ X0)),
% 0.23/0.54      inference('sup-', [status(thm)], ['101', '102'])).
% 0.23/0.54  thf('104', plain,
% 0.23/0.54      (![X0 : $i, X2 : $i]:
% 0.23/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.54  thf('105', plain,
% 0.23/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_1) | ((X0) = (sk_C_1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['103', '104'])).
% 0.23/0.54  thf('106', plain, (((sk_D) = (sk_C_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['94', '105'])).
% 0.23/0.54  thf('107', plain, (((sk_C_1) != (sk_D))),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 0.23/0.54  thf('108', plain, ($false),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
