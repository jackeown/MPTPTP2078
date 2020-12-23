%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SQgppIrh01

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 (2731 expanded)
%              Number of leaves         :   31 ( 760 expanded)
%              Depth                    :   32
%              Number of atoms          : 1168 (46489 expanded)
%              Number of equality atoms :   99 (3141 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X27: $i,X28: $i] :
      ( ( X28 = X27 )
      | ( ( k1_funct_1 @ sk_B_1 @ X28 )
       != ( k1_funct_1 @ sk_B_1 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ sk_A )
      | ~ ( r2_hidden @ X28 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
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
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_C @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ X11 @ ( sk_B @ X11 ) )
        = ( k1_funct_1 @ X11 @ ( sk_C @ X11 ) ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('21',plain,
    ( ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
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
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
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
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
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
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_B @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
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
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( ( sk_B @ X11 )
       != ( sk_C @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('40',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
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
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('46',plain,
    ( ~ ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) )
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X26 ) @ ( k1_funct_1 @ X26 @ X23 ) )
        = X23 )
      | ~ ( v2_funct_1 @ X26 ) ) ),
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

thf('57',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('61',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','46'])).

thf('62',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','63'])).

thf('65',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['68'])).

thf('71',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','46','70'])).

thf('72',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['76'])).

thf('79',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','46','78'])).

thf('80',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['75','80'])).

thf('82',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['49','81'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('83',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('84',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('91',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('94',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['50','52'])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['75','80'])).

thf('96',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('100',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('104',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C_1 )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['93','104','105'])).

thf('107',plain,(
    sk_D = sk_C_1 ),
    inference('sup-',[status(thm)],['92','106'])).

thf('108',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SQgppIrh01
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:22:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 146 iterations in 0.070s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(t77_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ B ) <=>
% 0.21/0.53         ( ![C:$i,D:$i]:
% 0.21/0.53           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.53               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.53             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.53            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.53          ( ( v2_funct_1 @ B ) <=>
% 0.21/0.53            ( ![C:$i,D:$i]:
% 0.21/0.53              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.53                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.53                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.21/0.53  thf('0', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i]:
% 0.21/0.53         (((X28) = (X27))
% 0.21/0.53          | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53          | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53          | ~ (r2_hidden @ X28 @ sk_A)
% 0.21/0.53          | (v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((v2_funct_1 @ sk_B_1)) | 
% 0.21/0.53       (![X27 : $i, X28 : $i]:
% 0.21/0.53          (((X28) = (X27))
% 0.21/0.53           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53           | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53           | ~ (r2_hidden @ X28 @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf(d8_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.53         ( ![B:$i,C:$i]:
% 0.21/0.53           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.53               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.53               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.21/0.53             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X11 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C @ X11) @ (k1_relat_1 @ X11))
% 0.21/0.53          | (v2_funct_1 @ X11)
% 0.21/0.53          | ~ (v1_funct_1 @ X11)
% 0.21/0.53          | ~ (v1_relat_1 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_k1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k1_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X17))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.53         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.53  thf(l3_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ X2)
% 0.21/0.53          | (r2_hidden @ X1 @ X3)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.53        | (v2_funct_1 @ sk_B_1)
% 0.21/0.53        | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( v1_relat_1 @ C ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.53         ((v1_relat_1 @ X14)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.53  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X11 : $i]:
% 0.21/0.53         (((k1_funct_1 @ X11 @ (sk_B @ X11))
% 0.21/0.53            = (k1_funct_1 @ X11 @ (sk_C @ X11)))
% 0.21/0.53          | (v2_funct_1 @ X11)
% 0.21/0.53          | ~ (v1_funct_1 @ X11)
% 0.21/0.53          | ~ (v1_relat_1 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((![X27 : $i, X28 : $i]:
% 0.21/0.53          (((X28) = (X27))
% 0.21/0.53           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53           | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53           | ~ (r2_hidden @ X28 @ sk_A)))
% 0.21/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.53             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.53           | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.53           | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.53           | (v2_funct_1 @ sk_B_1)
% 0.21/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.53           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.21/0.53           | ((X0) = (sk_C @ sk_B_1))))
% 0.21/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('24', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.53             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.53           | (v2_funct_1 @ sk_B_1)
% 0.21/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.53           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.21/0.53           | ((X0) = (sk_C @ sk_B_1))))
% 0.21/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_funct_1 @ sk_B_1)
% 0.21/0.53           | ((X0) = (sk_C @ sk_B_1))
% 0.21/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.53           | (v2_funct_1 @ sk_B_1)
% 0.21/0.53           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.53               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.21/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.53             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.53           | ((X0) = (sk_C @ sk_B_1))
% 0.21/0.53           | (v2_funct_1 @ sk_B_1)))
% 0.21/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((((v2_funct_1 @ sk_B_1)
% 0.21/0.53         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.21/0.53         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.21/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X11 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_B @ X11) @ (k1_relat_1 @ X11))
% 0.21/0.53          | (v2_funct_1 @ X11)
% 0.21/0.53          | ~ (v1_funct_1 @ X11)
% 0.21/0.53          | ~ (v1_relat_1 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.53        | (v2_funct_1 @ sk_B_1)
% 0.21/0.53        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('33', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.21/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('clc', [status(thm)], ['28', '34'])).
% 0.21/0.53  thf('36', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.21/0.53      inference('split', [status(esa)], ['36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.21/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.53             (![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X11 : $i]:
% 0.21/0.53         (((sk_B @ X11) != (sk_C @ X11))
% 0.21/0.53          | (v2_funct_1 @ X11)
% 0.21/0.53          | ~ (v1_funct_1 @ X11)
% 0.21/0.53          | ~ (v1_relat_1 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.21/0.53         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.53         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.53         | (v2_funct_1 @ sk_B_1)))
% 0.21/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.53             (![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.21/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.53             (![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (((v2_funct_1 @ sk_B_1))
% 0.21/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.53             (![X27 : $i, X28 : $i]:
% 0.21/0.53                (((X28) = (X27))
% 0.21/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.53  thf('45', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.21/0.53      inference('split', [status(esa)], ['36'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (~
% 0.21/0.53       (![X27 : $i, X28 : $i]:
% 0.21/0.53          (((X28) = (X27))
% 0.21/0.53           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.21/0.53           | ~ (r2_hidden @ X27 @ sk_A)
% 0.21/0.53           | ~ (r2_hidden @ X28 @ sk_A))) | 
% 0.21/0.53       ((v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('48', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['3', '46', '47'])).
% 0.21/0.53  thf('49', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['36'])).
% 0.21/0.53  thf('51', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('split', [status(esa)], ['36'])).
% 0.21/0.53  thf('52', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['3', '46', '51'])).
% 0.21/0.53  thf('53', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['50', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t32_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.53       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.21/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.21/0.53             ( C ) ) ) ) ))).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X23 @ X24)
% 0.21/0.53          | ((X25) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.21/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.21/0.53          | ((k1_funct_1 @ (k2_funct_1 @ X26) @ (k1_funct_1 @ X26 @ X23))
% 0.21/0.53              = (X23))
% 0.21/0.53          | ~ (v2_funct_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ sk_B_1)
% 0.21/0.53          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.53              = (X0))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.53          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.53          | ((sk_A) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.53  thf('57', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ sk_B_1)
% 0.21/0.53          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.53              = (X0))
% 0.21/0.53          | ((sk_A) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.53  thf('60', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('61', plain, (((v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['3', '46'])).
% 0.21/0.53  thf('62', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['60', '61'])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.53            = (X0))
% 0.21/0.53          | ((sk_A) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['59', '62'])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0))
% 0.21/0.53        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.21/0.53            = (sk_C_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '63'])).
% 0.21/0.53  thf('65', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.53            = (X0))
% 0.21/0.53          | ((sk_A) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['59', '62'])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0))
% 0.21/0.53        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.21/0.53            = (sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.21/0.53        | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.21/0.53         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.21/0.53      inference('split', [status(esa)], ['68'])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.21/0.53       ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('split', [status(esa)], ['68'])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['3', '46', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['69', '71'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0))
% 0.21/0.53        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.21/0.53            = (sk_D)))),
% 0.21/0.53      inference('demod', [status(thm)], ['67', '72'])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      ((((sk_C_1) = (sk_D))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['64', '73'])).
% 0.21/0.53  thf('75', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.53  thf('76', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('77', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.21/0.53      inference('split', [status(esa)], ['76'])).
% 0.21/0.53  thf('78', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.53      inference('split', [status(esa)], ['76'])).
% 0.21/0.53  thf('79', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['3', '46', '78'])).
% 0.21/0.53  thf('80', plain, (((sk_C_1) != (sk_D))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['77', '79'])).
% 0.21/0.53  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['75', '80'])).
% 0.21/0.53  thf('82', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.21/0.53      inference('demod', [status(thm)], ['49', '81'])).
% 0.21/0.53  thf(t4_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.53  thf('83', plain,
% 0.21/0.53      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf('84', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ X2)
% 0.21/0.53          | (r2_hidden @ X1 @ X3)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.53  thf('86', plain, (![X0 : $i]: (r2_hidden @ sk_D @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['82', '85'])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf(t4_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X8 @ X9)
% 0.21/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.21/0.53          | (m1_subset_1 @ X8 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.53  thf('89', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.53  thf('90', plain, (![X0 : $i]: (m1_subset_1 @ sk_D @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['86', '89'])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('92', plain, (![X0 : $i]: (r1_tarski @ sk_D @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.53  thf(t3_xboole_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf('93', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.53  thf('94', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['50', '52'])).
% 0.21/0.53  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['75', '80'])).
% 0.21/0.53  thf('96', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.21/0.53      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.53  thf('97', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.53  thf('98', plain, (![X0 : $i]: (r2_hidden @ sk_C_1 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.53  thf('99', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.53  thf('100', plain, (![X0 : $i]: (m1_subset_1 @ sk_C_1 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.53  thf('101', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('102', plain, (![X0 : $i]: (r1_tarski @ sk_C_1 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['100', '101'])).
% 0.21/0.53  thf('103', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.53  thf('104', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.53  thf('105', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.53  thf('106', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (sk_C_1)) | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['93', '104', '105'])).
% 0.21/0.53  thf('107', plain, (((sk_D) = (sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['92', '106'])).
% 0.21/0.53  thf('108', plain, (((sk_C_1) != (sk_D))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['77', '79'])).
% 0.21/0.53  thf('109', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
