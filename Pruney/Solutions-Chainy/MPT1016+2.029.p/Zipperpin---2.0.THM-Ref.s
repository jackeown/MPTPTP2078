%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T4usrhYeAV

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:55 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  133 (2289 expanded)
%              Number of leaves         :   28 ( 651 expanded)
%              Depth                    :   31
%              Number of atoms          : 1154 (36685 expanded)
%              Number of equality atoms :  100 (2416 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( ( k1_funct_1 @ sk_B_1 @ X27 )
       != ( k1_funct_1 @ sk_B_1 @ X26 ) )
      | ~ ( r2_hidden @ X26 @ sk_A )
      | ~ ( r2_hidden @ X27 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X26: $i,X27: $i] :
        ( ( X27 = X26 )
        | ( ( k1_funct_1 @ sk_B_1 @ X27 )
         != ( k1_funct_1 @ sk_B_1 @ X26 ) )
        | ~ ( r2_hidden @ X26 @ sk_A )
        | ~ ( r2_hidden @ X27 @ sk_A ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','19','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ X11 @ ( sk_B @ X11 ) )
        = ( k1_funct_1 @ X11 @ ( sk_C @ X11 ) ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('23',plain,
    ( ! [X26: $i,X27: $i] :
        ( ( X27 = X26 )
        | ( ( k1_funct_1 @ sk_B_1 @ X27 )
         != ( k1_funct_1 @ sk_B_1 @ X26 ) )
        | ~ ( r2_hidden @ X26 @ sk_A )
        | ~ ( r2_hidden @ X27 @ sk_A ) )
   <= ! [X26: $i,X27: $i] :
        ( ( X27 = X26 )
        | ( ( k1_funct_1 @ sk_B_1 @ X27 )
         != ( k1_funct_1 @ sk_B_1 @ X26 ) )
        | ~ ( r2_hidden @ X26 @ sk_A )
        | ~ ( r2_hidden @ X27 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,
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
   <= ! [X26: $i,X27: $i] :
        ( ( X27 = X26 )
        | ( ( k1_funct_1 @ sk_B_1 @ X27 )
         != ( k1_funct_1 @ sk_B_1 @ X26 ) )
        | ~ ( r2_hidden @ X26 @ sk_A )
        | ~ ( r2_hidden @ X27 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('26',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X26: $i,X27: $i] :
        ( ( X27 = X26 )
        | ( ( k1_funct_1 @ sk_B_1 @ X27 )
         != ( k1_funct_1 @ sk_B_1 @ X26 ) )
        | ~ ( r2_hidden @ X26 @ sk_A )
        | ~ ( r2_hidden @ X27 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X26: $i,X27: $i] :
        ( ( X27 = X26 )
        | ( ( k1_funct_1 @ sk_B_1 @ X27 )
         != ( k1_funct_1 @ sk_B_1 @ X26 ) )
        | ~ ( r2_hidden @ X26 @ sk_A )
        | ~ ( r2_hidden @ X27 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X26: $i,X27: $i] :
        ( ( X27 = X26 )
        | ( ( k1_funct_1 @ sk_B_1 @ X27 )
         != ( k1_funct_1 @ sk_B_1 @ X26 ) )
        | ~ ( r2_hidden @ X26 @ sk_A )
        | ~ ( r2_hidden @ X27 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X26: $i,X27: $i] :
        ( ( X27 = X26 )
        | ( ( k1_funct_1 @ sk_B_1 @ X27 )
         != ( k1_funct_1 @ sk_B_1 @ X26 ) )
        | ~ ( r2_hidden @ X26 @ sk_A )
        | ~ ( r2_hidden @ X27 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_B @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('35',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X26: $i,X27: $i] :
        ( ( X27 = X26 )
        | ( ( k1_funct_1 @ sk_B_1 @ X27 )
         != ( k1_funct_1 @ sk_B_1 @ X26 ) )
        | ~ ( r2_hidden @ X26 @ sk_A )
        | ~ ( r2_hidden @ X27 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X26: $i,X27: $i] :
          ( ( X27 = X26 )
          | ( ( k1_funct_1 @ sk_B_1 @ X27 )
           != ( k1_funct_1 @ sk_B_1 @ X26 ) )
          | ~ ( r2_hidden @ X26 @ sk_A )
          | ~ ( r2_hidden @ X27 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X11: $i] :
      ( ( ( sk_B @ X11 )
       != ( sk_C @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('42',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X26: $i,X27: $i] :
          ( ( X27 = X26 )
          | ( ( k1_funct_1 @ sk_B_1 @ X27 )
           != ( k1_funct_1 @ sk_B_1 @ X26 ) )
          | ~ ( r2_hidden @ X26 @ sk_A )
          | ~ ( r2_hidden @ X27 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('44',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X26: $i,X27: $i] :
          ( ( X27 = X26 )
          | ( ( k1_funct_1 @ sk_B_1 @ X27 )
           != ( k1_funct_1 @ sk_B_1 @ X26 ) )
          | ~ ( r2_hidden @ X26 @ sk_A )
          | ~ ( r2_hidden @ X27 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X26: $i,X27: $i] :
          ( ( X27 = X26 )
          | ( ( k1_funct_1 @ sk_B_1 @ X27 )
           != ( k1_funct_1 @ sk_B_1 @ X26 ) )
          | ~ ( r2_hidden @ X26 @ sk_A )
          | ~ ( r2_hidden @ X27 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('48',plain,
    ( ~ ! [X26: $i,X27: $i] :
          ( ( X27 = X26 )
          | ( ( k1_funct_1 @ sk_B_1 @ X27 )
           != ( k1_funct_1 @ sk_B_1 @ X26 ) )
          | ~ ( r2_hidden @ X26 @ sk_A )
          | ~ ( r2_hidden @ X27 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','48','49'])).

thf('51',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('53',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('54',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','48','53'])).

thf('55',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['52','54'])).

thf('56',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['52','54'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X25 ) @ ( k1_funct_1 @ X25 @ X22 ) )
        = X22 )
      | ~ ( v2_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('61',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','48'])).

thf('62',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','62','63','64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['67'])).

thf('70',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','48','69'])).

thf('71',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','62','63','64'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['78'])).

thf('81',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','48','80'])).

thf('82',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['79','81'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['77','82'])).

thf('84',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','83'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('85',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_funct_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X11 @ X13 ) )
      | ( X12 = X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_C_1 = X1 )
      | ( ( k1_funct_1 @ X0 @ sk_C_1 )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
     != ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','90'])).

thf('92',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['60','61'])).

thf('93',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf('94',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['77','82'])).

thf('95',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('100',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
     != ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['91','92','97','98','99'])).

thf('101',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['79','81'])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T4usrhYeAV
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:09:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 315 iterations in 0.111s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i > $i).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.58  thf(t77_funct_2, conjecture,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.58       ( ( v2_funct_1 @ B ) <=>
% 0.36/0.58         ( ![C:$i,D:$i]:
% 0.36/0.58           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.36/0.58               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.36/0.58             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i,B:$i]:
% 0.36/0.58        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.58            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.58          ( ( v2_funct_1 @ B ) <=>
% 0.36/0.58            ( ![C:$i,D:$i]:
% 0.36/0.58              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.36/0.58                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.36/0.58                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.36/0.58        | ~ (v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.36/0.58         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.36/0.58      inference('split', [status(esa)], ['0'])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (![X26 : $i, X27 : $i]:
% 0.36/0.58         (((X27) = (X26))
% 0.36/0.58          | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58          | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58          | ~ (r2_hidden @ X27 @ sk_A)
% 0.36/0.58          | (v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (((v2_funct_1 @ sk_B_1)) | 
% 0.36/0.58       (![X26 : $i, X27 : $i]:
% 0.36/0.58          (((X27) = (X26))
% 0.36/0.58           | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58           | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58           | ~ (r2_hidden @ X27 @ sk_A)))),
% 0.36/0.58      inference('split', [status(esa)], ['2'])).
% 0.36/0.58  thf(d8_funct_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.58       ( ( v2_funct_1 @ A ) <=>
% 0.36/0.58         ( ![B:$i,C:$i]:
% 0.36/0.58           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.36/0.58               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.36/0.58               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.36/0.58             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (![X11 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_C @ X11) @ (k1_relat_1 @ X11))
% 0.36/0.58          | (v2_funct_1 @ X11)
% 0.36/0.58          | ~ (v1_funct_1 @ X11)
% 0.36/0.58          | ~ (v1_relat_1 @ X11))),
% 0.36/0.58      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(dt_k1_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.58         ((m1_subset_1 @ (k1_relset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X16))
% 0.36/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.36/0.58      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.36/0.58        (k1_zfmisc_1 @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.58         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.36/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['7', '10'])).
% 0.36/0.58  thf(l3_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.58          | (r2_hidden @ X0 @ X2)
% 0.36/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      ((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.58        | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.58        | (v2_funct_1 @ sk_B_1)
% 0.36/0.58        | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['4', '13'])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(cc2_relat_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X7 : $i, X8 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.36/0.58          | (v1_relat_1 @ X7)
% 0.36/0.58          | ~ (v1_relat_1 @ X8))),
% 0.36/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.58  thf('17', plain,
% 0.36/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.58  thf(fc6_relat_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.58  thf('19', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf('20', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['14', '19', '20'])).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      (![X11 : $i]:
% 0.36/0.58         (((k1_funct_1 @ X11 @ (sk_B @ X11))
% 0.36/0.58            = (k1_funct_1 @ X11 @ (sk_C @ X11)))
% 0.36/0.58          | (v2_funct_1 @ X11)
% 0.36/0.58          | ~ (v1_funct_1 @ X11)
% 0.36/0.58          | ~ (v1_relat_1 @ X11))),
% 0.36/0.58      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      ((![X26 : $i, X27 : $i]:
% 0.36/0.58          (((X27) = (X26))
% 0.36/0.58           | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58           | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58           | ~ (r2_hidden @ X27 @ sk_A)))
% 0.36/0.58         <= ((![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('split', [status(esa)], ['2'])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.36/0.58             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.36/0.58           | ~ (v1_relat_1 @ sk_B_1)
% 0.36/0.58           | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.58           | (v2_funct_1 @ sk_B_1)
% 0.36/0.58           | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.58           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.36/0.58           | ((X0) = (sk_C @ sk_B_1))))
% 0.36/0.58         <= ((![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.58  thf('25', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf('26', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.36/0.58             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.36/0.58           | (v2_funct_1 @ sk_B_1)
% 0.36/0.58           | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.58           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.36/0.58           | ((X0) = (sk_C @ sk_B_1))))
% 0.36/0.58         <= ((![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          ((v2_funct_1 @ sk_B_1)
% 0.36/0.58           | ((X0) = (sk_C @ sk_B_1))
% 0.36/0.58           | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.58           | (v2_funct_1 @ sk_B_1)
% 0.36/0.58           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.36/0.58               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.36/0.58         <= ((![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['21', '27'])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.36/0.58             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.36/0.58           | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.58           | ((X0) = (sk_C @ sk_B_1))
% 0.36/0.58           | (v2_funct_1 @ sk_B_1)))
% 0.36/0.58         <= ((![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      ((((v2_funct_1 @ sk_B_1)
% 0.36/0.58         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.36/0.58         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.36/0.58         <= ((![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('eq_res', [status(thm)], ['29'])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      (![X11 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_B @ X11) @ (k1_relat_1 @ X11))
% 0.36/0.58          | (v2_funct_1 @ X11)
% 0.36/0.58          | ~ (v1_funct_1 @ X11)
% 0.36/0.58          | ~ (v1_relat_1 @ X11))),
% 0.36/0.58      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      ((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.58        | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.58        | (v2_funct_1 @ sk_B_1)
% 0.36/0.58        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.58  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf('35', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.36/0.58         <= ((![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('clc', [status(thm)], ['30', '36'])).
% 0.36/0.58  thf('38', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('39', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.36/0.58      inference('split', [status(esa)], ['38'])).
% 0.36/0.58  thf('40', plain,
% 0.36/0.58      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.36/0.58         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.36/0.58             (![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['37', '39'])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      (![X11 : $i]:
% 0.36/0.58         (((sk_B @ X11) != (sk_C @ X11))
% 0.36/0.58          | (v2_funct_1 @ X11)
% 0.36/0.58          | ~ (v1_funct_1 @ X11)
% 0.36/0.58          | ~ (v1_relat_1 @ X11))),
% 0.36/0.58      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.36/0.58         | ~ (v1_relat_1 @ sk_B_1)
% 0.36/0.58         | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.58         | (v2_funct_1 @ sk_B_1)))
% 0.36/0.58         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.36/0.58             (![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.58  thf('43', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf('44', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.36/0.58         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.36/0.58             (![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.36/0.58  thf('46', plain,
% 0.36/0.58      (((v2_funct_1 @ sk_B_1))
% 0.36/0.58         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.36/0.58             (![X26 : $i, X27 : $i]:
% 0.36/0.58                (((X27) = (X26))
% 0.36/0.58                 | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58                 | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58                 | ~ (r2_hidden @ X27 @ sk_A))))),
% 0.36/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.36/0.58  thf('47', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.36/0.58      inference('split', [status(esa)], ['38'])).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      (~
% 0.36/0.58       (![X26 : $i, X27 : $i]:
% 0.36/0.58          (((X27) = (X26))
% 0.36/0.58           | ((k1_funct_1 @ sk_B_1 @ X27) != (k1_funct_1 @ sk_B_1 @ X26))
% 0.36/0.58           | ~ (r2_hidden @ X26 @ sk_A)
% 0.36/0.58           | ~ (r2_hidden @ X27 @ sk_A))) | 
% 0.36/0.58       ((v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.36/0.58       ~ ((v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('split', [status(esa)], ['0'])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['3', '48', '49'])).
% 0.36/0.58  thf('51', plain,
% 0.36/0.58      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.36/0.58  thf('52', plain,
% 0.36/0.58      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.36/0.58      inference('split', [status(esa)], ['38'])).
% 0.36/0.58  thf('53', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('split', [status(esa)], ['38'])).
% 0.36/0.58  thf('54', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['3', '48', '53'])).
% 0.36/0.58  thf('55', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['52', '54'])).
% 0.36/0.58  thf('56', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['52', '54'])).
% 0.36/0.58  thf('57', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t32_funct_2, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.58       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.36/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.58           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.36/0.58             ( C ) ) ) ) ))).
% 0.36/0.58  thf('58', plain,
% 0.36/0.58      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X22 @ X23)
% 0.36/0.58          | ((X24) = (k1_xboole_0))
% 0.36/0.58          | ~ (v1_funct_1 @ X25)
% 0.36/0.58          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.36/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.36/0.58          | ((k1_funct_1 @ (k2_funct_1 @ X25) @ (k1_funct_1 @ X25 @ X22))
% 0.36/0.58              = (X22))
% 0.36/0.58          | ~ (v2_funct_1 @ X25))),
% 0.36/0.58      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.36/0.58  thf('59', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v2_funct_1 @ sk_B_1)
% 0.36/0.58          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.36/0.58              = (X0))
% 0.36/0.58          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.58          | ((sk_A) = (k1_xboole_0))
% 0.36/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.58  thf('60', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.36/0.58      inference('split', [status(esa)], ['2'])).
% 0.36/0.58  thf('61', plain, (((v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['3', '48'])).
% 0.36/0.58  thf('62', plain, ((v2_funct_1 @ sk_B_1)),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['60', '61'])).
% 0.36/0.58  thf('63', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('64', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('65', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.36/0.58            = (X0))
% 0.36/0.58          | ((sk_A) = (k1_xboole_0))
% 0.36/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['59', '62', '63', '64'])).
% 0.36/0.58  thf('66', plain,
% 0.36/0.58      ((((sk_A) = (k1_xboole_0))
% 0.36/0.58        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.36/0.58            = (sk_C_1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['56', '65'])).
% 0.36/0.58  thf('67', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('68', plain,
% 0.36/0.58      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.36/0.58      inference('split', [status(esa)], ['67'])).
% 0.36/0.58  thf('69', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('split', [status(esa)], ['67'])).
% 0.36/0.58  thf('70', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['3', '48', '69'])).
% 0.36/0.58  thf('71', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 0.36/0.58  thf('72', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.36/0.58            = (X0))
% 0.36/0.58          | ((sk_A) = (k1_xboole_0))
% 0.36/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['59', '62', '63', '64'])).
% 0.36/0.58  thf('73', plain,
% 0.36/0.58      ((((sk_A) = (k1_xboole_0))
% 0.36/0.58        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.36/0.58            = (sk_D)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['71', '72'])).
% 0.36/0.58  thf('74', plain,
% 0.36/0.58      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.36/0.58  thf('75', plain,
% 0.36/0.58      ((((sk_A) = (k1_xboole_0))
% 0.36/0.58        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.36/0.58            = (sk_D)))),
% 0.36/0.58      inference('demod', [status(thm)], ['73', '74'])).
% 0.36/0.58  thf('76', plain,
% 0.36/0.58      ((((sk_C_1) = (sk_D))
% 0.36/0.58        | ((sk_A) = (k1_xboole_0))
% 0.36/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['66', '75'])).
% 0.36/0.58  thf('77', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['76'])).
% 0.36/0.58  thf('78', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('79', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.36/0.58      inference('split', [status(esa)], ['78'])).
% 0.36/0.58  thf('80', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.36/0.58      inference('split', [status(esa)], ['78'])).
% 0.36/0.58  thf('81', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['3', '48', '80'])).
% 0.36/0.58  thf('82', plain, (((sk_C_1) != (sk_D))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['79', '81'])).
% 0.36/0.58  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['77', '82'])).
% 0.36/0.58  thf('84', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.36/0.58      inference('demod', [status(thm)], ['55', '83'])).
% 0.36/0.58  thf(t4_subset_1, axiom,
% 0.36/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.58  thf('85', plain,
% 0.36/0.58      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.58  thf('86', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.58          | (r2_hidden @ X0 @ X2)
% 0.36/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.36/0.58  thf('87', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['85', '86'])).
% 0.36/0.58  thf('88', plain, (![X0 : $i]: (r2_hidden @ sk_C_1 @ X0)),
% 0.36/0.58      inference('sup-', [status(thm)], ['84', '87'])).
% 0.36/0.58  thf('89', plain,
% 0.36/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.58         (~ (v2_funct_1 @ X11)
% 0.36/0.58          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.36/0.58          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11))
% 0.36/0.58          | ((k1_funct_1 @ X11 @ X12) != (k1_funct_1 @ X11 @ X13))
% 0.36/0.58          | ((X12) = (X13))
% 0.36/0.58          | ~ (v1_funct_1 @ X11)
% 0.36/0.58          | ~ (v1_relat_1 @ X11))),
% 0.36/0.58      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.36/0.58  thf('90', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ((sk_C_1) = (X1))
% 0.36/0.58          | ((k1_funct_1 @ X0 @ sk_C_1) != (k1_funct_1 @ X0 @ X1))
% 0.36/0.58          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.36/0.58          | ~ (v2_funct_1 @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['88', '89'])).
% 0.36/0.58  thf('91', plain,
% 0.36/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.36/0.58        | ~ (v2_funct_1 @ sk_B_1)
% 0.36/0.58        | ~ (r2_hidden @ sk_D @ (k1_relat_1 @ sk_B_1))
% 0.36/0.58        | ((sk_C_1) = (sk_D))
% 0.36/0.58        | ~ (v1_funct_1 @ sk_B_1)
% 0.36/0.58        | ~ (v1_relat_1 @ sk_B_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['51', '90'])).
% 0.36/0.58  thf('92', plain, ((v2_funct_1 @ sk_B_1)),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['60', '61'])).
% 0.36/0.58  thf('93', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 0.36/0.58  thf('94', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['77', '82'])).
% 0.36/0.58  thf('95', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.36/0.58      inference('demod', [status(thm)], ['93', '94'])).
% 0.36/0.58  thf('96', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['85', '86'])).
% 0.36/0.58  thf('97', plain, (![X0 : $i]: (r2_hidden @ sk_D @ X0)),
% 0.36/0.58      inference('sup-', [status(thm)], ['95', '96'])).
% 0.36/0.58  thf('98', plain, ((v1_funct_1 @ sk_B_1)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('99', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf('100', plain,
% 0.36/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.36/0.58        | ((sk_C_1) = (sk_D)))),
% 0.36/0.58      inference('demod', [status(thm)], ['91', '92', '97', '98', '99'])).
% 0.36/0.58  thf('101', plain, (((sk_C_1) = (sk_D))),
% 0.36/0.58      inference('simplify', [status(thm)], ['100'])).
% 0.36/0.58  thf('102', plain, (((sk_C_1) != (sk_D))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['79', '81'])).
% 0.36/0.58  thf('103', plain, ($false),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
