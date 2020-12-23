%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4uUTAcYa2Q

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:52 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 175 expanded)
%              Number of leaves         :   37 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  824 (1988 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(t47_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                    <=> ? [E: $i] :
                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                          & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_relset_1])).

thf('0',plain,(
    ! [X41: $i] :
      ( ~ ( m1_subset_1 @ X41 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X41 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X41: $i] :
        ( ~ ( m1_subset_1 @ X41 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X41 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X38 )
        = ( k1_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X34: $i] :
      ( ( ( k10_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k10_relat_1 @ X33 @ X31 ) )
      | ( r2_hidden @ ( k4_tarski @ X32 @ ( sk_D_3 @ X33 @ X31 @ X32 ) ) @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_D_4 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ! [X41: $i] :
        ( ~ ( m1_subset_1 @ X41 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X41 ) @ sk_C_1 ) )
   <= ! [X41: $i] :
        ( ~ ( m1_subset_1 @ X41 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X41 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X41: $i] :
          ( ~ ( m1_subset_1 @ X41 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X41 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('22',plain,(
    ! [X34: $i] :
      ( ( ( k10_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('23',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k10_relat_1 @ X33 @ X31 ) )
      | ( r2_hidden @ ( sk_D_3 @ X33 @ X31 @ X32 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('39',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('42',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','48'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('51',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ! [X41: $i] :
          ( ~ ( m1_subset_1 @ X41 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X41 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['20','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('54',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 )
      | ( r2_hidden @ X21 @ X24 )
      | ( X24
       != ( k1_relat_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ ( k1_relat_1 @ X23 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','52','53','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4uUTAcYa2Q
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 249 iterations in 0.098s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.55  thf(sk_D_4_type, type, sk_D_4: $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.55  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.36/0.55  thf(t47_relset_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( m1_subset_1 @ D @ A ) =>
% 0.36/0.55                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.36/0.55                     ( ?[E:$i]:
% 0.36/0.55                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.36/0.55                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55                  ( ![D:$i]:
% 0.36/0.55                    ( ( m1_subset_1 @ D @ A ) =>
% 0.36/0.55                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.36/0.55                        ( ?[E:$i]:
% 0.36/0.55                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.36/0.55                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (![X41 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X41 @ sk_B)
% 0.36/0.55          | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X41) @ sk_C_1)
% 0.36/0.55          | ~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      ((![X41 : $i]:
% 0.36/0.55          (~ (m1_subset_1 @ X41 @ sk_B)
% 0.36/0.55           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X41) @ sk_C_1))) | 
% 0.36/0.55       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.36/0.55      inference('split', [status(esa)], ['0'])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.36/0.55         (((k1_relset_1 @ X39 @ X40 @ X38) = (k1_relat_1 @ X38))
% 0.36/0.55          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)
% 0.36/0.55        | (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('split', [status(esa)], ['5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('sup+', [status(thm)], ['4', '6'])).
% 0.36/0.55  thf(t169_relat_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ A ) =>
% 0.36/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X34 : $i]:
% 0.36/0.55         (((k10_relat_1 @ X34 @ (k2_relat_1 @ X34)) = (k1_relat_1 @ X34))
% 0.36/0.55          | ~ (v1_relat_1 @ X34))),
% 0.36/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.36/0.55  thf(t166_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ C ) =>
% 0.36/0.55       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.36/0.55         ( ?[D:$i]:
% 0.36/0.55           ( ( r2_hidden @ D @ B ) & 
% 0.36/0.55             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.36/0.55             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X32 @ (k10_relat_1 @ X33 @ X31))
% 0.36/0.55          | (r2_hidden @ (k4_tarski @ X32 @ (sk_D_3 @ X33 @ X31 @ X32)) @ X33)
% 0.36/0.55          | ~ (v1_relat_1 @ X33))),
% 0.36/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.36/0.55          | ~ (v1_relat_1 @ X0)
% 0.36/0.55          | ~ (v1_relat_1 @ X0)
% 0.36/0.55          | (r2_hidden @ 
% 0.36/0.55             (k4_tarski @ X1 @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ 
% 0.36/0.55           (k4_tarski @ X1 @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.36/0.55          | ~ (v1_relat_1 @ X0)
% 0.36/0.55          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (((~ (v1_relat_1 @ sk_C_1)
% 0.36/0.55         | (r2_hidden @ 
% 0.36/0.55            (k4_tarski @ sk_D_4 @ 
% 0.36/0.55             (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4)) @ 
% 0.36/0.55            sk_C_1)))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc2_relat_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X17 : $i, X18 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.36/0.55          | (v1_relat_1 @ X17)
% 0.36/0.55          | ~ (v1_relat_1 @ X18))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf(fc6_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.55  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (((r2_hidden @ 
% 0.36/0.55         (k4_tarski @ sk_D_4 @ 
% 0.36/0.55          (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4)) @ 
% 0.36/0.55         sk_C_1))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '17'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      ((![X41 : $i]:
% 0.36/0.55          (~ (m1_subset_1 @ X41 @ sk_B)
% 0.36/0.55           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X41) @ sk_C_1)))
% 0.36/0.55         <= ((![X41 : $i]:
% 0.36/0.55                (~ (m1_subset_1 @ X41 @ sk_B)
% 0.36/0.55                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X41) @ sk_C_1))))),
% 0.36/0.55      inference('split', [status(esa)], ['0'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      ((~ (m1_subset_1 @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.36/0.55           sk_B))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 0.36/0.55             (![X41 : $i]:
% 0.36/0.55                (~ (m1_subset_1 @ X41 @ sk_B)
% 0.36/0.55                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X41) @ sk_C_1))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('sup+', [status(thm)], ['4', '6'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X34 : $i]:
% 0.36/0.55         (((k10_relat_1 @ X34 @ (k2_relat_1 @ X34)) = (k1_relat_1 @ X34))
% 0.36/0.55          | ~ (v1_relat_1 @ X34))),
% 0.36/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X32 @ (k10_relat_1 @ X33 @ X31))
% 0.36/0.55          | (r2_hidden @ (sk_D_3 @ X33 @ X31 @ X32) @ (k2_relat_1 @ X33))
% 0.36/0.55          | ~ (v1_relat_1 @ X33))),
% 0.36/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.36/0.55          | ~ (v1_relat_1 @ X0)
% 0.36/0.55          | ~ (v1_relat_1 @ X0)
% 0.36/0.55          | (r2_hidden @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.36/0.55             (k2_relat_1 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.36/0.55           (k2_relat_1 @ X0))
% 0.36/0.55          | ~ (v1_relat_1 @ X0)
% 0.36/0.55          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (((~ (v1_relat_1 @ sk_C_1)
% 0.36/0.55         | (r2_hidden @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.36/0.55            (k2_relat_1 @ sk_C_1))))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '25'])).
% 0.36/0.55  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (((r2_hidden @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.36/0.55         (k2_relat_1 @ sk_C_1)))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.36/0.55         ((v5_relat_1 @ X35 @ X37)
% 0.36/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.55  thf('31', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf(d19_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ B ) =>
% 0.36/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X19 : $i, X20 : $i]:
% 0.36/0.55         (~ (v5_relat_1 @ X19 @ X20)
% 0.36/0.55          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.36/0.55          | ~ (v1_relat_1 @ X19))),
% 0.36/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.55  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.55  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.36/0.55      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf(t3_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X14 : $i, X16 : $i]:
% 0.36/0.55         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf(dt_k3_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.36/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k2_relat_1 @ sk_C_1)) @ 
% 0.36/0.55        (k1_zfmisc_1 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf(d5_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i]:
% 0.36/0.55         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.36/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_relat_1 @ sk_C_1)))
% 0.36/0.55         = (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_relat_1 @ sk_C_1))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.55  thf(d5_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.36/0.55          | (r2_hidden @ X4 @ X1)
% 0.36/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X0 @ 
% 0.36/0.55             (k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_relat_1 @ sk_C_1))))
% 0.36/0.55          | (r2_hidden @ X0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['41', '43'])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf(involutiveness_k3_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.36/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.36/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_relat_1 @ sk_C_1)))
% 0.36/0.55         = (k2_relat_1 @ sk_C_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)) | (r2_hidden @ X0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['44', '47'])).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      (((r2_hidden @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ sk_B))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '48'])).
% 0.36/0.55  thf(t1_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      (((m1_subset_1 @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.36/0.55         sk_B))
% 0.36/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      (~
% 0.36/0.55       (![X41 : $i]:
% 0.36/0.55          (~ (m1_subset_1 @ X41 @ sk_B)
% 0.36/0.55           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X41) @ sk_C_1))) | 
% 0.36/0.55       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.36/0.55      inference('demod', [status(thm)], ['20', '51'])).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)) | 
% 0.36/0.55       ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.36/0.55      inference('split', [status(esa)], ['5'])).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1))
% 0.36/0.55         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)))),
% 0.36/0.55      inference('split', [status(esa)], ['5'])).
% 0.36/0.55  thf(d4_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.36/0.55       ( ![C:$i]:
% 0.36/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.36/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.36/0.55  thf('55', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.55         (~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23)
% 0.36/0.55          | (r2_hidden @ X21 @ X24)
% 0.36/0.55          | ((X24) != (k1_relat_1 @ X23)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.55         ((r2_hidden @ X21 @ (k1_relat_1 @ X23))
% 0.36/0.55          | ~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23))),
% 0.36/0.55      inference('simplify', [status(thm)], ['55'])).
% 0.36/0.55  thf('57', plain,
% 0.36/0.55      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.36/0.55         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['54', '56'])).
% 0.36/0.55  thf('58', plain,
% 0.36/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      ((~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.36/0.55         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('split', [status(esa)], ['0'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      ((~ (r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.36/0.55         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.55  thf('61', plain,
% 0.36/0.55      (~ ((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)) | 
% 0.36/0.55       ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['57', '60'])).
% 0.36/0.55  thf('62', plain, ($false),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['1', '52', '53', '61'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
