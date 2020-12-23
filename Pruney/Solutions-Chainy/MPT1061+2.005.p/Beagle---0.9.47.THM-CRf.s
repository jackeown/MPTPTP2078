%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:37 EST 2020

% Result     : Theorem 13.78s
% Output     : CNFRefutation 14.15s
% Verified   : 
% Statistics : Number of formulae       :  368 (2293 expanded)
%              Number of leaves         :   50 ( 748 expanded)
%              Depth                    :   17
%              Number of atoms          :  612 (6032 expanded)
%              Number of equality atoms :  178 ( 778 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_146,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_72,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_116,plain,(
    ! [A_72,A_73,B_74] :
      ( v1_relat_1(A_72)
      | ~ r1_tarski(A_72,k2_zfmisc_1(A_73,B_74)) ) ),
    inference(resolution,[status(thm)],[c_20,c_95])).

tff(c_130,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_116])).

tff(c_34311,plain,(
    ! [C_2170,A_2171,B_2172] :
      ( v4_relat_1(C_2170,A_2171)
      | ~ m1_subset_1(C_2170,k1_zfmisc_1(k2_zfmisc_1(A_2171,B_2172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_37218,plain,(
    ! [A_2366,A_2367,B_2368] :
      ( v4_relat_1(A_2366,A_2367)
      | ~ r1_tarski(A_2366,k2_zfmisc_1(A_2367,B_2368)) ) ),
    inference(resolution,[status(thm)],[c_20,c_34311])).

tff(c_37258,plain,(
    ! [A_2369] : v4_relat_1(k1_xboole_0,A_2369) ),
    inference(resolution,[status(thm)],[c_16,c_37218])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_37261,plain,(
    ! [A_2369] :
      ( k7_relat_1(k1_xboole_0,A_2369) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_37258,c_30])).

tff(c_37265,plain,(
    ! [A_2370] : k7_relat_1(k1_xboole_0,A_2370) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_37261])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1218,plain,(
    ! [B_203,A_204] :
      ( B_203 = A_204
      | ~ r1_tarski(B_203,A_204)
      | ~ r1_tarski(A_204,B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_27984,plain,(
    ! [A_1774] :
      ( k1_xboole_0 = A_1774
      | ~ r1_tarski(A_1774,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_1218])).

tff(c_27997,plain,(
    ! [B_24] :
      ( k1_relat_1(k7_relat_1(B_24,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_32,c_27984])).

tff(c_37271,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_37265,c_27997])).

tff(c_37279,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_37271])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_43869,plain,(
    ! [A_2795,B_2796,C_2797,D_2798] :
      ( k2_partfun1(A_2795,B_2796,C_2797,D_2798) = k7_relat_1(C_2797,D_2798)
      | ~ m1_subset_1(C_2797,k1_zfmisc_1(k2_zfmisc_1(A_2795,B_2796)))
      | ~ v1_funct_1(C_2797) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_43880,plain,(
    ! [D_2798] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_2798) = k7_relat_1('#skF_6',D_2798)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_43869])).

tff(c_43886,plain,(
    ! [D_2799] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_2799) = k7_relat_1('#skF_6',D_2799) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_43880])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34153,plain,(
    ! [A_2155,B_2156,C_2157,D_2158] :
      ( k2_partfun1(A_2155,B_2156,C_2157,D_2158) = k7_relat_1(C_2157,D_2158)
      | ~ m1_subset_1(C_2157,k1_zfmisc_1(k2_zfmisc_1(A_2155,B_2156)))
      | ~ v1_funct_1(C_2157) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_34168,plain,(
    ! [D_2158] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_2158) = k7_relat_1('#skF_6',D_2158)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_34153])).

tff(c_34173,plain,(
    ! [D_2158] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_2158) = k7_relat_1('#skF_6',D_2158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_34168])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32460,plain,(
    ! [A_2092,B_2093,C_2094,D_2095] :
      ( k2_partfun1(A_2092,B_2093,C_2094,D_2095) = k7_relat_1(C_2094,D_2095)
      | ~ m1_subset_1(C_2094,k1_zfmisc_1(k2_zfmisc_1(A_2092,B_2093)))
      | ~ v1_funct_1(C_2094) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32475,plain,(
    ! [D_2095] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_2095) = k7_relat_1('#skF_6',D_2095)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_32460])).

tff(c_32480,plain,(
    ! [D_2095] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_2095) = k7_relat_1('#skF_6',D_2095) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_32475])).

tff(c_33718,plain,(
    ! [A_2138,B_2139,C_2140,D_2141] :
      ( m1_subset_1(k2_partfun1(A_2138,B_2139,C_2140,D_2141),k1_zfmisc_1(k2_zfmisc_1(A_2138,B_2139)))
      | ~ m1_subset_1(C_2140,k1_zfmisc_1(k2_zfmisc_1(A_2138,B_2139)))
      | ~ v1_funct_1(C_2140) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_33764,plain,(
    ! [D_2095] :
      ( m1_subset_1(k7_relat_1('#skF_6',D_2095),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5')))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32480,c_33718])).

tff(c_33797,plain,(
    ! [D_2142] : m1_subset_1(k7_relat_1('#skF_6',D_2142),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_33764])).

tff(c_24,plain,(
    ! [B_16,A_14] :
      ( v1_relat_1(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_33826,plain,(
    ! [D_2142] :
      ( v1_relat_1(k7_relat_1('#skF_6',D_2142))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_33797,c_24])).

tff(c_33851,plain,(
    ! [D_2142] : v1_relat_1(k7_relat_1('#skF_6',D_2142)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_33826])).

tff(c_31852,plain,(
    ! [C_2074,A_2075,B_2076] :
      ( m1_subset_1(C_2074,k1_zfmisc_1(k2_zfmisc_1(A_2075,B_2076)))
      | ~ r1_tarski(k2_relat_1(C_2074),B_2076)
      | ~ r1_tarski(k1_relat_1(C_2074),A_2075)
      | ~ v1_relat_1(C_2074) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1155,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( v1_funct_1(k2_partfun1(A_194,B_195,C_196,D_197))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ v1_funct_1(C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1162,plain,(
    ! [D_197] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6',D_197))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_1155])).

tff(c_1166,plain,(
    ! [D_197] : v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6',D_197)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1162])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_157,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_1203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1166,c_157])).

tff(c_1204,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_28002,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1204])).

tff(c_31906,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_31852,c_28002])).

tff(c_32168,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_31906])).

tff(c_32481,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32480,c_32168])).

tff(c_33875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33851,c_32481])).

tff(c_33877,plain,(
    v1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_31906])).

tff(c_34176,plain,(
    v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34173,c_33877])).

tff(c_104,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_95])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_28487,plain,(
    ! [A_1840,B_1841,C_1842] :
      ( k1_relset_1(A_1840,B_1841,C_1842) = k1_relat_1(C_1842)
      | ~ m1_subset_1(C_1842,k1_zfmisc_1(k2_zfmisc_1(A_1840,B_1841))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28496,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_28487])).

tff(c_29538,plain,(
    ! [B_1928,A_1929,C_1930] :
      ( k1_xboole_0 = B_1928
      | k1_relset_1(A_1929,B_1928,C_1930) = A_1929
      | ~ v1_funct_2(C_1930,A_1929,B_1928)
      | ~ m1_subset_1(C_1930,k1_zfmisc_1(k2_zfmisc_1(A_1929,B_1928))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_29554,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_29538])).

tff(c_29560,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_28496,c_29554])).

tff(c_29561,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_29560])).

tff(c_28149,plain,(
    ! [C_1807,A_1808,B_1809] :
      ( v4_relat_1(C_1807,A_1808)
      | ~ m1_subset_1(C_1807,k1_zfmisc_1(k2_zfmisc_1(A_1808,B_1809))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28158,plain,(
    v4_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_28149])).

tff(c_28161,plain,
    ( k7_relat_1('#skF_6','#skF_2') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28158,c_30])).

tff(c_28164,plain,(
    k7_relat_1('#skF_6','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_28161])).

tff(c_28171,plain,
    ( r1_tarski(k1_relat_1('#skF_6'),'#skF_2')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_28164,c_32])).

tff(c_28177,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_28171])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28187,plain,
    ( k1_relat_1('#skF_6') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_28177,c_10])).

tff(c_28197,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_28187])).

tff(c_29563,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29561,c_28197])).

tff(c_29567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_29563])).

tff(c_29568,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_29560])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29599,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29568,c_8])).

tff(c_29601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_29599])).

tff(c_29602,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28187])).

tff(c_29711,plain,(
    ! [B_1943,A_1944] :
      ( k1_relat_1(k7_relat_1(B_1943,A_1944)) = A_1944
      | ~ r1_tarski(A_1944,k1_relat_1(B_1943))
      | ~ v1_relat_1(B_1943) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_29714,plain,(
    ! [A_1944] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_1944)) = A_1944
      | ~ r1_tarski(A_1944,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29602,c_29711])).

tff(c_29735,plain,(
    ! [A_1944] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_1944)) = A_1944
      | ~ r1_tarski(A_1944,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_29714])).

tff(c_30888,plain,(
    ! [B_2043] :
      ( k1_relat_1(k7_relat_1(B_2043,k1_relat_1(B_2043))) = k1_relat_1(B_2043)
      | ~ v1_relat_1(B_2043) ) ),
    inference(resolution,[status(thm)],[c_14,c_29711])).

tff(c_31250,plain,(
    ! [A_2055] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_6',A_2055),A_2055)) = k1_relat_1(k7_relat_1('#skF_6',A_2055))
      | ~ v1_relat_1(k7_relat_1('#skF_6',A_2055))
      | ~ r1_tarski(A_2055,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29735,c_30888])).

tff(c_31287,plain,(
    ! [A_2055] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_6',A_2055)),A_2055)
      | ~ v1_relat_1(k7_relat_1('#skF_6',A_2055))
      | ~ v1_relat_1(k7_relat_1('#skF_6',A_2055))
      | ~ r1_tarski(A_2055,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31250,c_32])).

tff(c_30665,plain,(
    ! [A_2027,B_2028,C_2029,D_2030] :
      ( k7_relset_1(A_2027,B_2028,C_2029,D_2030) = k9_relat_1(C_2029,D_2030)
      | ~ m1_subset_1(C_2029,k1_zfmisc_1(k2_zfmisc_1(A_2027,B_2028))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30675,plain,(
    ! [D_2031] : k7_relset_1('#skF_2','#skF_5','#skF_6',D_2031) = k9_relat_1('#skF_6',D_2031) ),
    inference(resolution,[status(thm)],[c_74,c_30665])).

tff(c_70,plain,(
    r1_tarski(k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_14853,plain,(
    ! [C_995,B_996,A_997] :
      ( ~ v1_xboole_0(C_995)
      | ~ m1_subset_1(B_996,k1_zfmisc_1(C_995))
      | ~ r2_hidden(A_997,B_996) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20798,plain,(
    ! [B_1360,A_1361,A_1362] :
      ( ~ v1_xboole_0(B_1360)
      | ~ r2_hidden(A_1361,A_1362)
      | ~ r1_tarski(A_1362,B_1360) ) ),
    inference(resolution,[status(thm)],[c_20,c_14853])).

tff(c_20802,plain,(
    ! [B_1363,A_1364,B_1365] :
      ( ~ v1_xboole_0(B_1363)
      | ~ r1_tarski(A_1364,B_1363)
      | r1_tarski(A_1364,B_1365) ) ),
    inference(resolution,[status(thm)],[c_6,c_20798])).

tff(c_20817,plain,(
    ! [B_1365] :
      ( ~ v1_xboole_0('#skF_4')
      | r1_tarski(k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3'),B_1365) ) ),
    inference(resolution,[status(thm)],[c_70,c_20802])).

tff(c_20823,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20817])).

tff(c_21751,plain,(
    ! [A_1453,B_1454,C_1455] :
      ( k1_relset_1(A_1453,B_1454,C_1455) = k1_relat_1(C_1455)
      | ~ m1_subset_1(C_1455,k1_zfmisc_1(k2_zfmisc_1(A_1453,B_1454))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_21767,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_21751])).

tff(c_23852,plain,(
    ! [B_1559,A_1560,C_1561] :
      ( k1_xboole_0 = B_1559
      | k1_relset_1(A_1560,B_1559,C_1561) = A_1560
      | ~ v1_funct_2(C_1561,A_1560,B_1559)
      | ~ m1_subset_1(C_1561,k1_zfmisc_1(k2_zfmisc_1(A_1560,B_1559))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_23877,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_23852])).

tff(c_23886,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_21767,c_23877])).

tff(c_23887,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_23886])).

tff(c_20905,plain,(
    ! [C_1376,A_1377,B_1378] :
      ( v4_relat_1(C_1376,A_1377)
      | ~ m1_subset_1(C_1376,k1_zfmisc_1(k2_zfmisc_1(A_1377,B_1378))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20914,plain,(
    v4_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_20905])).

tff(c_20917,plain,
    ( k7_relat_1('#skF_6','#skF_2') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20914,c_30])).

tff(c_20920,plain,(
    k7_relat_1('#skF_6','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_20917])).

tff(c_20924,plain,
    ( r1_tarski(k1_relat_1('#skF_6'),'#skF_2')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_20920,c_32])).

tff(c_20928,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_20924])).

tff(c_20942,plain,
    ( k1_relat_1('#skF_6') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_20928,c_10])).

tff(c_20962,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_20942])).

tff(c_23889,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23887,c_20962])).

tff(c_23893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_23889])).

tff(c_23894,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_23886])).

tff(c_23937,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23894,c_8])).

tff(c_23939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_23937])).

tff(c_23940,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20942])).

tff(c_24362,plain,(
    ! [B_1608,A_1609] :
      ( k1_relat_1(k7_relat_1(B_1608,A_1609)) = A_1609
      | ~ r1_tarski(A_1609,k1_relat_1(B_1608))
      | ~ v1_relat_1(B_1608) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24385,plain,(
    ! [A_1609] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_1609)) = A_1609
      | ~ r1_tarski(A_1609,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23940,c_24362])).

tff(c_24416,plain,(
    ! [A_1609] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_1609)) = A_1609
      | ~ r1_tarski(A_1609,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_24385])).

tff(c_27069,plain,(
    ! [A_1738,B_1739,C_1740,D_1741] :
      ( k2_partfun1(A_1738,B_1739,C_1740,D_1741) = k7_relat_1(C_1740,D_1741)
      | ~ m1_subset_1(C_1740,k1_zfmisc_1(k2_zfmisc_1(A_1738,B_1739)))
      | ~ v1_funct_1(C_1740) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_27086,plain,(
    ! [D_1741] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_1741) = k7_relat_1('#skF_6',D_1741)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_27069])).

tff(c_27094,plain,(
    ! [D_1741] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_1741) = k7_relat_1('#skF_6',D_1741) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_27086])).

tff(c_18695,plain,(
    ! [A_1288,B_1289,C_1290,D_1291] :
      ( k2_partfun1(A_1288,B_1289,C_1290,D_1291) = k7_relat_1(C_1290,D_1291)
      | ~ m1_subset_1(C_1290,k1_zfmisc_1(k2_zfmisc_1(A_1288,B_1289)))
      | ~ v1_funct_1(C_1290) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_18706,plain,(
    ! [D_1291] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_1291) = k7_relat_1('#skF_6',D_1291)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_18695])).

tff(c_18710,plain,(
    ! [D_1291] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_1291) = k7_relat_1('#skF_6',D_1291) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_18706])).

tff(c_20578,plain,(
    ! [A_1355,B_1356,C_1357,D_1358] :
      ( m1_subset_1(k2_partfun1(A_1355,B_1356,C_1357,D_1358),k1_zfmisc_1(k2_zfmisc_1(A_1355,B_1356)))
      | ~ m1_subset_1(C_1357,k1_zfmisc_1(k2_zfmisc_1(A_1355,B_1356)))
      | ~ v1_funct_1(C_1357) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_20627,plain,(
    ! [D_1291] :
      ( m1_subset_1(k7_relat_1('#skF_6',D_1291),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5')))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18710,c_20578])).

tff(c_20657,plain,(
    ! [D_1359] : m1_subset_1(k7_relat_1('#skF_6',D_1359),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_20627])).

tff(c_20686,plain,(
    ! [D_1359] :
      ( v1_relat_1(k7_relat_1('#skF_6',D_1359))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_20657,c_24])).

tff(c_20711,plain,(
    ! [D_1359] : v1_relat_1(k7_relat_1('#skF_6',D_1359)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20686])).

tff(c_18992,plain,(
    ! [C_1300,A_1301,B_1302] :
      ( m1_subset_1(C_1300,k1_zfmisc_1(k2_zfmisc_1(A_1301,B_1302)))
      | ~ r1_tarski(k2_relat_1(C_1300),B_1302)
      | ~ r1_tarski(k1_relat_1(C_1300),A_1301)
      | ~ v1_relat_1(C_1300) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14861,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1204])).

tff(c_18714,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18710,c_14861])).

tff(c_19045,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18992,c_18714])).

tff(c_19243,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_19045])).

tff(c_20735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20711,c_19243])).

tff(c_20737,plain,(
    v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_19045])).

tff(c_15225,plain,(
    ! [A_1050,B_1051,C_1052] :
      ( k1_relset_1(A_1050,B_1051,C_1052) = k1_relat_1(C_1052)
      | ~ m1_subset_1(C_1052,k1_zfmisc_1(k2_zfmisc_1(A_1050,B_1051))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15234,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_15225])).

tff(c_16409,plain,(
    ! [B_1149,A_1150,C_1151] :
      ( k1_xboole_0 = B_1149
      | k1_relset_1(A_1150,B_1149,C_1151) = A_1150
      | ~ v1_funct_2(C_1151,A_1150,B_1149)
      | ~ m1_subset_1(C_1151,k1_zfmisc_1(k2_zfmisc_1(A_1150,B_1149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_16425,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_16409])).

tff(c_16431,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_15234,c_16425])).

tff(c_16432,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16431])).

tff(c_15020,plain,(
    ! [C_1030,A_1031,B_1032] :
      ( v4_relat_1(C_1030,A_1031)
      | ~ m1_subset_1(C_1030,k1_zfmisc_1(k2_zfmisc_1(A_1031,B_1032))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_15029,plain,(
    v4_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_15020])).

tff(c_15042,plain,
    ( k7_relat_1('#skF_6','#skF_2') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_15029,c_30])).

tff(c_15045,plain,(
    k7_relat_1('#skF_6','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_15042])).

tff(c_15052,plain,
    ( r1_tarski(k1_relat_1('#skF_6'),'#skF_2')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_15045,c_32])).

tff(c_15058,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_15052])).

tff(c_15072,plain,
    ( k1_relat_1('#skF_6') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_15058,c_10])).

tff(c_15082,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_15072])).

tff(c_16434,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16432,c_15082])).

tff(c_16438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16434])).

tff(c_16439,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_16431])).

tff(c_16470,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16439,c_8])).

tff(c_16472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_16470])).

tff(c_16473,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_15072])).

tff(c_16519,plain,(
    ! [B_1156,A_1157] :
      ( k1_relat_1(k7_relat_1(B_1156,A_1157)) = A_1157
      | ~ r1_tarski(A_1157,k1_relat_1(B_1156))
      | ~ v1_relat_1(B_1156) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16522,plain,(
    ! [A_1157] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_1157)) = A_1157
      | ~ r1_tarski(A_1157,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16473,c_16519])).

tff(c_16543,plain,(
    ! [A_1157] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_1157)) = A_1157
      | ~ r1_tarski(A_1157,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_16522])).

tff(c_17731,plain,(
    ! [B_1257] :
      ( k1_relat_1(k7_relat_1(B_1257,k1_relat_1(B_1257))) = k1_relat_1(B_1257)
      | ~ v1_relat_1(B_1257) ) ),
    inference(resolution,[status(thm)],[c_14,c_16519])).

tff(c_18093,plain,(
    ! [A_1269] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_6',A_1269),A_1269)) = k1_relat_1(k7_relat_1('#skF_6',A_1269))
      | ~ v1_relat_1(k7_relat_1('#skF_6',A_1269))
      | ~ r1_tarski(A_1269,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16543,c_17731])).

tff(c_18130,plain,(
    ! [A_1269] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_6',A_1269)),A_1269)
      | ~ v1_relat_1(k7_relat_1('#skF_6',A_1269))
      | ~ v1_relat_1(k7_relat_1('#skF_6',A_1269))
      | ~ r1_tarski(A_1269,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18093,c_32])).

tff(c_17686,plain,(
    ! [A_1252,B_1253,C_1254,D_1255] :
      ( k7_relset_1(A_1252,B_1253,C_1254,D_1255) = k9_relat_1(C_1254,D_1255)
      | ~ m1_subset_1(C_1254,k1_zfmisc_1(k2_zfmisc_1(A_1252,B_1253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17697,plain,(
    ! [D_1255] : k7_relset_1('#skF_2','#skF_5','#skF_6',D_1255) = k9_relat_1('#skF_6',D_1255) ),
    inference(resolution,[status(thm)],[c_74,c_17686])).

tff(c_17700,plain,(
    r1_tarski(k9_relat_1('#skF_6','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17697,c_70])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20736,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_19045])).

tff(c_20738,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20736])).

tff(c_20744,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_6','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_20738])).

tff(c_20748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_17700,c_20744])).

tff(c_20749,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_20736])).

tff(c_20779,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18130,c_20749])).

tff(c_20795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20737,c_20779])).

tff(c_20797,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1204])).

tff(c_24632,plain,(
    ! [A_1629,B_1630,C_1631] :
      ( k1_relset_1(A_1629,B_1630,C_1631) = k1_relat_1(C_1631)
      | ~ m1_subset_1(C_1631,k1_zfmisc_1(k2_zfmisc_1(A_1629,B_1630))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24643,plain,(
    k1_relset_1('#skF_3','#skF_4',k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) = k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20797,c_24632])).

tff(c_27283,plain,(
    k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) = k1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27094,c_27094,c_24643])).

tff(c_20796,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1204])).

tff(c_27289,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27094,c_20796])).

tff(c_27288,plain,(
    m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27094,c_20797])).

tff(c_27558,plain,(
    ! [B_1755,C_1756,A_1757] :
      ( k1_xboole_0 = B_1755
      | v1_funct_2(C_1756,A_1757,B_1755)
      | k1_relset_1(A_1757,B_1755,C_1756) != A_1757
      | ~ m1_subset_1(C_1756,k1_zfmisc_1(k2_zfmisc_1(A_1757,B_1755))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_27561,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_27288,c_27558])).

tff(c_27586,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_27289,c_27561])).

tff(c_27725,plain,(
    k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_27586])).

tff(c_27874,plain,(
    k1_relat_1(k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27283,c_27725])).

tff(c_27887,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24416,c_27874])).

tff(c_27896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_27887])).

tff(c_27897,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_27586])).

tff(c_27942,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27897,c_8])).

tff(c_27945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20823,c_27942])).

tff(c_27947,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_20817])).

tff(c_27948,plain,(
    ! [B_1770,B_1771] :
      ( ~ v1_xboole_0(B_1770)
      | r1_tarski(B_1770,B_1771) ) ),
    inference(resolution,[status(thm)],[c_14,c_20802])).

tff(c_1233,plain,
    ( k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4',k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_1218])).

tff(c_14814,plain,(
    ~ r1_tarski('#skF_4',k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1233])).

tff(c_27953,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_27948,c_14814])).

tff(c_27974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27947,c_27953])).

tff(c_27975,plain,(
    k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1233])).

tff(c_30681,plain,(
    k9_relat_1('#skF_6','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_30675,c_27975])).

tff(c_34069,plain,(
    ! [A_2149,B_2150,C_2151,D_2152] :
      ( k2_partfun1(A_2149,B_2150,C_2151,D_2152) = k7_relat_1(C_2151,D_2152)
      | ~ m1_subset_1(C_2151,k1_zfmisc_1(k2_zfmisc_1(A_2149,B_2150)))
      | ~ v1_funct_1(C_2151) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_34084,plain,(
    ! [D_2152] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_2152) = k7_relat_1('#skF_6',D_2152)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_34069])).

tff(c_34089,plain,(
    ! [D_2152] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_2152) = k7_relat_1('#skF_6',D_2152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_34084])).

tff(c_33876,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_31906])).

tff(c_33878,plain,(
    ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_33876])).

tff(c_34091,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34089,c_33878])).

tff(c_34130,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_6','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_34091])).

tff(c_34134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_14,c_30681,c_34130])).

tff(c_34136,plain,(
    r1_tarski(k2_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_33876])).

tff(c_34175,plain,(
    r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34173,c_34136])).

tff(c_48,plain,(
    ! [C_46,A_44,B_45] :
      ( m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ r1_tarski(k2_relat_1(C_46),B_45)
      | ~ r1_tarski(k1_relat_1(C_46),A_44)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34180,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34173,c_28002])).

tff(c_34256,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_34180])).

tff(c_34262,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34176,c_34175,c_34256])).

tff(c_34266,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_31287,c_34262])).

tff(c_34282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34176,c_34266])).

tff(c_34284,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1204])).

tff(c_37443,plain,(
    ! [C_2397,B_2398,A_2399] :
      ( v1_xboole_0(C_2397)
      | ~ m1_subset_1(C_2397,k1_zfmisc_1(k2_zfmisc_1(B_2398,A_2399)))
      | ~ v1_xboole_0(A_2399) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_37454,plain,
    ( v1_xboole_0(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34284,c_37443])).

tff(c_37492,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_37454])).

tff(c_40973,plain,(
    ! [A_2577,B_2578,C_2579,D_2580] :
      ( k2_partfun1(A_2577,B_2578,C_2579,D_2580) = k7_relat_1(C_2579,D_2580)
      | ~ m1_subset_1(C_2579,k1_zfmisc_1(k2_zfmisc_1(A_2577,B_2578)))
      | ~ v1_funct_1(C_2579) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40990,plain,(
    ! [D_2580] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_2580) = k7_relat_1('#skF_6',D_2580)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_40973])).

tff(c_40998,plain,(
    ! [D_2580] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_2580) = k7_relat_1('#skF_6',D_2580) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_40990])).

tff(c_34283,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1204])).

tff(c_41012,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40998,c_34283])).

tff(c_35077,plain,(
    ! [A_2258,B_2259,C_2260] :
      ( k1_relset_1(A_2258,B_2259,C_2260) = k1_relat_1(C_2260)
      | ~ m1_subset_1(C_2260,k1_zfmisc_1(k2_zfmisc_1(A_2258,B_2259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_35090,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_35077])).

tff(c_37091,plain,(
    ! [B_2360,A_2361,C_2362] :
      ( k1_xboole_0 = B_2360
      | k1_relset_1(A_2361,B_2360,C_2362) = A_2361
      | ~ v1_funct_2(C_2362,A_2361,B_2360)
      | ~ m1_subset_1(C_2362,k1_zfmisc_1(k2_zfmisc_1(A_2361,B_2360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_37113,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_37091])).

tff(c_37119,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_35090,c_37113])).

tff(c_37120,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_37119])).

tff(c_34320,plain,(
    v4_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_34311])).

tff(c_34323,plain,
    ( k7_relat_1('#skF_6','#skF_2') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34320,c_30])).

tff(c_34326,plain,(
    k7_relat_1('#skF_6','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_34323])).

tff(c_34330,plain,
    ( r1_tarski(k1_relat_1('#skF_6'),'#skF_2')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_34326,c_32])).

tff(c_34334,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_34330])).

tff(c_34342,plain,
    ( k1_relat_1('#skF_6') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_34334,c_10])).

tff(c_34344,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_34342])).

tff(c_37122,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37120,c_34344])).

tff(c_37126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_37122])).

tff(c_37127,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_37119])).

tff(c_37167,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37127,c_8])).

tff(c_37169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_37167])).

tff(c_37170,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34342])).

tff(c_37569,plain,(
    ! [B_2411,A_2412] :
      ( k1_relat_1(k7_relat_1(B_2411,A_2412)) = A_2412
      | ~ r1_tarski(A_2412,k1_relat_1(B_2411))
      | ~ v1_relat_1(B_2411) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_37586,plain,(
    ! [A_2412] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_2412)) = A_2412
      | ~ r1_tarski(A_2412,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37170,c_37569])).

tff(c_37609,plain,(
    ! [A_2412] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_2412)) = A_2412
      | ~ r1_tarski(A_2412,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_37586])).

tff(c_40302,plain,(
    ! [A_2552,B_2553,C_2554,D_2555] :
      ( k2_partfun1(A_2552,B_2553,C_2554,D_2555) = k7_relat_1(C_2554,D_2555)
      | ~ m1_subset_1(C_2554,k1_zfmisc_1(k2_zfmisc_1(A_2552,B_2553)))
      | ~ v1_funct_1(C_2554) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40319,plain,(
    ! [D_2555] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_2555) = k7_relat_1('#skF_6',D_2555)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_40302])).

tff(c_40327,plain,(
    ! [D_2555] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_2555) = k7_relat_1('#skF_6',D_2555) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_40319])).

tff(c_37177,plain,
    ( v1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34284,c_24])).

tff(c_37187,plain,(
    v1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_37177])).

tff(c_40,plain,(
    ! [C_32,A_30,B_31] :
      ( v4_relat_1(C_32,A_30)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_37184,plain,(
    v4_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_34284,c_40])).

tff(c_37200,plain,
    ( k7_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3') = k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_37184,c_30])).

tff(c_37203,plain,(
    k7_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3') = k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37187,c_37200])).

tff(c_37856,plain,
    ( r1_tarski(k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37203,c_32])).

tff(c_37862,plain,(
    r1_tarski(k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37187,c_37856])).

tff(c_37876,plain,
    ( k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_37862,c_10])).

tff(c_39380,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_37876])).

tff(c_40328,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k7_relat_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40327,c_39380])).

tff(c_40399,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_37609,c_40328])).

tff(c_40409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14,c_40399])).

tff(c_40410,plain,(
    k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_37876])).

tff(c_38019,plain,(
    ! [A_2448,B_2449,C_2450] :
      ( k1_relset_1(A_2448,B_2449,C_2450) = k1_relat_1(C_2450)
      | ~ m1_subset_1(C_2450,k1_zfmisc_1(k2_zfmisc_1(A_2448,B_2449))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38030,plain,(
    k1_relset_1('#skF_3','#skF_4',k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) = k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34284,c_38019])).

tff(c_40412,plain,(
    k1_relset_1('#skF_3','#skF_4',k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40410,c_38030])).

tff(c_40999,plain,(
    k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40998,c_40412])).

tff(c_41011,plain,(
    m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40998,c_34284])).

tff(c_56,plain,(
    ! [B_48,C_49,A_47] :
      ( k1_xboole_0 = B_48
      | v1_funct_2(C_49,A_47,B_48)
      | k1_relset_1(A_47,B_48,C_49) != A_47
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_41228,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_41011,c_56])).

tff(c_41260,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40999,c_41228])).

tff(c_41261,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_41012,c_41260])).

tff(c_41322,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41261,c_8])).

tff(c_41325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37492,c_41322])).

tff(c_41327,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_37454])).

tff(c_42057,plain,(
    ! [A_2652,A_2653,B_2654] :
      ( v1_xboole_0(A_2652)
      | ~ v1_xboole_0(A_2653)
      | ~ r1_tarski(A_2652,k2_zfmisc_1(B_2654,A_2653)) ) ),
    inference(resolution,[status(thm)],[c_20,c_37443])).

tff(c_42093,plain,(
    ! [B_2655,A_2656] :
      ( v1_xboole_0(k2_zfmisc_1(B_2655,A_2656))
      | ~ v1_xboole_0(A_2656) ) ),
    inference(resolution,[status(thm)],[c_14,c_42057])).

tff(c_37295,plain,(
    ! [C_2373,B_2374,A_2375] :
      ( ~ v1_xboole_0(C_2373)
      | ~ m1_subset_1(B_2374,k1_zfmisc_1(C_2373))
      | ~ r2_hidden(A_2375,B_2374) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_37335,plain,(
    ! [B_2382,A_2383,A_2384] :
      ( ~ v1_xboole_0(B_2382)
      | ~ r2_hidden(A_2383,A_2384)
      | ~ r1_tarski(A_2384,B_2382) ) ),
    inference(resolution,[status(thm)],[c_20,c_37295])).

tff(c_37339,plain,(
    ! [B_2385,A_2386,B_2387] :
      ( ~ v1_xboole_0(B_2385)
      | ~ r1_tarski(A_2386,B_2385)
      | r1_tarski(A_2386,B_2387) ) ),
    inference(resolution,[status(thm)],[c_6,c_37335])).

tff(c_37379,plain,(
    ! [B_2390,B_2391] :
      ( ~ v1_xboole_0(B_2390)
      | r1_tarski(B_2390,B_2391) ) ),
    inference(resolution,[status(thm)],[c_14,c_37339])).

tff(c_1235,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_1218])).

tff(c_37413,plain,(
    ! [B_2390] :
      ( k1_xboole_0 = B_2390
      | ~ v1_xboole_0(B_2390) ) ),
    inference(resolution,[status(thm)],[c_37379,c_1235])).

tff(c_41336,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_41327,c_37413])).

tff(c_41346,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41336,c_16])).

tff(c_50,plain,(
    ! [A_47] :
      ( v1_funct_2(k1_xboole_0,A_47,k1_xboole_0)
      | k1_xboole_0 = A_47
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_47,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_41496,plain,(
    ! [A_2596] :
      ( v1_funct_2('#skF_4',A_2596,'#skF_4')
      | A_2596 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_2596,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41336,c_41336,c_41336,c_41336,c_41336,c_50])).

tff(c_41499,plain,(
    ! [A_2596] :
      ( v1_funct_2('#skF_4',A_2596,'#skF_4')
      | A_2596 = '#skF_4'
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_2596,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_20,c_41496])).

tff(c_41528,plain,(
    ! [A_2599] :
      ( v1_funct_2('#skF_4',A_2599,'#skF_4')
      | A_2599 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41346,c_41499])).

tff(c_41326,plain,(
    v1_xboole_0(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_37454])).

tff(c_41338,plain,(
    ! [B_2390] :
      ( B_2390 = '#skF_4'
      | ~ v1_xboole_0(B_2390) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41336,c_37413])).

tff(c_41444,plain,(
    k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_41326,c_41338])).

tff(c_41517,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41444,c_34283])).

tff(c_41532,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_41528,c_41517])).

tff(c_37302,plain,(
    ! [A_2375] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_2375,k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34284,c_37295])).

tff(c_37332,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_37302])).

tff(c_41535,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41532,c_37332])).

tff(c_42098,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42093,c_41535])).

tff(c_42116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41327,c_42098])).

tff(c_42140,plain,(
    ! [A_2662] : ~ r2_hidden(A_2662,k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_37302])).

tff(c_42158,plain,(
    ! [B_2664] : r1_tarski(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),B_2664) ),
    inference(resolution,[status(thm)],[c_6,c_42140])).

tff(c_42182,plain,(
    k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42158,c_1235])).

tff(c_43892,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_43886,c_42182])).

tff(c_42282,plain,(
    ! [B_2675,A_2676] :
      ( k1_relat_1(k7_relat_1(B_2675,A_2676)) = A_2676
      | ~ r1_tarski(A_2676,k1_relat_1(B_2675))
      | ~ v1_relat_1(B_2675) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42288,plain,(
    ! [A_2676] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_2676)) = A_2676
      | ~ r1_tarski(A_2676,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37170,c_42282])).

tff(c_42307,plain,(
    ! [A_2676] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_2676)) = A_2676
      | ~ r1_tarski(A_2676,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_42288])).

tff(c_43916,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_43892,c_42307])).

tff(c_43931,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_37279,c_43916])).

tff(c_43975,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43931,c_43931,c_37279])).

tff(c_43981,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43931,c_16])).

tff(c_42453,plain,(
    ! [A_2686,B_2687,C_2688] :
      ( k1_relset_1(A_2686,B_2687,C_2688) = k1_relat_1(C_2688)
      | ~ m1_subset_1(C_2688,k1_zfmisc_1(k2_zfmisc_1(A_2686,B_2687))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44951,plain,(
    ! [A_2835,B_2836,A_2837] :
      ( k1_relset_1(A_2835,B_2836,A_2837) = k1_relat_1(A_2837)
      | ~ r1_tarski(A_2837,k2_zfmisc_1(A_2835,B_2836)) ) ),
    inference(resolution,[status(thm)],[c_20,c_42453])).

tff(c_44961,plain,(
    ! [A_2835,B_2836] : k1_relset_1(A_2835,B_2836,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_43981,c_44951])).

tff(c_44986,plain,(
    ! [A_2835,B_2836] : k1_relset_1(A_2835,B_2836,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43975,c_44961])).

tff(c_43415,plain,(
    ! [C_2775,B_2776] :
      ( v1_funct_2(C_2775,k1_xboole_0,B_2776)
      | k1_relset_1(k1_xboole_0,B_2776,C_2775) != k1_xboole_0
      | ~ m1_subset_1(C_2775,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2776))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_43424,plain,(
    ! [A_9,B_2776] :
      ( v1_funct_2(A_9,k1_xboole_0,B_2776)
      | k1_relset_1(k1_xboole_0,B_2776,A_9) != k1_xboole_0
      | ~ r1_tarski(A_9,k2_zfmisc_1(k1_xboole_0,B_2776)) ) ),
    inference(resolution,[status(thm)],[c_20,c_43415])).

tff(c_46653,plain,(
    ! [A_2934,B_2935] :
      ( v1_funct_2(A_2934,'#skF_3',B_2935)
      | k1_relset_1('#skF_3',B_2935,A_2934) != '#skF_3'
      | ~ r1_tarski(A_2934,k2_zfmisc_1('#skF_3',B_2935)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43931,c_43931,c_43931,c_43931,c_43424])).

tff(c_46672,plain,(
    ! [B_2935] :
      ( v1_funct_2('#skF_3','#skF_3',B_2935)
      | k1_relset_1('#skF_3',B_2935,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_43981,c_46653])).

tff(c_46696,plain,(
    ! [B_2935] : v1_funct_2('#skF_3','#skF_3',B_2935) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44986,c_46672])).

tff(c_42194,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42182,c_34283])).

tff(c_43969,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43931,c_42194])).

tff(c_46704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46696,c_43969])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 14:35:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.78/5.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.78/5.75  
% 13.78/5.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.78/5.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 13.78/5.75  
% 13.78/5.75  %Foreground sorts:
% 13.78/5.75  
% 13.78/5.75  
% 13.78/5.75  %Background operators:
% 13.78/5.75  
% 13.78/5.75  
% 13.78/5.75  %Foreground operators:
% 13.78/5.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.78/5.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.78/5.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.78/5.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.78/5.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.78/5.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.78/5.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.78/5.75  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.78/5.75  tff('#skF_5', type, '#skF_5': $i).
% 13.78/5.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.78/5.75  tff('#skF_6', type, '#skF_6': $i).
% 13.78/5.75  tff('#skF_2', type, '#skF_2': $i).
% 13.78/5.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.78/5.75  tff('#skF_3', type, '#skF_3': $i).
% 13.78/5.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.78/5.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.78/5.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.78/5.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.78/5.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.78/5.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.78/5.75  tff('#skF_4', type, '#skF_4': $i).
% 13.78/5.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.78/5.75  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.78/5.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.78/5.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.78/5.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.78/5.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.78/5.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.78/5.75  
% 14.15/5.79  tff(f_167, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 14.15/5.79  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.15/5.79  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.15/5.79  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.15/5.79  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.15/5.79  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 14.15/5.79  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 14.15/5.79  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.15/5.79  tff(f_146, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 14.15/5.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.15/5.79  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.15/5.79  tff(f_140, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 14.15/5.79  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 14.15/5.79  tff(f_114, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 14.15/5.79  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.15/5.79  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 14.15/5.79  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.15/5.79  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 14.15/5.79  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 14.15/5.79  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 14.15/5.79  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 14.15/5.79  tff(f_98, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 14.15/5.79  tff(c_72, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.15/5.79  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.15/5.79  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.15/5.79  tff(c_95, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.15/5.79  tff(c_116, plain, (![A_72, A_73, B_74]: (v1_relat_1(A_72) | ~r1_tarski(A_72, k2_zfmisc_1(A_73, B_74)))), inference(resolution, [status(thm)], [c_20, c_95])).
% 14.15/5.79  tff(c_130, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_116])).
% 14.15/5.79  tff(c_34311, plain, (![C_2170, A_2171, B_2172]: (v4_relat_1(C_2170, A_2171) | ~m1_subset_1(C_2170, k1_zfmisc_1(k2_zfmisc_1(A_2171, B_2172))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.15/5.79  tff(c_37218, plain, (![A_2366, A_2367, B_2368]: (v4_relat_1(A_2366, A_2367) | ~r1_tarski(A_2366, k2_zfmisc_1(A_2367, B_2368)))), inference(resolution, [status(thm)], [c_20, c_34311])).
% 14.15/5.79  tff(c_37258, plain, (![A_2369]: (v4_relat_1(k1_xboole_0, A_2369))), inference(resolution, [status(thm)], [c_16, c_37218])).
% 14.15/5.79  tff(c_30, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.15/5.79  tff(c_37261, plain, (![A_2369]: (k7_relat_1(k1_xboole_0, A_2369)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_37258, c_30])).
% 14.15/5.79  tff(c_37265, plain, (![A_2370]: (k7_relat_1(k1_xboole_0, A_2370)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_37261])).
% 14.15/5.79  tff(c_32, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.15/5.79  tff(c_1218, plain, (![B_203, A_204]: (B_203=A_204 | ~r1_tarski(B_203, A_204) | ~r1_tarski(A_204, B_203))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.15/5.79  tff(c_27984, plain, (![A_1774]: (k1_xboole_0=A_1774 | ~r1_tarski(A_1774, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_1218])).
% 14.15/5.79  tff(c_27997, plain, (![B_24]: (k1_relat_1(k7_relat_1(B_24, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_32, c_27984])).
% 14.15/5.79  tff(c_37271, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_37265, c_27997])).
% 14.15/5.79  tff(c_37279, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_130, c_37271])).
% 14.15/5.79  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.15/5.79  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.15/5.79  tff(c_43869, plain, (![A_2795, B_2796, C_2797, D_2798]: (k2_partfun1(A_2795, B_2796, C_2797, D_2798)=k7_relat_1(C_2797, D_2798) | ~m1_subset_1(C_2797, k1_zfmisc_1(k2_zfmisc_1(A_2795, B_2796))) | ~v1_funct_1(C_2797))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.15/5.79  tff(c_43880, plain, (![D_2798]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2798)=k7_relat_1('#skF_6', D_2798) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_43869])).
% 14.15/5.79  tff(c_43886, plain, (![D_2799]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2799)=k7_relat_1('#skF_6', D_2799))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_43880])).
% 14.15/5.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.15/5.79  tff(c_34153, plain, (![A_2155, B_2156, C_2157, D_2158]: (k2_partfun1(A_2155, B_2156, C_2157, D_2158)=k7_relat_1(C_2157, D_2158) | ~m1_subset_1(C_2157, k1_zfmisc_1(k2_zfmisc_1(A_2155, B_2156))) | ~v1_funct_1(C_2157))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.15/5.79  tff(c_34168, plain, (![D_2158]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2158)=k7_relat_1('#skF_6', D_2158) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_34153])).
% 14.15/5.79  tff(c_34173, plain, (![D_2158]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2158)=k7_relat_1('#skF_6', D_2158))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_34168])).
% 14.15/5.79  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.15/5.79  tff(c_32460, plain, (![A_2092, B_2093, C_2094, D_2095]: (k2_partfun1(A_2092, B_2093, C_2094, D_2095)=k7_relat_1(C_2094, D_2095) | ~m1_subset_1(C_2094, k1_zfmisc_1(k2_zfmisc_1(A_2092, B_2093))) | ~v1_funct_1(C_2094))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.15/5.79  tff(c_32475, plain, (![D_2095]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2095)=k7_relat_1('#skF_6', D_2095) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_32460])).
% 14.15/5.79  tff(c_32480, plain, (![D_2095]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2095)=k7_relat_1('#skF_6', D_2095))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_32475])).
% 14.15/5.79  tff(c_33718, plain, (![A_2138, B_2139, C_2140, D_2141]: (m1_subset_1(k2_partfun1(A_2138, B_2139, C_2140, D_2141), k1_zfmisc_1(k2_zfmisc_1(A_2138, B_2139))) | ~m1_subset_1(C_2140, k1_zfmisc_1(k2_zfmisc_1(A_2138, B_2139))) | ~v1_funct_1(C_2140))), inference(cnfTransformation, [status(thm)], [f_140])).
% 14.15/5.79  tff(c_33764, plain, (![D_2095]: (m1_subset_1(k7_relat_1('#skF_6', D_2095), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32480, c_33718])).
% 14.15/5.79  tff(c_33797, plain, (![D_2142]: (m1_subset_1(k7_relat_1('#skF_6', D_2142), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_33764])).
% 14.15/5.79  tff(c_24, plain, (![B_16, A_14]: (v1_relat_1(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.15/5.79  tff(c_33826, plain, (![D_2142]: (v1_relat_1(k7_relat_1('#skF_6', D_2142)) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_5')))), inference(resolution, [status(thm)], [c_33797, c_24])).
% 14.15/5.79  tff(c_33851, plain, (![D_2142]: (v1_relat_1(k7_relat_1('#skF_6', D_2142)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_33826])).
% 14.15/5.79  tff(c_31852, plain, (![C_2074, A_2075, B_2076]: (m1_subset_1(C_2074, k1_zfmisc_1(k2_zfmisc_1(A_2075, B_2076))) | ~r1_tarski(k2_relat_1(C_2074), B_2076) | ~r1_tarski(k1_relat_1(C_2074), A_2075) | ~v1_relat_1(C_2074))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.15/5.79  tff(c_1155, plain, (![A_194, B_195, C_196, D_197]: (v1_funct_1(k2_partfun1(A_194, B_195, C_196, D_197)) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | ~v1_funct_1(C_196))), inference(cnfTransformation, [status(thm)], [f_140])).
% 14.15/5.79  tff(c_1162, plain, (![D_197]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_197)) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_1155])).
% 14.15/5.79  tff(c_1166, plain, (![D_197]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_197)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1162])).
% 14.15/5.79  tff(c_68, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.15/5.79  tff(c_157, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_68])).
% 14.15/5.79  tff(c_1203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1166, c_157])).
% 14.15/5.79  tff(c_1204, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_68])).
% 14.15/5.79  tff(c_28002, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1204])).
% 14.15/5.79  tff(c_31906, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_31852, c_28002])).
% 14.15/5.79  tff(c_32168, plain, (~v1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_31906])).
% 14.15/5.79  tff(c_32481, plain, (~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32480, c_32168])).
% 14.15/5.79  tff(c_33875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33851, c_32481])).
% 14.15/5.79  tff(c_33877, plain, (v1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitRight, [status(thm)], [c_31906])).
% 14.15/5.79  tff(c_34176, plain, (v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34173, c_33877])).
% 14.15/5.79  tff(c_104, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_95])).
% 14.15/5.79  tff(c_80, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.15/5.79  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.15/5.79  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.15/5.79  tff(c_28487, plain, (![A_1840, B_1841, C_1842]: (k1_relset_1(A_1840, B_1841, C_1842)=k1_relat_1(C_1842) | ~m1_subset_1(C_1842, k1_zfmisc_1(k2_zfmisc_1(A_1840, B_1841))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.15/5.79  tff(c_28496, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_28487])).
% 14.15/5.79  tff(c_29538, plain, (![B_1928, A_1929, C_1930]: (k1_xboole_0=B_1928 | k1_relset_1(A_1929, B_1928, C_1930)=A_1929 | ~v1_funct_2(C_1930, A_1929, B_1928) | ~m1_subset_1(C_1930, k1_zfmisc_1(k2_zfmisc_1(A_1929, B_1928))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.15/5.79  tff(c_29554, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_29538])).
% 14.15/5.79  tff(c_29560, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_28496, c_29554])).
% 14.15/5.79  tff(c_29561, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_29560])).
% 14.15/5.79  tff(c_28149, plain, (![C_1807, A_1808, B_1809]: (v4_relat_1(C_1807, A_1808) | ~m1_subset_1(C_1807, k1_zfmisc_1(k2_zfmisc_1(A_1808, B_1809))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.15/5.79  tff(c_28158, plain, (v4_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_28149])).
% 14.15/5.79  tff(c_28161, plain, (k7_relat_1('#skF_6', '#skF_2')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_28158, c_30])).
% 14.15/5.79  tff(c_28164, plain, (k7_relat_1('#skF_6', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_28161])).
% 14.15/5.79  tff(c_28171, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_2') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_28164, c_32])).
% 14.15/5.79  tff(c_28177, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_28171])).
% 14.15/5.79  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.15/5.79  tff(c_28187, plain, (k1_relat_1('#skF_6')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_28177, c_10])).
% 14.15/5.79  tff(c_28197, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_28187])).
% 14.15/5.79  tff(c_29563, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29561, c_28197])).
% 14.15/5.79  tff(c_29567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_29563])).
% 14.15/5.79  tff(c_29568, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_29560])).
% 14.15/5.79  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.15/5.79  tff(c_29599, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_29568, c_8])).
% 14.15/5.79  tff(c_29601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_29599])).
% 14.15/5.79  tff(c_29602, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitRight, [status(thm)], [c_28187])).
% 14.15/5.79  tff(c_29711, plain, (![B_1943, A_1944]: (k1_relat_1(k7_relat_1(B_1943, A_1944))=A_1944 | ~r1_tarski(A_1944, k1_relat_1(B_1943)) | ~v1_relat_1(B_1943))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.15/5.79  tff(c_29714, plain, (![A_1944]: (k1_relat_1(k7_relat_1('#skF_6', A_1944))=A_1944 | ~r1_tarski(A_1944, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_29602, c_29711])).
% 14.15/5.79  tff(c_29735, plain, (![A_1944]: (k1_relat_1(k7_relat_1('#skF_6', A_1944))=A_1944 | ~r1_tarski(A_1944, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_29714])).
% 14.15/5.79  tff(c_30888, plain, (![B_2043]: (k1_relat_1(k7_relat_1(B_2043, k1_relat_1(B_2043)))=k1_relat_1(B_2043) | ~v1_relat_1(B_2043))), inference(resolution, [status(thm)], [c_14, c_29711])).
% 14.15/5.79  tff(c_31250, plain, (![A_2055]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_6', A_2055), A_2055))=k1_relat_1(k7_relat_1('#skF_6', A_2055)) | ~v1_relat_1(k7_relat_1('#skF_6', A_2055)) | ~r1_tarski(A_2055, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_29735, c_30888])).
% 14.15/5.79  tff(c_31287, plain, (![A_2055]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_6', A_2055)), A_2055) | ~v1_relat_1(k7_relat_1('#skF_6', A_2055)) | ~v1_relat_1(k7_relat_1('#skF_6', A_2055)) | ~r1_tarski(A_2055, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_31250, c_32])).
% 14.15/5.79  tff(c_30665, plain, (![A_2027, B_2028, C_2029, D_2030]: (k7_relset_1(A_2027, B_2028, C_2029, D_2030)=k9_relat_1(C_2029, D_2030) | ~m1_subset_1(C_2029, k1_zfmisc_1(k2_zfmisc_1(A_2027, B_2028))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.15/5.79  tff(c_30675, plain, (![D_2031]: (k7_relset_1('#skF_2', '#skF_5', '#skF_6', D_2031)=k9_relat_1('#skF_6', D_2031))), inference(resolution, [status(thm)], [c_74, c_30665])).
% 14.15/5.79  tff(c_70, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.15/5.79  tff(c_14853, plain, (![C_995, B_996, A_997]: (~v1_xboole_0(C_995) | ~m1_subset_1(B_996, k1_zfmisc_1(C_995)) | ~r2_hidden(A_997, B_996))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.15/5.79  tff(c_20798, plain, (![B_1360, A_1361, A_1362]: (~v1_xboole_0(B_1360) | ~r2_hidden(A_1361, A_1362) | ~r1_tarski(A_1362, B_1360))), inference(resolution, [status(thm)], [c_20, c_14853])).
% 14.15/5.79  tff(c_20802, plain, (![B_1363, A_1364, B_1365]: (~v1_xboole_0(B_1363) | ~r1_tarski(A_1364, B_1363) | r1_tarski(A_1364, B_1365))), inference(resolution, [status(thm)], [c_6, c_20798])).
% 14.15/5.79  tff(c_20817, plain, (![B_1365]: (~v1_xboole_0('#skF_4') | r1_tarski(k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), B_1365))), inference(resolution, [status(thm)], [c_70, c_20802])).
% 14.15/5.79  tff(c_20823, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_20817])).
% 14.15/5.79  tff(c_21751, plain, (![A_1453, B_1454, C_1455]: (k1_relset_1(A_1453, B_1454, C_1455)=k1_relat_1(C_1455) | ~m1_subset_1(C_1455, k1_zfmisc_1(k2_zfmisc_1(A_1453, B_1454))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.15/5.79  tff(c_21767, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_21751])).
% 14.15/5.79  tff(c_23852, plain, (![B_1559, A_1560, C_1561]: (k1_xboole_0=B_1559 | k1_relset_1(A_1560, B_1559, C_1561)=A_1560 | ~v1_funct_2(C_1561, A_1560, B_1559) | ~m1_subset_1(C_1561, k1_zfmisc_1(k2_zfmisc_1(A_1560, B_1559))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.15/5.79  tff(c_23877, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_23852])).
% 14.15/5.79  tff(c_23886, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_21767, c_23877])).
% 14.15/5.79  tff(c_23887, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_23886])).
% 14.15/5.79  tff(c_20905, plain, (![C_1376, A_1377, B_1378]: (v4_relat_1(C_1376, A_1377) | ~m1_subset_1(C_1376, k1_zfmisc_1(k2_zfmisc_1(A_1377, B_1378))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.15/5.79  tff(c_20914, plain, (v4_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_20905])).
% 14.15/5.79  tff(c_20917, plain, (k7_relat_1('#skF_6', '#skF_2')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20914, c_30])).
% 14.15/5.79  tff(c_20920, plain, (k7_relat_1('#skF_6', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_20917])).
% 14.15/5.79  tff(c_20924, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_2') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_20920, c_32])).
% 14.15/5.79  tff(c_20928, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_20924])).
% 14.15/5.79  tff(c_20942, plain, (k1_relat_1('#skF_6')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20928, c_10])).
% 14.15/5.79  tff(c_20962, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_20942])).
% 14.15/5.79  tff(c_23889, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_23887, c_20962])).
% 14.15/5.79  tff(c_23893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_23889])).
% 14.15/5.79  tff(c_23894, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_23886])).
% 14.15/5.79  tff(c_23937, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_23894, c_8])).
% 14.15/5.79  tff(c_23939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_23937])).
% 14.15/5.79  tff(c_23940, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitRight, [status(thm)], [c_20942])).
% 14.15/5.79  tff(c_24362, plain, (![B_1608, A_1609]: (k1_relat_1(k7_relat_1(B_1608, A_1609))=A_1609 | ~r1_tarski(A_1609, k1_relat_1(B_1608)) | ~v1_relat_1(B_1608))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.15/5.79  tff(c_24385, plain, (![A_1609]: (k1_relat_1(k7_relat_1('#skF_6', A_1609))=A_1609 | ~r1_tarski(A_1609, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_23940, c_24362])).
% 14.15/5.79  tff(c_24416, plain, (![A_1609]: (k1_relat_1(k7_relat_1('#skF_6', A_1609))=A_1609 | ~r1_tarski(A_1609, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_24385])).
% 14.15/5.79  tff(c_27069, plain, (![A_1738, B_1739, C_1740, D_1741]: (k2_partfun1(A_1738, B_1739, C_1740, D_1741)=k7_relat_1(C_1740, D_1741) | ~m1_subset_1(C_1740, k1_zfmisc_1(k2_zfmisc_1(A_1738, B_1739))) | ~v1_funct_1(C_1740))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.15/5.79  tff(c_27086, plain, (![D_1741]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_1741)=k7_relat_1('#skF_6', D_1741) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_27069])).
% 14.15/5.79  tff(c_27094, plain, (![D_1741]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_1741)=k7_relat_1('#skF_6', D_1741))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_27086])).
% 14.15/5.79  tff(c_18695, plain, (![A_1288, B_1289, C_1290, D_1291]: (k2_partfun1(A_1288, B_1289, C_1290, D_1291)=k7_relat_1(C_1290, D_1291) | ~m1_subset_1(C_1290, k1_zfmisc_1(k2_zfmisc_1(A_1288, B_1289))) | ~v1_funct_1(C_1290))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.15/5.79  tff(c_18706, plain, (![D_1291]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_1291)=k7_relat_1('#skF_6', D_1291) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_18695])).
% 14.15/5.79  tff(c_18710, plain, (![D_1291]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_1291)=k7_relat_1('#skF_6', D_1291))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_18706])).
% 14.15/5.79  tff(c_20578, plain, (![A_1355, B_1356, C_1357, D_1358]: (m1_subset_1(k2_partfun1(A_1355, B_1356, C_1357, D_1358), k1_zfmisc_1(k2_zfmisc_1(A_1355, B_1356))) | ~m1_subset_1(C_1357, k1_zfmisc_1(k2_zfmisc_1(A_1355, B_1356))) | ~v1_funct_1(C_1357))), inference(cnfTransformation, [status(thm)], [f_140])).
% 14.15/5.79  tff(c_20627, plain, (![D_1291]: (m1_subset_1(k7_relat_1('#skF_6', D_1291), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_18710, c_20578])).
% 14.15/5.79  tff(c_20657, plain, (![D_1359]: (m1_subset_1(k7_relat_1('#skF_6', D_1359), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_20627])).
% 14.15/5.79  tff(c_20686, plain, (![D_1359]: (v1_relat_1(k7_relat_1('#skF_6', D_1359)) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_5')))), inference(resolution, [status(thm)], [c_20657, c_24])).
% 14.15/5.79  tff(c_20711, plain, (![D_1359]: (v1_relat_1(k7_relat_1('#skF_6', D_1359)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20686])).
% 14.15/5.79  tff(c_18992, plain, (![C_1300, A_1301, B_1302]: (m1_subset_1(C_1300, k1_zfmisc_1(k2_zfmisc_1(A_1301, B_1302))) | ~r1_tarski(k2_relat_1(C_1300), B_1302) | ~r1_tarski(k1_relat_1(C_1300), A_1301) | ~v1_relat_1(C_1300))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.15/5.79  tff(c_14861, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1204])).
% 14.15/5.79  tff(c_18714, plain, (~m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_18710, c_14861])).
% 14.15/5.79  tff(c_19045, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_18992, c_18714])).
% 14.15/5.79  tff(c_19243, plain, (~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_19045])).
% 14.15/5.79  tff(c_20735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20711, c_19243])).
% 14.15/5.79  tff(c_20737, plain, (v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(splitRight, [status(thm)], [c_19045])).
% 14.15/5.79  tff(c_15225, plain, (![A_1050, B_1051, C_1052]: (k1_relset_1(A_1050, B_1051, C_1052)=k1_relat_1(C_1052) | ~m1_subset_1(C_1052, k1_zfmisc_1(k2_zfmisc_1(A_1050, B_1051))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.15/5.79  tff(c_15234, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_15225])).
% 14.15/5.79  tff(c_16409, plain, (![B_1149, A_1150, C_1151]: (k1_xboole_0=B_1149 | k1_relset_1(A_1150, B_1149, C_1151)=A_1150 | ~v1_funct_2(C_1151, A_1150, B_1149) | ~m1_subset_1(C_1151, k1_zfmisc_1(k2_zfmisc_1(A_1150, B_1149))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.15/5.79  tff(c_16425, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_16409])).
% 14.15/5.79  tff(c_16431, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_15234, c_16425])).
% 14.15/5.79  tff(c_16432, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_16431])).
% 14.15/5.79  tff(c_15020, plain, (![C_1030, A_1031, B_1032]: (v4_relat_1(C_1030, A_1031) | ~m1_subset_1(C_1030, k1_zfmisc_1(k2_zfmisc_1(A_1031, B_1032))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.15/5.79  tff(c_15029, plain, (v4_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_15020])).
% 14.15/5.79  tff(c_15042, plain, (k7_relat_1('#skF_6', '#skF_2')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_15029, c_30])).
% 14.15/5.79  tff(c_15045, plain, (k7_relat_1('#skF_6', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_15042])).
% 14.15/5.79  tff(c_15052, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_2') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_15045, c_32])).
% 14.15/5.79  tff(c_15058, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_15052])).
% 14.15/5.79  tff(c_15072, plain, (k1_relat_1('#skF_6')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_15058, c_10])).
% 14.15/5.79  tff(c_15082, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_15072])).
% 14.15/5.79  tff(c_16434, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16432, c_15082])).
% 14.15/5.79  tff(c_16438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_16434])).
% 14.15/5.79  tff(c_16439, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_16431])).
% 14.15/5.79  tff(c_16470, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16439, c_8])).
% 14.15/5.79  tff(c_16472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_16470])).
% 14.15/5.79  tff(c_16473, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitRight, [status(thm)], [c_15072])).
% 14.15/5.79  tff(c_16519, plain, (![B_1156, A_1157]: (k1_relat_1(k7_relat_1(B_1156, A_1157))=A_1157 | ~r1_tarski(A_1157, k1_relat_1(B_1156)) | ~v1_relat_1(B_1156))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.15/5.79  tff(c_16522, plain, (![A_1157]: (k1_relat_1(k7_relat_1('#skF_6', A_1157))=A_1157 | ~r1_tarski(A_1157, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_16473, c_16519])).
% 14.15/5.79  tff(c_16543, plain, (![A_1157]: (k1_relat_1(k7_relat_1('#skF_6', A_1157))=A_1157 | ~r1_tarski(A_1157, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_16522])).
% 14.15/5.79  tff(c_17731, plain, (![B_1257]: (k1_relat_1(k7_relat_1(B_1257, k1_relat_1(B_1257)))=k1_relat_1(B_1257) | ~v1_relat_1(B_1257))), inference(resolution, [status(thm)], [c_14, c_16519])).
% 14.15/5.79  tff(c_18093, plain, (![A_1269]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_6', A_1269), A_1269))=k1_relat_1(k7_relat_1('#skF_6', A_1269)) | ~v1_relat_1(k7_relat_1('#skF_6', A_1269)) | ~r1_tarski(A_1269, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_16543, c_17731])).
% 14.15/5.79  tff(c_18130, plain, (![A_1269]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_6', A_1269)), A_1269) | ~v1_relat_1(k7_relat_1('#skF_6', A_1269)) | ~v1_relat_1(k7_relat_1('#skF_6', A_1269)) | ~r1_tarski(A_1269, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18093, c_32])).
% 14.15/5.79  tff(c_17686, plain, (![A_1252, B_1253, C_1254, D_1255]: (k7_relset_1(A_1252, B_1253, C_1254, D_1255)=k9_relat_1(C_1254, D_1255) | ~m1_subset_1(C_1254, k1_zfmisc_1(k2_zfmisc_1(A_1252, B_1253))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.15/5.79  tff(c_17697, plain, (![D_1255]: (k7_relset_1('#skF_2', '#skF_5', '#skF_6', D_1255)=k9_relat_1('#skF_6', D_1255))), inference(resolution, [status(thm)], [c_74, c_17686])).
% 14.15/5.79  tff(c_17700, plain, (r1_tarski(k9_relat_1('#skF_6', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17697, c_70])).
% 14.15/5.79  tff(c_28, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.15/5.79  tff(c_20736, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_19045])).
% 14.15/5.79  tff(c_20738, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_20736])).
% 14.15/5.79  tff(c_20744, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_28, c_20738])).
% 14.15/5.79  tff(c_20748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_17700, c_20744])).
% 14.15/5.79  tff(c_20749, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_20736])).
% 14.15/5.79  tff(c_20779, plain, (~v1_relat_1(k7_relat_1('#skF_6', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_18130, c_20749])).
% 14.15/5.79  tff(c_20795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_20737, c_20779])).
% 14.15/5.79  tff(c_20797, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1204])).
% 14.15/5.79  tff(c_24632, plain, (![A_1629, B_1630, C_1631]: (k1_relset_1(A_1629, B_1630, C_1631)=k1_relat_1(C_1631) | ~m1_subset_1(C_1631, k1_zfmisc_1(k2_zfmisc_1(A_1629, B_1630))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.15/5.79  tff(c_24643, plain, (k1_relset_1('#skF_3', '#skF_4', k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_20797, c_24632])).
% 14.15/5.79  tff(c_27283, plain, (k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_27094, c_27094, c_24643])).
% 14.15/5.79  tff(c_20796, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1204])).
% 14.15/5.79  tff(c_27289, plain, (~v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27094, c_20796])).
% 14.15/5.79  tff(c_27288, plain, (m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_27094, c_20797])).
% 14.15/5.79  tff(c_27558, plain, (![B_1755, C_1756, A_1757]: (k1_xboole_0=B_1755 | v1_funct_2(C_1756, A_1757, B_1755) | k1_relset_1(A_1757, B_1755, C_1756)!=A_1757 | ~m1_subset_1(C_1756, k1_zfmisc_1(k2_zfmisc_1(A_1757, B_1755))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.15/5.79  tff(c_27561, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_27288, c_27558])).
% 14.15/5.79  tff(c_27586, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_27289, c_27561])).
% 14.15/5.79  tff(c_27725, plain, (k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_27586])).
% 14.15/5.79  tff(c_27874, plain, (k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_27283, c_27725])).
% 14.15/5.79  tff(c_27887, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24416, c_27874])).
% 14.15/5.79  tff(c_27896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_27887])).
% 14.15/5.79  tff(c_27897, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_27586])).
% 14.15/5.79  tff(c_27942, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27897, c_8])).
% 14.15/5.79  tff(c_27945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20823, c_27942])).
% 14.15/5.79  tff(c_27947, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_20817])).
% 14.15/5.79  tff(c_27948, plain, (![B_1770, B_1771]: (~v1_xboole_0(B_1770) | r1_tarski(B_1770, B_1771))), inference(resolution, [status(thm)], [c_14, c_20802])).
% 14.15/5.79  tff(c_1233, plain, (k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_70, c_1218])).
% 14.15/5.79  tff(c_14814, plain, (~r1_tarski('#skF_4', k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1233])).
% 14.15/5.79  tff(c_27953, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_27948, c_14814])).
% 14.15/5.79  tff(c_27974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27947, c_27953])).
% 14.15/5.79  tff(c_27975, plain, (k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1233])).
% 14.15/5.79  tff(c_30681, plain, (k9_relat_1('#skF_6', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_30675, c_27975])).
% 14.15/5.79  tff(c_34069, plain, (![A_2149, B_2150, C_2151, D_2152]: (k2_partfun1(A_2149, B_2150, C_2151, D_2152)=k7_relat_1(C_2151, D_2152) | ~m1_subset_1(C_2151, k1_zfmisc_1(k2_zfmisc_1(A_2149, B_2150))) | ~v1_funct_1(C_2151))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.15/5.79  tff(c_34084, plain, (![D_2152]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2152)=k7_relat_1('#skF_6', D_2152) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_34069])).
% 14.15/5.79  tff(c_34089, plain, (![D_2152]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2152)=k7_relat_1('#skF_6', D_2152))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_34084])).
% 14.15/5.79  tff(c_33876, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_31906])).
% 14.15/5.79  tff(c_33878, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_33876])).
% 14.15/5.79  tff(c_34091, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34089, c_33878])).
% 14.15/5.79  tff(c_34130, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_28, c_34091])).
% 14.15/5.79  tff(c_34134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_14, c_30681, c_34130])).
% 14.15/5.79  tff(c_34136, plain, (r1_tarski(k2_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_33876])).
% 14.15/5.79  tff(c_34175, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34173, c_34136])).
% 14.15/5.79  tff(c_48, plain, (![C_46, A_44, B_45]: (m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~r1_tarski(k2_relat_1(C_46), B_45) | ~r1_tarski(k1_relat_1(C_46), A_44) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.15/5.79  tff(c_34180, plain, (~m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34173, c_28002])).
% 14.15/5.79  tff(c_34256, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_34180])).
% 14.15/5.79  tff(c_34262, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34176, c_34175, c_34256])).
% 14.15/5.79  tff(c_34266, plain, (~v1_relat_1(k7_relat_1('#skF_6', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_31287, c_34262])).
% 14.15/5.79  tff(c_34282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_34176, c_34266])).
% 14.15/5.79  tff(c_34284, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1204])).
% 14.15/5.79  tff(c_37443, plain, (![C_2397, B_2398, A_2399]: (v1_xboole_0(C_2397) | ~m1_subset_1(C_2397, k1_zfmisc_1(k2_zfmisc_1(B_2398, A_2399))) | ~v1_xboole_0(A_2399))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.15/5.79  tff(c_37454, plain, (v1_xboole_0(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34284, c_37443])).
% 14.15/5.79  tff(c_37492, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_37454])).
% 14.15/5.79  tff(c_40973, plain, (![A_2577, B_2578, C_2579, D_2580]: (k2_partfun1(A_2577, B_2578, C_2579, D_2580)=k7_relat_1(C_2579, D_2580) | ~m1_subset_1(C_2579, k1_zfmisc_1(k2_zfmisc_1(A_2577, B_2578))) | ~v1_funct_1(C_2579))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.15/5.79  tff(c_40990, plain, (![D_2580]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2580)=k7_relat_1('#skF_6', D_2580) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_40973])).
% 14.15/5.79  tff(c_40998, plain, (![D_2580]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2580)=k7_relat_1('#skF_6', D_2580))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_40990])).
% 14.15/5.79  tff(c_34283, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1204])).
% 14.15/5.79  tff(c_41012, plain, (~v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40998, c_34283])).
% 14.15/5.79  tff(c_35077, plain, (![A_2258, B_2259, C_2260]: (k1_relset_1(A_2258, B_2259, C_2260)=k1_relat_1(C_2260) | ~m1_subset_1(C_2260, k1_zfmisc_1(k2_zfmisc_1(A_2258, B_2259))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.15/5.79  tff(c_35090, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_35077])).
% 14.15/5.79  tff(c_37091, plain, (![B_2360, A_2361, C_2362]: (k1_xboole_0=B_2360 | k1_relset_1(A_2361, B_2360, C_2362)=A_2361 | ~v1_funct_2(C_2362, A_2361, B_2360) | ~m1_subset_1(C_2362, k1_zfmisc_1(k2_zfmisc_1(A_2361, B_2360))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.15/5.79  tff(c_37113, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_37091])).
% 14.15/5.79  tff(c_37119, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_35090, c_37113])).
% 14.15/5.79  tff(c_37120, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_37119])).
% 14.15/5.79  tff(c_34320, plain, (v4_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_34311])).
% 14.15/5.79  tff(c_34323, plain, (k7_relat_1('#skF_6', '#skF_2')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34320, c_30])).
% 14.15/5.79  tff(c_34326, plain, (k7_relat_1('#skF_6', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_34323])).
% 14.15/5.79  tff(c_34330, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_2') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_34326, c_32])).
% 14.15/5.79  tff(c_34334, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_34330])).
% 14.15/5.79  tff(c_34342, plain, (k1_relat_1('#skF_6')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_34334, c_10])).
% 14.15/5.79  tff(c_34344, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_34342])).
% 14.15/5.79  tff(c_37122, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37120, c_34344])).
% 14.15/5.79  tff(c_37126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_37122])).
% 14.15/5.79  tff(c_37127, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_37119])).
% 14.15/5.79  tff(c_37167, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_37127, c_8])).
% 14.15/5.79  tff(c_37169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_37167])).
% 14.15/5.79  tff(c_37170, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitRight, [status(thm)], [c_34342])).
% 14.15/5.79  tff(c_37569, plain, (![B_2411, A_2412]: (k1_relat_1(k7_relat_1(B_2411, A_2412))=A_2412 | ~r1_tarski(A_2412, k1_relat_1(B_2411)) | ~v1_relat_1(B_2411))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.15/5.79  tff(c_37586, plain, (![A_2412]: (k1_relat_1(k7_relat_1('#skF_6', A_2412))=A_2412 | ~r1_tarski(A_2412, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_37170, c_37569])).
% 14.15/5.79  tff(c_37609, plain, (![A_2412]: (k1_relat_1(k7_relat_1('#skF_6', A_2412))=A_2412 | ~r1_tarski(A_2412, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_37586])).
% 14.15/5.79  tff(c_40302, plain, (![A_2552, B_2553, C_2554, D_2555]: (k2_partfun1(A_2552, B_2553, C_2554, D_2555)=k7_relat_1(C_2554, D_2555) | ~m1_subset_1(C_2554, k1_zfmisc_1(k2_zfmisc_1(A_2552, B_2553))) | ~v1_funct_1(C_2554))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.15/5.79  tff(c_40319, plain, (![D_2555]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2555)=k7_relat_1('#skF_6', D_2555) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_40302])).
% 14.15/5.79  tff(c_40327, plain, (![D_2555]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_2555)=k7_relat_1('#skF_6', D_2555))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_40319])).
% 14.15/5.79  tff(c_37177, plain, (v1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34284, c_24])).
% 14.15/5.79  tff(c_37187, plain, (v1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_37177])).
% 14.15/5.79  tff(c_40, plain, (![C_32, A_30, B_31]: (v4_relat_1(C_32, A_30) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.15/5.79  tff(c_37184, plain, (v4_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_34284, c_40])).
% 14.15/5.79  tff(c_37200, plain, (k7_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3')=k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_37184, c_30])).
% 14.15/5.79  tff(c_37203, plain, (k7_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3')=k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37187, c_37200])).
% 14.15/5.79  tff(c_37856, plain, (r1_tarski(k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37203, c_32])).
% 14.15/5.79  tff(c_37862, plain, (r1_tarski(k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37187, c_37856])).
% 14.15/5.79  tff(c_37876, plain, (k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')))), inference(resolution, [status(thm)], [c_37862, c_10])).
% 14.15/5.79  tff(c_39380, plain, (~r1_tarski('#skF_3', k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')))), inference(splitLeft, [status(thm)], [c_37876])).
% 14.15/5.79  tff(c_40328, plain, (~r1_tarski('#skF_3', k1_relat_1(k7_relat_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40327, c_39380])).
% 14.15/5.79  tff(c_40399, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_37609, c_40328])).
% 14.15/5.79  tff(c_40409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_14, c_40399])).
% 14.15/5.79  tff(c_40410, plain, (k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_37876])).
% 14.15/5.79  tff(c_38019, plain, (![A_2448, B_2449, C_2450]: (k1_relset_1(A_2448, B_2449, C_2450)=k1_relat_1(C_2450) | ~m1_subset_1(C_2450, k1_zfmisc_1(k2_zfmisc_1(A_2448, B_2449))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.15/5.79  tff(c_38030, plain, (k1_relset_1('#skF_3', '#skF_4', k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_34284, c_38019])).
% 14.15/5.79  tff(c_40412, plain, (k1_relset_1('#skF_3', '#skF_4', k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40410, c_38030])).
% 14.15/5.79  tff(c_40999, plain, (k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40998, c_40412])).
% 14.15/5.79  tff(c_41011, plain, (m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40998, c_34284])).
% 14.15/5.79  tff(c_56, plain, (![B_48, C_49, A_47]: (k1_xboole_0=B_48 | v1_funct_2(C_49, A_47, B_48) | k1_relset_1(A_47, B_48, C_49)!=A_47 | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.15/5.79  tff(c_41228, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_41011, c_56])).
% 14.15/5.79  tff(c_41260, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40999, c_41228])).
% 14.15/5.79  tff(c_41261, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_41012, c_41260])).
% 14.15/5.79  tff(c_41322, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41261, c_8])).
% 14.15/5.79  tff(c_41325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37492, c_41322])).
% 14.15/5.79  tff(c_41327, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_37454])).
% 14.15/5.79  tff(c_42057, plain, (![A_2652, A_2653, B_2654]: (v1_xboole_0(A_2652) | ~v1_xboole_0(A_2653) | ~r1_tarski(A_2652, k2_zfmisc_1(B_2654, A_2653)))), inference(resolution, [status(thm)], [c_20, c_37443])).
% 14.15/5.79  tff(c_42093, plain, (![B_2655, A_2656]: (v1_xboole_0(k2_zfmisc_1(B_2655, A_2656)) | ~v1_xboole_0(A_2656))), inference(resolution, [status(thm)], [c_14, c_42057])).
% 14.15/5.79  tff(c_37295, plain, (![C_2373, B_2374, A_2375]: (~v1_xboole_0(C_2373) | ~m1_subset_1(B_2374, k1_zfmisc_1(C_2373)) | ~r2_hidden(A_2375, B_2374))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.15/5.79  tff(c_37335, plain, (![B_2382, A_2383, A_2384]: (~v1_xboole_0(B_2382) | ~r2_hidden(A_2383, A_2384) | ~r1_tarski(A_2384, B_2382))), inference(resolution, [status(thm)], [c_20, c_37295])).
% 14.15/5.79  tff(c_37339, plain, (![B_2385, A_2386, B_2387]: (~v1_xboole_0(B_2385) | ~r1_tarski(A_2386, B_2385) | r1_tarski(A_2386, B_2387))), inference(resolution, [status(thm)], [c_6, c_37335])).
% 14.15/5.79  tff(c_37379, plain, (![B_2390, B_2391]: (~v1_xboole_0(B_2390) | r1_tarski(B_2390, B_2391))), inference(resolution, [status(thm)], [c_14, c_37339])).
% 14.15/5.79  tff(c_1235, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_1218])).
% 14.15/5.79  tff(c_37413, plain, (![B_2390]: (k1_xboole_0=B_2390 | ~v1_xboole_0(B_2390))), inference(resolution, [status(thm)], [c_37379, c_1235])).
% 14.15/5.79  tff(c_41336, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_41327, c_37413])).
% 14.15/5.79  tff(c_41346, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_41336, c_16])).
% 14.15/5.79  tff(c_50, plain, (![A_47]: (v1_funct_2(k1_xboole_0, A_47, k1_xboole_0) | k1_xboole_0=A_47 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_47, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.15/5.79  tff(c_41496, plain, (![A_2596]: (v1_funct_2('#skF_4', A_2596, '#skF_4') | A_2596='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_2596, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_41336, c_41336, c_41336, c_41336, c_41336, c_50])).
% 14.15/5.79  tff(c_41499, plain, (![A_2596]: (v1_funct_2('#skF_4', A_2596, '#skF_4') | A_2596='#skF_4' | ~r1_tarski('#skF_4', k2_zfmisc_1(A_2596, '#skF_4')))), inference(resolution, [status(thm)], [c_20, c_41496])).
% 14.15/5.79  tff(c_41528, plain, (![A_2599]: (v1_funct_2('#skF_4', A_2599, '#skF_4') | A_2599='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41346, c_41499])).
% 14.15/5.79  tff(c_41326, plain, (v1_xboole_0(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitRight, [status(thm)], [c_37454])).
% 14.15/5.79  tff(c_41338, plain, (![B_2390]: (B_2390='#skF_4' | ~v1_xboole_0(B_2390))), inference(demodulation, [status(thm), theory('equality')], [c_41336, c_37413])).
% 14.15/5.79  tff(c_41444, plain, (k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_41326, c_41338])).
% 14.15/5.79  tff(c_41517, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41444, c_34283])).
% 14.15/5.79  tff(c_41532, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_41528, c_41517])).
% 14.15/5.79  tff(c_37302, plain, (![A_2375]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_2375, k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')))), inference(resolution, [status(thm)], [c_34284, c_37295])).
% 14.15/5.79  tff(c_37332, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_37302])).
% 14.15/5.79  tff(c_41535, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_41532, c_37332])).
% 14.15/5.79  tff(c_42098, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42093, c_41535])).
% 14.15/5.79  tff(c_42116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41327, c_42098])).
% 14.15/5.79  tff(c_42140, plain, (![A_2662]: (~r2_hidden(A_2662, k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')))), inference(splitRight, [status(thm)], [c_37302])).
% 14.15/5.79  tff(c_42158, plain, (![B_2664]: (r1_tarski(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), B_2664))), inference(resolution, [status(thm)], [c_6, c_42140])).
% 14.15/5.79  tff(c_42182, plain, (k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42158, c_1235])).
% 14.15/5.79  tff(c_43892, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_43886, c_42182])).
% 14.15/5.79  tff(c_42282, plain, (![B_2675, A_2676]: (k1_relat_1(k7_relat_1(B_2675, A_2676))=A_2676 | ~r1_tarski(A_2676, k1_relat_1(B_2675)) | ~v1_relat_1(B_2675))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.15/5.79  tff(c_42288, plain, (![A_2676]: (k1_relat_1(k7_relat_1('#skF_6', A_2676))=A_2676 | ~r1_tarski(A_2676, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_37170, c_42282])).
% 14.15/5.79  tff(c_42307, plain, (![A_2676]: (k1_relat_1(k7_relat_1('#skF_6', A_2676))=A_2676 | ~r1_tarski(A_2676, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_42288])).
% 14.15/5.79  tff(c_43916, plain, (k1_relat_1(k1_xboole_0)='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_43892, c_42307])).
% 14.15/5.79  tff(c_43931, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_37279, c_43916])).
% 14.15/5.79  tff(c_43975, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_43931, c_43931, c_37279])).
% 14.15/5.79  tff(c_43981, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_43931, c_16])).
% 14.15/5.79  tff(c_42453, plain, (![A_2686, B_2687, C_2688]: (k1_relset_1(A_2686, B_2687, C_2688)=k1_relat_1(C_2688) | ~m1_subset_1(C_2688, k1_zfmisc_1(k2_zfmisc_1(A_2686, B_2687))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.15/5.79  tff(c_44951, plain, (![A_2835, B_2836, A_2837]: (k1_relset_1(A_2835, B_2836, A_2837)=k1_relat_1(A_2837) | ~r1_tarski(A_2837, k2_zfmisc_1(A_2835, B_2836)))), inference(resolution, [status(thm)], [c_20, c_42453])).
% 14.15/5.79  tff(c_44961, plain, (![A_2835, B_2836]: (k1_relset_1(A_2835, B_2836, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_43981, c_44951])).
% 14.15/5.79  tff(c_44986, plain, (![A_2835, B_2836]: (k1_relset_1(A_2835, B_2836, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_43975, c_44961])).
% 14.15/5.79  tff(c_43415, plain, (![C_2775, B_2776]: (v1_funct_2(C_2775, k1_xboole_0, B_2776) | k1_relset_1(k1_xboole_0, B_2776, C_2775)!=k1_xboole_0 | ~m1_subset_1(C_2775, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2776))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.15/5.79  tff(c_43424, plain, (![A_9, B_2776]: (v1_funct_2(A_9, k1_xboole_0, B_2776) | k1_relset_1(k1_xboole_0, B_2776, A_9)!=k1_xboole_0 | ~r1_tarski(A_9, k2_zfmisc_1(k1_xboole_0, B_2776)))), inference(resolution, [status(thm)], [c_20, c_43415])).
% 14.15/5.79  tff(c_46653, plain, (![A_2934, B_2935]: (v1_funct_2(A_2934, '#skF_3', B_2935) | k1_relset_1('#skF_3', B_2935, A_2934)!='#skF_3' | ~r1_tarski(A_2934, k2_zfmisc_1('#skF_3', B_2935)))), inference(demodulation, [status(thm), theory('equality')], [c_43931, c_43931, c_43931, c_43931, c_43424])).
% 14.15/5.79  tff(c_46672, plain, (![B_2935]: (v1_funct_2('#skF_3', '#skF_3', B_2935) | k1_relset_1('#skF_3', B_2935, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_43981, c_46653])).
% 14.15/5.79  tff(c_46696, plain, (![B_2935]: (v1_funct_2('#skF_3', '#skF_3', B_2935))), inference(demodulation, [status(thm), theory('equality')], [c_44986, c_46672])).
% 14.15/5.79  tff(c_42194, plain, (~v1_funct_2(k1_xboole_0, '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42182, c_34283])).
% 14.15/5.79  tff(c_43969, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43931, c_42194])).
% 14.15/5.79  tff(c_46704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46696, c_43969])).
% 14.15/5.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.15/5.79  
% 14.15/5.79  Inference rules
% 14.15/5.79  ----------------------
% 14.15/5.79  #Ref     : 0
% 14.15/5.79  #Sup     : 10557
% 14.15/5.79  #Fact    : 0
% 14.15/5.79  #Define  : 0
% 14.15/5.79  #Split   : 105
% 14.15/5.79  #Chain   : 0
% 14.15/5.79  #Close   : 0
% 14.15/5.79  
% 14.15/5.79  Ordering : KBO
% 14.15/5.79  
% 14.15/5.79  Simplification rules
% 14.15/5.79  ----------------------
% 14.15/5.79  #Subsume      : 2165
% 14.15/5.79  #Demod        : 9322
% 14.15/5.79  #Tautology    : 5102
% 14.15/5.80  #SimpNegUnit  : 48
% 14.15/5.80  #BackRed      : 664
% 14.15/5.80  
% 14.15/5.80  #Partial instantiations: 0
% 14.15/5.80  #Strategies tried      : 1
% 14.15/5.80  
% 14.15/5.80  Timing (in seconds)
% 14.15/5.80  ----------------------
% 14.15/5.80  Preprocessing        : 0.37
% 14.23/5.80  Parsing              : 0.20
% 14.23/5.80  CNF conversion       : 0.03
% 14.23/5.80  Main loop            : 4.59
% 14.23/5.80  Inferencing          : 1.41
% 14.23/5.80  Reduction            : 1.73
% 14.23/5.80  Demodulation         : 1.25
% 14.23/5.80  BG Simplification    : 0.12
% 14.23/5.80  Subsumption          : 0.99
% 14.23/5.80  Abstraction          : 0.18
% 14.23/5.80  MUC search           : 0.00
% 14.23/5.80  Cooper               : 0.00
% 14.23/5.80  Total                : 5.07
% 14.23/5.80  Index Insertion      : 0.00
% 14.23/5.80  Index Deletion       : 0.00
% 14.23/5.80  Index Matching       : 0.00
% 14.23/5.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
