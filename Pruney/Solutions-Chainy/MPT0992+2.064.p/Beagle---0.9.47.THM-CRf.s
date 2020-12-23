%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:40 EST 2020

% Result     : Theorem 9.39s
% Output     : CNFRefutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :  233 (4292 expanded)
%              Number of leaves         :   39 (1357 expanded)
%              Depth                    :   18
%              Number of atoms          :  415 (13262 expanded)
%              Number of equality atoms :   94 (5136 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_138,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_68,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_30,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2362,plain,(
    ! [B_233,A_234] :
      ( v1_relat_1(B_233)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(A_234))
      | ~ v1_relat_1(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2368,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_2362])).

tff(c_2372,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2368])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_79,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_12452,plain,(
    ! [A_732,B_733,C_734] :
      ( k1_relset_1(A_732,B_733,C_734) = k1_relat_1(C_734)
      | ~ m1_subset_1(C_734,k1_zfmisc_1(k2_zfmisc_1(A_732,B_733))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12471,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_12452])).

tff(c_13713,plain,(
    ! [B_828,A_829,C_830] :
      ( k1_xboole_0 = B_828
      | k1_relset_1(A_829,B_828,C_830) = A_829
      | ~ v1_funct_2(C_830,A_829,B_828)
      | ~ m1_subset_1(C_830,k1_zfmisc_1(k2_zfmisc_1(A_829,B_828))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_13726,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_13713])).

tff(c_13741,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12471,c_13726])).

tff(c_13742,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_13741])).

tff(c_36,plain,(
    ! [B_26,A_25] :
      ( k1_relat_1(k7_relat_1(B_26,A_25)) = A_25
      | ~ r1_tarski(A_25,k1_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_13764,plain,(
    ! [A_25] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_25)) = A_25
      | ~ r1_tarski(A_25,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13742,c_36])).

tff(c_13801,plain,(
    ! [A_25] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_25)) = A_25
      | ~ r1_tarski(A_25,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_13764])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_13438,plain,(
    ! [A_813,B_814,C_815,D_816] :
      ( k2_partfun1(A_813,B_814,C_815,D_816) = k7_relat_1(C_815,D_816)
      | ~ m1_subset_1(C_815,k1_zfmisc_1(k2_zfmisc_1(A_813,B_814)))
      | ~ v1_funct_1(C_815) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_13445,plain,(
    ! [D_816] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_816) = k7_relat_1('#skF_4',D_816)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_13438])).

tff(c_13456,plain,(
    ! [D_816] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_816) = k7_relat_1('#skF_4',D_816) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_13445])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k7_relat_1(B_24,A_23),B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_140,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_140])).

tff(c_2396,plain,(
    ! [A_237,C_238,B_239] :
      ( r1_tarski(A_237,C_238)
      | ~ r1_tarski(B_239,C_238)
      | ~ r1_tarski(A_237,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2434,plain,(
    ! [A_243] :
      ( r1_tarski(A_243,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_243,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_144,c_2396])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2369,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(A_7)
      | ~ v1_relat_1(B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_2362])).

tff(c_2439,plain,(
    ! [A_243] :
      ( v1_relat_1(A_243)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_243,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2434,c_2369])).

tff(c_2444,plain,(
    ! [A_244] :
      ( v1_relat_1(A_244)
      | ~ r1_tarski(A_244,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2439])).

tff(c_2452,plain,(
    ! [A_23] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_23))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_2444])).

tff(c_2456,plain,(
    ! [A_23] : v1_relat_1(k7_relat_1('#skF_4',A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_2452])).

tff(c_2405,plain,(
    ! [A_237] :
      ( r1_tarski(A_237,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_237,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_144,c_2396])).

tff(c_2470,plain,(
    ! [C_250,A_251,B_252] :
      ( v4_relat_1(C_250,A_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2520,plain,(
    ! [A_260,A_261,B_262] :
      ( v4_relat_1(A_260,A_261)
      | ~ r1_tarski(A_260,k2_zfmisc_1(A_261,B_262)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2470])).

tff(c_2541,plain,(
    ! [A_237] :
      ( v4_relat_1(A_237,'#skF_1')
      | ~ r1_tarski(A_237,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2405,c_2520])).

tff(c_2565,plain,(
    ! [B_267,A_268] :
      ( k7_relat_1(B_267,A_268) = B_267
      | ~ v4_relat_1(B_267,A_268)
      | ~ v1_relat_1(B_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2888,plain,(
    ! [A_296] :
      ( k7_relat_1(A_296,'#skF_1') = A_296
      | ~ v1_relat_1(A_296)
      | ~ r1_tarski(A_296,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2541,c_2565])).

tff(c_2903,plain,(
    ! [A_23] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_23),'#skF_1') = k7_relat_1('#skF_4',A_23)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_23))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_2888])).

tff(c_2914,plain,(
    ! [A_297] : k7_relat_1(k7_relat_1('#skF_4',A_297),'#skF_1') = k7_relat_1('#skF_4',A_297) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_2456,c_2903])).

tff(c_2923,plain,(
    ! [A_297] :
      ( r1_tarski(k7_relat_1('#skF_4',A_297),k7_relat_1('#skF_4',A_297))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_297)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2914,c_34])).

tff(c_2937,plain,(
    ! [A_297] : r1_tarski(k7_relat_1('#skF_4',A_297),k7_relat_1('#skF_4',A_297)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_2923])).

tff(c_3583,plain,(
    ! [A_327,B_328,A_329] :
      ( r1_tarski(A_327,B_328)
      | ~ r1_tarski(A_327,k7_relat_1(B_328,A_329))
      | ~ v1_relat_1(B_328) ) ),
    inference(resolution,[status(thm)],[c_34,c_2396])).

tff(c_3596,plain,(
    ! [A_297] :
      ( r1_tarski(k7_relat_1('#skF_4',A_297),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2937,c_3583])).

tff(c_3625,plain,(
    ! [A_297] : r1_tarski(k7_relat_1('#skF_4',A_297),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_3596])).

tff(c_2485,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_2470])).

tff(c_3851,plain,(
    ! [A_345,B_346,C_347] :
      ( k1_relset_1(A_345,B_346,C_347) = k1_relat_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3866,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3851])).

tff(c_4831,plain,(
    ! [B_421,A_422,C_423] :
      ( k1_xboole_0 = B_421
      | k1_relset_1(A_422,B_421,C_423) = A_422
      | ~ v1_funct_2(C_423,A_422,B_421)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_422,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4841,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_4831])).

tff(c_4854,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3866,c_4841])).

tff(c_4855,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_4854])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4898,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_1',A_12)
      | ~ v4_relat_1('#skF_4',A_12)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4855,c_20])).

tff(c_5034,plain,(
    ! [A_427] :
      ( r1_tarski('#skF_1',A_427)
      | ~ v4_relat_1('#skF_4',A_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_4898])).

tff(c_5061,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2485,c_5034])).

tff(c_4570,plain,(
    ! [D_405,B_406,C_407,A_408] :
      ( m1_subset_1(D_405,k1_zfmisc_1(k2_zfmisc_1(B_406,C_407)))
      | ~ r1_tarski(k1_relat_1(D_405),B_406)
      | ~ m1_subset_1(D_405,k1_zfmisc_1(k2_zfmisc_1(A_408,C_407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4583,plain,(
    ! [B_409] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_409,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_409) ) ),
    inference(resolution,[status(thm)],[c_70,c_4570])).

tff(c_40,plain,(
    ! [C_29,A_27,B_28] :
      ( v4_relat_1(C_29,A_27)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4614,plain,(
    ! [B_409] :
      ( v4_relat_1('#skF_4',B_409)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_409) ) ),
    inference(resolution,[status(thm)],[c_4583,c_40])).

tff(c_4862,plain,(
    ! [B_409] :
      ( v4_relat_1('#skF_4',B_409)
      | ~ r1_tarski('#skF_1',B_409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4855,c_4614])).

tff(c_2409,plain,(
    ! [B_240,A_241] :
      ( r1_tarski(k1_relat_1(B_240),A_241)
      | ~ v4_relat_1(B_240,A_241)
      | ~ v1_relat_1(B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5671,plain,(
    ! [A_463,A_464,B_465] :
      ( r1_tarski(A_463,A_464)
      | ~ r1_tarski(A_463,k1_relat_1(B_465))
      | ~ v4_relat_1(B_465,A_464)
      | ~ v1_relat_1(B_465) ) ),
    inference(resolution,[status(thm)],[c_2409,c_2])).

tff(c_5675,plain,(
    ! [A_463,A_464] :
      ( r1_tarski(A_463,A_464)
      | ~ r1_tarski(A_463,'#skF_1')
      | ~ v4_relat_1('#skF_4',A_464)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4855,c_5671])).

tff(c_5707,plain,(
    ! [A_466,A_467] :
      ( r1_tarski(A_466,A_467)
      | ~ r1_tarski(A_466,'#skF_1')
      | ~ v4_relat_1('#skF_4',A_467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_5675])).

tff(c_5734,plain,(
    ! [A_468] :
      ( r1_tarski('#skF_3',A_468)
      | ~ v4_relat_1('#skF_4',A_468) ) ),
    inference(resolution,[status(thm)],[c_68,c_5707])).

tff(c_5753,plain,(
    ! [B_409] :
      ( r1_tarski('#skF_3',B_409)
      | ~ r1_tarski('#skF_1',B_409) ) ),
    inference(resolution,[status(thm)],[c_4862,c_5734])).

tff(c_2577,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2485,c_2565])).

tff(c_2583,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_2577])).

tff(c_2632,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2583,c_34])).

tff(c_2640,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_2632])).

tff(c_3124,plain,(
    ! [C_308,A_309,B_310] :
      ( v4_relat_1(k7_relat_1(C_308,A_309),A_309)
      | ~ v4_relat_1(C_308,B_310)
      | ~ v1_relat_1(C_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3145,plain,(
    ! [A_237,A_309] :
      ( v4_relat_1(k7_relat_1(A_237,A_309),A_309)
      | ~ v1_relat_1(A_237)
      | ~ r1_tarski(A_237,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2541,c_3124])).

tff(c_4880,plain,(
    ! [A_25] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_25)) = A_25
      | ~ r1_tarski(A_25,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4855,c_36])).

tff(c_5134,plain,(
    ! [A_434] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_434)) = A_434
      | ~ r1_tarski(A_434,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_4880])).

tff(c_5180,plain,(
    ! [A_434,A_12] :
      ( r1_tarski(A_434,A_12)
      | ~ v4_relat_1(k7_relat_1('#skF_4',A_434),A_12)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_434))
      | ~ r1_tarski(A_434,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5134,c_20])).

tff(c_6938,plain,(
    ! [A_545,A_546] :
      ( r1_tarski(A_545,A_546)
      | ~ v4_relat_1(k7_relat_1('#skF_4',A_545),A_546)
      | ~ r1_tarski(A_545,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_5180])).

tff(c_6957,plain,(
    ! [A_309] :
      ( r1_tarski(A_309,A_309)
      | ~ r1_tarski(A_309,'#skF_1')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3145,c_6938])).

tff(c_7016,plain,(
    ! [A_547] :
      ( r1_tarski(A_547,A_547)
      | ~ r1_tarski(A_547,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2640,c_2372,c_6957])).

tff(c_7019,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5753,c_7016])).

tff(c_7040,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5061,c_7019])).

tff(c_5763,plain,(
    ! [B_469] :
      ( r1_tarski('#skF_3',B_469)
      | ~ r1_tarski('#skF_1',B_469) ) ),
    inference(resolution,[status(thm)],[c_4862,c_5734])).

tff(c_7771,plain,(
    ! [B_562] :
      ( k1_relat_1(k7_relat_1(B_562,'#skF_3')) = '#skF_3'
      | ~ v1_relat_1(B_562)
      | ~ r1_tarski('#skF_1',k1_relat_1(B_562)) ) ),
    inference(resolution,[status(thm)],[c_5763,c_36])).

tff(c_7781,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4855,c_7771])).

tff(c_7797,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5061,c_2372,c_7781])).

tff(c_10308,plain,(
    ! [A_601,B_602,C_603,A_604] :
      ( m1_subset_1(A_601,k1_zfmisc_1(k2_zfmisc_1(B_602,C_603)))
      | ~ r1_tarski(k1_relat_1(A_601),B_602)
      | ~ r1_tarski(A_601,k2_zfmisc_1(A_604,C_603)) ) ),
    inference(resolution,[status(thm)],[c_14,c_4570])).

tff(c_10967,plain,(
    ! [A_630,B_631] :
      ( m1_subset_1(A_630,k1_zfmisc_1(k2_zfmisc_1(B_631,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(A_630),B_631)
      | ~ r1_tarski(A_630,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2405,c_10308])).

tff(c_4723,plain,(
    ! [A_413,B_414,C_415,D_416] :
      ( k2_partfun1(A_413,B_414,C_415,D_416) = k7_relat_1(C_415,D_416)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414)))
      | ~ v1_funct_1(C_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4730,plain,(
    ! [D_416] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_416) = k7_relat_1('#skF_4',D_416)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_4723])).

tff(c_4741,plain,(
    ! [D_416] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_416) = k7_relat_1('#skF_4',D_416) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4730])).

tff(c_2343,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( v1_funct_1(k2_partfun1(A_229,B_230,C_231,D_232))
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2348,plain,(
    ! [D_232] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_232))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_2343])).

tff(c_2356,plain,(
    ! [D_232] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_232)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2348])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_161,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_2359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2356,c_161])).

tff(c_2360,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2373,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2360])).

tff(c_4744,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4741,c_2373])).

tff(c_10980,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10967,c_4744])).

tff(c_11017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3625,c_7040,c_7797,c_10980])).

tff(c_11019,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2360])).

tff(c_12469,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_11019,c_12452])).

tff(c_13460,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13456,c_13456,c_12469])).

tff(c_11018,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2360])).

tff(c_13468,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13456,c_11018])).

tff(c_13467,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13456,c_11019])).

tff(c_13933,plain,(
    ! [B_834,C_835,A_836] :
      ( k1_xboole_0 = B_834
      | v1_funct_2(C_835,A_836,B_834)
      | k1_relset_1(A_836,B_834,C_835) != A_836
      | ~ m1_subset_1(C_835,k1_zfmisc_1(k2_zfmisc_1(A_836,B_834))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_13936,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_13467,c_13933])).

tff(c_13952,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_13468,c_79,c_13936])).

tff(c_14331,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13460,c_13952])).

tff(c_14338,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13801,c_14331])).

tff(c_14342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14338])).

tff(c_14343,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14355,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14343,c_14343,c_8])).

tff(c_14344,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_14349,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14343,c_14344])).

tff(c_14366,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14355,c_14349,c_70])).

tff(c_18606,plain,(
    ! [A_1271,B_1272] :
      ( r1_tarski(A_1271,B_1272)
      | ~ m1_subset_1(A_1271,k1_zfmisc_1(B_1272)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18610,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_14366,c_18606])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14386,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14343,c_14343,c_4])).

tff(c_18614,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18610,c_14386])).

tff(c_14350,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14349,c_72])).

tff(c_18622,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18614,c_18614,c_14350])).

tff(c_16220,plain,(
    ! [A_1023,B_1024] :
      ( r1_tarski(A_1023,B_1024)
      | ~ m1_subset_1(A_1023,k1_zfmisc_1(B_1024)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16224,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_14366,c_16220])).

tff(c_16228,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16224,c_14386])).

tff(c_14363,plain,(
    ! [A_853,B_854] : v1_relat_1(k2_zfmisc_1(A_853,B_854)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14365,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14355,c_14363])).

tff(c_16237,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_14365])).

tff(c_16238,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_14366])).

tff(c_16239,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16228,c_14355])).

tff(c_16374,plain,(
    ! [C_1042,A_1043,B_1044] :
      ( v4_relat_1(C_1042,A_1043)
      | ~ m1_subset_1(C_1042,k1_zfmisc_1(k2_zfmisc_1(A_1043,B_1044))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16420,plain,(
    ! [C_1052,A_1053] :
      ( v4_relat_1(C_1052,A_1053)
      | ~ m1_subset_1(C_1052,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16239,c_16374])).

tff(c_16426,plain,(
    ! [A_1053] : v4_relat_1('#skF_4',A_1053) ),
    inference(resolution,[status(thm)],[c_16238,c_16420])).

tff(c_14403,plain,(
    ! [B_859,A_860] :
      ( r1_tarski(k7_relat_1(B_859,A_860),B_859)
      | ~ v1_relat_1(B_859) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14407,plain,(
    ! [A_860] :
      ( k7_relat_1('#skF_1',A_860) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14403,c_14386])).

tff(c_14410,plain,(
    ! [A_860] : k7_relat_1('#skF_1',A_860) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14365,c_14407])).

tff(c_16231,plain,(
    ! [A_860] : k7_relat_1('#skF_4',A_860) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16228,c_14410])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14367,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14343,c_14343,c_10])).

tff(c_16235,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16228,c_14367])).

tff(c_16468,plain,(
    ! [A_1064,A_1065,B_1066] :
      ( v4_relat_1(A_1064,A_1065)
      | ~ r1_tarski(A_1064,k2_zfmisc_1(A_1065,B_1066)) ) ),
    inference(resolution,[status(thm)],[c_14,c_16374])).

tff(c_16482,plain,(
    ! [A_1065,B_1066,A_23] :
      ( v4_relat_1(k7_relat_1(k2_zfmisc_1(A_1065,B_1066),A_23),A_1065)
      | ~ v1_relat_1(k2_zfmisc_1(A_1065,B_1066)) ) ),
    inference(resolution,[status(thm)],[c_34,c_16468])).

tff(c_16486,plain,(
    ! [A_1065,B_1066,A_23] : v4_relat_1(k7_relat_1(k2_zfmisc_1(A_1065,B_1066),A_23),A_1065) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16482])).

tff(c_16450,plain,(
    ! [B_1060,A_1061] :
      ( r1_tarski(k1_relat_1(B_1060),A_1061)
      | ~ v4_relat_1(B_1060,A_1061)
      | ~ v1_relat_1(B_1060) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16234,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16228,c_14386])).

tff(c_16540,plain,(
    ! [B_1079] :
      ( k1_relat_1(B_1079) = '#skF_4'
      | ~ v4_relat_1(B_1079,'#skF_4')
      | ~ v1_relat_1(B_1079) ) ),
    inference(resolution,[status(thm)],[c_16450,c_16234])).

tff(c_16544,plain,(
    ! [B_1066,A_23] :
      ( k1_relat_1(k7_relat_1(k2_zfmisc_1('#skF_4',B_1066),A_23)) = '#skF_4'
      | ~ v1_relat_1(k7_relat_1(k2_zfmisc_1('#skF_4',B_1066),A_23)) ) ),
    inference(resolution,[status(thm)],[c_16486,c_16540])).

tff(c_16555,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16237,c_16231,c_16235,c_16231,c_16235,c_16544])).

tff(c_16563,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_4',A_12)
      | ~ v4_relat_1('#skF_4',A_12)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16555,c_20])).

tff(c_16570,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16237,c_16426,c_16563])).

tff(c_17124,plain,(
    ! [D_1135,B_1136,C_1137,A_1138] :
      ( m1_subset_1(D_1135,k1_zfmisc_1(k2_zfmisc_1(B_1136,C_1137)))
      | ~ r1_tarski(k1_relat_1(D_1135),B_1136)
      | ~ m1_subset_1(D_1135,k1_zfmisc_1(k2_zfmisc_1(A_1138,C_1137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18496,plain,(
    ! [A_1265,B_1266,C_1267,A_1268] :
      ( m1_subset_1(A_1265,k1_zfmisc_1(k2_zfmisc_1(B_1266,C_1267)))
      | ~ r1_tarski(k1_relat_1(A_1265),B_1266)
      | ~ r1_tarski(A_1265,k2_zfmisc_1(A_1268,C_1267)) ) ),
    inference(resolution,[status(thm)],[c_14,c_17124])).

tff(c_18508,plain,(
    ! [B_1266,C_1267] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1266,C_1267)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1266) ) ),
    inference(resolution,[status(thm)],[c_16570,c_18496])).

tff(c_18532,plain,(
    ! [B_1269,C_1270] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1269,C_1270))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16570,c_16555,c_18508])).

tff(c_62,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k2_partfun1(A_44,B_45,C_46,D_47) = k7_relat_1(C_46,D_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_18542,plain,(
    ! [B_1269,C_1270,D_47] :
      ( k2_partfun1(B_1269,C_1270,'#skF_4',D_47) = k7_relat_1('#skF_4',D_47)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18532,c_62])).

tff(c_18575,plain,(
    ! [B_1269,C_1270,D_47] : k2_partfun1(B_1269,C_1270,'#skF_4',D_47) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16231,c_18542])).

tff(c_14430,plain,(
    ! [A_862,B_863] :
      ( r1_tarski(A_862,B_863)
      | ~ m1_subset_1(A_862,k1_zfmisc_1(B_863)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14434,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_14366,c_14430])).

tff(c_14438,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14434,c_14386])).

tff(c_14448,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14438,c_14366])).

tff(c_14445,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14438,c_14438,c_14367])).

tff(c_16195,plain,(
    ! [A_1016,B_1017,C_1018,D_1019] :
      ( v1_funct_1(k2_partfun1(A_1016,B_1017,C_1018,D_1019))
      | ~ m1_subset_1(C_1018,k1_zfmisc_1(k2_zfmisc_1(A_1016,B_1017)))
      | ~ v1_funct_1(C_1018) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_16204,plain,(
    ! [B_1020,C_1021,D_1022] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_1020,C_1021,D_1022))
      | ~ m1_subset_1(C_1021,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1021) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14445,c_16195])).

tff(c_16206,plain,(
    ! [B_1020,D_1022] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_1020,'#skF_4',D_1022))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14448,c_16204])).

tff(c_16212,plain,(
    ! [B_1020,D_1022] : v1_funct_1(k2_partfun1('#skF_4',B_1020,'#skF_4',D_1022)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16206])).

tff(c_14387,plain,(
    ! [A_856] :
      ( A_856 = '#skF_1'
      | ~ r1_tarski(A_856,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14343,c_14343,c_4])).

tff(c_14391,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_68,c_14387])).

tff(c_14428,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14391,c_14349,c_14391,c_14391,c_14349,c_14349,c_14391,c_14355,c_14349,c_14349,c_64])).

tff(c_14429,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_14428])).

tff(c_14440,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14438,c_14438,c_14438,c_14429])).

tff(c_16216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16212,c_14440])).

tff(c_16217,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_14428])).

tff(c_16219,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_16217])).

tff(c_16350,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16228,c_16228,c_16228,c_16219])).

tff(c_16354,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_16350])).

tff(c_18597,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18575,c_16354])).

tff(c_18603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16570,c_18597])).

tff(c_18605,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_16217])).

tff(c_18748,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18614,c_18614,c_18614,c_18614,c_18605])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18758,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_18748,c_12])).

tff(c_18620,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18614,c_18614,c_14386])).

tff(c_18768,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18758,c_18620])).

tff(c_18604,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_16217])).

tff(c_18747,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18614,c_18614,c_18614,c_18614,c_18614,c_18604])).

tff(c_18772,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18768,c_18747])).

tff(c_18779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18622,c_18772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.39/3.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.44  
% 9.61/3.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.61/3.44  
% 9.61/3.44  %Foreground sorts:
% 9.61/3.44  
% 9.61/3.44  
% 9.61/3.44  %Background operators:
% 9.61/3.44  
% 9.61/3.44  
% 9.61/3.44  %Foreground operators:
% 9.61/3.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.61/3.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.61/3.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.61/3.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.61/3.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.61/3.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.61/3.44  tff('#skF_2', type, '#skF_2': $i).
% 9.61/3.44  tff('#skF_3', type, '#skF_3': $i).
% 9.61/3.44  tff('#skF_1', type, '#skF_1': $i).
% 9.61/3.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.61/3.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.61/3.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.61/3.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.61/3.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.61/3.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.61/3.44  tff('#skF_4', type, '#skF_4': $i).
% 9.61/3.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.61/3.44  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.61/3.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.61/3.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.61/3.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.61/3.44  
% 9.61/3.47  tff(f_158, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 9.61/3.47  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.61/3.47  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.61/3.47  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.61/3.47  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.61/3.47  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 9.61/3.47  tff(f_138, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.61/3.47  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 9.61/3.47  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.61/3.47  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.61/3.47  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.61/3.47  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.61/3.47  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.61/3.47  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 9.61/3.47  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 9.61/3.47  tff(f_132, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.61/3.47  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.61/3.47  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.61/3.47  tff(c_68, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.61/3.47  tff(c_30, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.61/3.47  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.61/3.47  tff(c_2362, plain, (![B_233, A_234]: (v1_relat_1(B_233) | ~m1_subset_1(B_233, k1_zfmisc_1(A_234)) | ~v1_relat_1(A_234))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.61/3.47  tff(c_2368, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_2362])).
% 9.61/3.47  tff(c_2372, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2368])).
% 9.61/3.47  tff(c_66, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.61/3.47  tff(c_79, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_66])).
% 9.61/3.47  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.61/3.47  tff(c_12452, plain, (![A_732, B_733, C_734]: (k1_relset_1(A_732, B_733, C_734)=k1_relat_1(C_734) | ~m1_subset_1(C_734, k1_zfmisc_1(k2_zfmisc_1(A_732, B_733))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.61/3.47  tff(c_12471, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_12452])).
% 9.61/3.47  tff(c_13713, plain, (![B_828, A_829, C_830]: (k1_xboole_0=B_828 | k1_relset_1(A_829, B_828, C_830)=A_829 | ~v1_funct_2(C_830, A_829, B_828) | ~m1_subset_1(C_830, k1_zfmisc_1(k2_zfmisc_1(A_829, B_828))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.61/3.47  tff(c_13726, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_13713])).
% 9.61/3.47  tff(c_13741, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_12471, c_13726])).
% 9.61/3.47  tff(c_13742, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_79, c_13741])).
% 9.61/3.47  tff(c_36, plain, (![B_26, A_25]: (k1_relat_1(k7_relat_1(B_26, A_25))=A_25 | ~r1_tarski(A_25, k1_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.61/3.47  tff(c_13764, plain, (![A_25]: (k1_relat_1(k7_relat_1('#skF_4', A_25))=A_25 | ~r1_tarski(A_25, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13742, c_36])).
% 9.61/3.47  tff(c_13801, plain, (![A_25]: (k1_relat_1(k7_relat_1('#skF_4', A_25))=A_25 | ~r1_tarski(A_25, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_13764])).
% 9.61/3.47  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.61/3.47  tff(c_13438, plain, (![A_813, B_814, C_815, D_816]: (k2_partfun1(A_813, B_814, C_815, D_816)=k7_relat_1(C_815, D_816) | ~m1_subset_1(C_815, k1_zfmisc_1(k2_zfmisc_1(A_813, B_814))) | ~v1_funct_1(C_815))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.61/3.47  tff(c_13445, plain, (![D_816]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_816)=k7_relat_1('#skF_4', D_816) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_13438])).
% 9.61/3.47  tff(c_13456, plain, (![D_816]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_816)=k7_relat_1('#skF_4', D_816))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_13445])).
% 9.61/3.47  tff(c_34, plain, (![B_24, A_23]: (r1_tarski(k7_relat_1(B_24, A_23), B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.61/3.47  tff(c_140, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.47  tff(c_144, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_140])).
% 9.61/3.47  tff(c_2396, plain, (![A_237, C_238, B_239]: (r1_tarski(A_237, C_238) | ~r1_tarski(B_239, C_238) | ~r1_tarski(A_237, B_239))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.47  tff(c_2434, plain, (![A_243]: (r1_tarski(A_243, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_243, '#skF_4'))), inference(resolution, [status(thm)], [c_144, c_2396])).
% 9.61/3.47  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.47  tff(c_2369, plain, (![A_7, B_8]: (v1_relat_1(A_7) | ~v1_relat_1(B_8) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_14, c_2362])).
% 9.61/3.47  tff(c_2439, plain, (![A_243]: (v1_relat_1(A_243) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_243, '#skF_4'))), inference(resolution, [status(thm)], [c_2434, c_2369])).
% 9.61/3.47  tff(c_2444, plain, (![A_244]: (v1_relat_1(A_244) | ~r1_tarski(A_244, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2439])).
% 9.61/3.47  tff(c_2452, plain, (![A_23]: (v1_relat_1(k7_relat_1('#skF_4', A_23)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_2444])).
% 9.61/3.47  tff(c_2456, plain, (![A_23]: (v1_relat_1(k7_relat_1('#skF_4', A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_2452])).
% 9.61/3.47  tff(c_2405, plain, (![A_237]: (r1_tarski(A_237, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_237, '#skF_4'))), inference(resolution, [status(thm)], [c_144, c_2396])).
% 9.61/3.47  tff(c_2470, plain, (![C_250, A_251, B_252]: (v4_relat_1(C_250, A_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.61/3.47  tff(c_2520, plain, (![A_260, A_261, B_262]: (v4_relat_1(A_260, A_261) | ~r1_tarski(A_260, k2_zfmisc_1(A_261, B_262)))), inference(resolution, [status(thm)], [c_14, c_2470])).
% 9.61/3.47  tff(c_2541, plain, (![A_237]: (v4_relat_1(A_237, '#skF_1') | ~r1_tarski(A_237, '#skF_4'))), inference(resolution, [status(thm)], [c_2405, c_2520])).
% 9.61/3.47  tff(c_2565, plain, (![B_267, A_268]: (k7_relat_1(B_267, A_268)=B_267 | ~v4_relat_1(B_267, A_268) | ~v1_relat_1(B_267))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.61/3.47  tff(c_2888, plain, (![A_296]: (k7_relat_1(A_296, '#skF_1')=A_296 | ~v1_relat_1(A_296) | ~r1_tarski(A_296, '#skF_4'))), inference(resolution, [status(thm)], [c_2541, c_2565])).
% 9.61/3.47  tff(c_2903, plain, (![A_23]: (k7_relat_1(k7_relat_1('#skF_4', A_23), '#skF_1')=k7_relat_1('#skF_4', A_23) | ~v1_relat_1(k7_relat_1('#skF_4', A_23)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_2888])).
% 9.61/3.47  tff(c_2914, plain, (![A_297]: (k7_relat_1(k7_relat_1('#skF_4', A_297), '#skF_1')=k7_relat_1('#skF_4', A_297))), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_2456, c_2903])).
% 9.61/3.47  tff(c_2923, plain, (![A_297]: (r1_tarski(k7_relat_1('#skF_4', A_297), k7_relat_1('#skF_4', A_297)) | ~v1_relat_1(k7_relat_1('#skF_4', A_297)))), inference(superposition, [status(thm), theory('equality')], [c_2914, c_34])).
% 9.61/3.47  tff(c_2937, plain, (![A_297]: (r1_tarski(k7_relat_1('#skF_4', A_297), k7_relat_1('#skF_4', A_297)))), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_2923])).
% 9.61/3.47  tff(c_3583, plain, (![A_327, B_328, A_329]: (r1_tarski(A_327, B_328) | ~r1_tarski(A_327, k7_relat_1(B_328, A_329)) | ~v1_relat_1(B_328))), inference(resolution, [status(thm)], [c_34, c_2396])).
% 9.61/3.47  tff(c_3596, plain, (![A_297]: (r1_tarski(k7_relat_1('#skF_4', A_297), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2937, c_3583])).
% 9.61/3.47  tff(c_3625, plain, (![A_297]: (r1_tarski(k7_relat_1('#skF_4', A_297), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_3596])).
% 9.61/3.47  tff(c_2485, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_2470])).
% 9.61/3.47  tff(c_3851, plain, (![A_345, B_346, C_347]: (k1_relset_1(A_345, B_346, C_347)=k1_relat_1(C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.61/3.47  tff(c_3866, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3851])).
% 9.61/3.47  tff(c_4831, plain, (![B_421, A_422, C_423]: (k1_xboole_0=B_421 | k1_relset_1(A_422, B_421, C_423)=A_422 | ~v1_funct_2(C_423, A_422, B_421) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_422, B_421))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.61/3.47  tff(c_4841, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_4831])).
% 9.61/3.47  tff(c_4854, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3866, c_4841])).
% 9.61/3.47  tff(c_4855, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_79, c_4854])).
% 9.61/3.47  tff(c_20, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.61/3.47  tff(c_4898, plain, (![A_12]: (r1_tarski('#skF_1', A_12) | ~v4_relat_1('#skF_4', A_12) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4855, c_20])).
% 9.61/3.47  tff(c_5034, plain, (![A_427]: (r1_tarski('#skF_1', A_427) | ~v4_relat_1('#skF_4', A_427))), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_4898])).
% 9.61/3.47  tff(c_5061, plain, (r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2485, c_5034])).
% 9.61/3.47  tff(c_4570, plain, (![D_405, B_406, C_407, A_408]: (m1_subset_1(D_405, k1_zfmisc_1(k2_zfmisc_1(B_406, C_407))) | ~r1_tarski(k1_relat_1(D_405), B_406) | ~m1_subset_1(D_405, k1_zfmisc_1(k2_zfmisc_1(A_408, C_407))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.61/3.47  tff(c_4583, plain, (![B_409]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_409, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_409))), inference(resolution, [status(thm)], [c_70, c_4570])).
% 9.61/3.47  tff(c_40, plain, (![C_29, A_27, B_28]: (v4_relat_1(C_29, A_27) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.61/3.47  tff(c_4614, plain, (![B_409]: (v4_relat_1('#skF_4', B_409) | ~r1_tarski(k1_relat_1('#skF_4'), B_409))), inference(resolution, [status(thm)], [c_4583, c_40])).
% 9.61/3.47  tff(c_4862, plain, (![B_409]: (v4_relat_1('#skF_4', B_409) | ~r1_tarski('#skF_1', B_409))), inference(demodulation, [status(thm), theory('equality')], [c_4855, c_4614])).
% 9.61/3.47  tff(c_2409, plain, (![B_240, A_241]: (r1_tarski(k1_relat_1(B_240), A_241) | ~v4_relat_1(B_240, A_241) | ~v1_relat_1(B_240))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.61/3.47  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.47  tff(c_5671, plain, (![A_463, A_464, B_465]: (r1_tarski(A_463, A_464) | ~r1_tarski(A_463, k1_relat_1(B_465)) | ~v4_relat_1(B_465, A_464) | ~v1_relat_1(B_465))), inference(resolution, [status(thm)], [c_2409, c_2])).
% 9.61/3.47  tff(c_5675, plain, (![A_463, A_464]: (r1_tarski(A_463, A_464) | ~r1_tarski(A_463, '#skF_1') | ~v4_relat_1('#skF_4', A_464) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4855, c_5671])).
% 9.61/3.47  tff(c_5707, plain, (![A_466, A_467]: (r1_tarski(A_466, A_467) | ~r1_tarski(A_466, '#skF_1') | ~v4_relat_1('#skF_4', A_467))), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_5675])).
% 9.61/3.47  tff(c_5734, plain, (![A_468]: (r1_tarski('#skF_3', A_468) | ~v4_relat_1('#skF_4', A_468))), inference(resolution, [status(thm)], [c_68, c_5707])).
% 9.61/3.47  tff(c_5753, plain, (![B_409]: (r1_tarski('#skF_3', B_409) | ~r1_tarski('#skF_1', B_409))), inference(resolution, [status(thm)], [c_4862, c_5734])).
% 9.61/3.47  tff(c_2577, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2485, c_2565])).
% 9.61/3.47  tff(c_2583, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_2577])).
% 9.61/3.47  tff(c_2632, plain, (r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2583, c_34])).
% 9.61/3.47  tff(c_2640, plain, (r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_2632])).
% 9.61/3.47  tff(c_3124, plain, (![C_308, A_309, B_310]: (v4_relat_1(k7_relat_1(C_308, A_309), A_309) | ~v4_relat_1(C_308, B_310) | ~v1_relat_1(C_308))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.61/3.47  tff(c_3145, plain, (![A_237, A_309]: (v4_relat_1(k7_relat_1(A_237, A_309), A_309) | ~v1_relat_1(A_237) | ~r1_tarski(A_237, '#skF_4'))), inference(resolution, [status(thm)], [c_2541, c_3124])).
% 9.61/3.47  tff(c_4880, plain, (![A_25]: (k1_relat_1(k7_relat_1('#skF_4', A_25))=A_25 | ~r1_tarski(A_25, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4855, c_36])).
% 9.61/3.47  tff(c_5134, plain, (![A_434]: (k1_relat_1(k7_relat_1('#skF_4', A_434))=A_434 | ~r1_tarski(A_434, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_4880])).
% 9.61/3.47  tff(c_5180, plain, (![A_434, A_12]: (r1_tarski(A_434, A_12) | ~v4_relat_1(k7_relat_1('#skF_4', A_434), A_12) | ~v1_relat_1(k7_relat_1('#skF_4', A_434)) | ~r1_tarski(A_434, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5134, c_20])).
% 9.61/3.47  tff(c_6938, plain, (![A_545, A_546]: (r1_tarski(A_545, A_546) | ~v4_relat_1(k7_relat_1('#skF_4', A_545), A_546) | ~r1_tarski(A_545, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_5180])).
% 9.61/3.47  tff(c_6957, plain, (![A_309]: (r1_tarski(A_309, A_309) | ~r1_tarski(A_309, '#skF_1') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_3145, c_6938])).
% 9.61/3.47  tff(c_7016, plain, (![A_547]: (r1_tarski(A_547, A_547) | ~r1_tarski(A_547, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2640, c_2372, c_6957])).
% 9.61/3.47  tff(c_7019, plain, (r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5753, c_7016])).
% 9.61/3.47  tff(c_7040, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5061, c_7019])).
% 9.61/3.47  tff(c_5763, plain, (![B_469]: (r1_tarski('#skF_3', B_469) | ~r1_tarski('#skF_1', B_469))), inference(resolution, [status(thm)], [c_4862, c_5734])).
% 9.61/3.47  tff(c_7771, plain, (![B_562]: (k1_relat_1(k7_relat_1(B_562, '#skF_3'))='#skF_3' | ~v1_relat_1(B_562) | ~r1_tarski('#skF_1', k1_relat_1(B_562)))), inference(resolution, [status(thm)], [c_5763, c_36])).
% 9.61/3.47  tff(c_7781, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4855, c_7771])).
% 9.61/3.47  tff(c_7797, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5061, c_2372, c_7781])).
% 9.61/3.47  tff(c_10308, plain, (![A_601, B_602, C_603, A_604]: (m1_subset_1(A_601, k1_zfmisc_1(k2_zfmisc_1(B_602, C_603))) | ~r1_tarski(k1_relat_1(A_601), B_602) | ~r1_tarski(A_601, k2_zfmisc_1(A_604, C_603)))), inference(resolution, [status(thm)], [c_14, c_4570])).
% 9.61/3.47  tff(c_10967, plain, (![A_630, B_631]: (m1_subset_1(A_630, k1_zfmisc_1(k2_zfmisc_1(B_631, '#skF_2'))) | ~r1_tarski(k1_relat_1(A_630), B_631) | ~r1_tarski(A_630, '#skF_4'))), inference(resolution, [status(thm)], [c_2405, c_10308])).
% 9.61/3.47  tff(c_4723, plain, (![A_413, B_414, C_415, D_416]: (k2_partfun1(A_413, B_414, C_415, D_416)=k7_relat_1(C_415, D_416) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))) | ~v1_funct_1(C_415))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.61/3.47  tff(c_4730, plain, (![D_416]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_416)=k7_relat_1('#skF_4', D_416) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_4723])).
% 9.61/3.47  tff(c_4741, plain, (![D_416]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_416)=k7_relat_1('#skF_4', D_416))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4730])).
% 9.61/3.47  tff(c_2343, plain, (![A_229, B_230, C_231, D_232]: (v1_funct_1(k2_partfun1(A_229, B_230, C_231, D_232)) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~v1_funct_1(C_231))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.61/3.47  tff(c_2348, plain, (![D_232]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_232)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_2343])).
% 9.61/3.47  tff(c_2356, plain, (![D_232]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_232)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2348])).
% 9.61/3.47  tff(c_64, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.61/3.47  tff(c_161, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 9.61/3.47  tff(c_2359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2356, c_161])).
% 9.61/3.47  tff(c_2360, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_64])).
% 9.61/3.47  tff(c_2373, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2360])).
% 9.61/3.47  tff(c_4744, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4741, c_2373])).
% 9.61/3.47  tff(c_10980, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_10967, c_4744])).
% 9.61/3.47  tff(c_11017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3625, c_7040, c_7797, c_10980])).
% 9.61/3.47  tff(c_11019, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_2360])).
% 9.61/3.47  tff(c_12469, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_11019, c_12452])).
% 9.61/3.47  tff(c_13460, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13456, c_13456, c_12469])).
% 9.61/3.47  tff(c_11018, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_2360])).
% 9.61/3.47  tff(c_13468, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13456, c_11018])).
% 9.61/3.47  tff(c_13467, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_13456, c_11019])).
% 9.61/3.47  tff(c_13933, plain, (![B_834, C_835, A_836]: (k1_xboole_0=B_834 | v1_funct_2(C_835, A_836, B_834) | k1_relset_1(A_836, B_834, C_835)!=A_836 | ~m1_subset_1(C_835, k1_zfmisc_1(k2_zfmisc_1(A_836, B_834))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.61/3.47  tff(c_13936, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_13467, c_13933])).
% 9.61/3.47  tff(c_13952, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_13468, c_79, c_13936])).
% 9.61/3.47  tff(c_14331, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13460, c_13952])).
% 9.61/3.47  tff(c_14338, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13801, c_14331])).
% 9.61/3.47  tff(c_14342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_14338])).
% 9.61/3.47  tff(c_14343, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_66])).
% 9.61/3.47  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.61/3.47  tff(c_14355, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14343, c_14343, c_8])).
% 9.61/3.47  tff(c_14344, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 9.61/3.47  tff(c_14349, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14343, c_14344])).
% 9.61/3.47  tff(c_14366, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14355, c_14349, c_70])).
% 9.61/3.47  tff(c_18606, plain, (![A_1271, B_1272]: (r1_tarski(A_1271, B_1272) | ~m1_subset_1(A_1271, k1_zfmisc_1(B_1272)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.47  tff(c_18610, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_14366, c_18606])).
% 9.61/3.47  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.61/3.47  tff(c_14386, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14343, c_14343, c_4])).
% 9.61/3.47  tff(c_18614, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_18610, c_14386])).
% 9.61/3.47  tff(c_14350, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14349, c_72])).
% 9.61/3.47  tff(c_18622, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18614, c_18614, c_14350])).
% 9.61/3.47  tff(c_16220, plain, (![A_1023, B_1024]: (r1_tarski(A_1023, B_1024) | ~m1_subset_1(A_1023, k1_zfmisc_1(B_1024)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.47  tff(c_16224, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_14366, c_16220])).
% 9.61/3.47  tff(c_16228, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_16224, c_14386])).
% 9.61/3.47  tff(c_14363, plain, (![A_853, B_854]: (v1_relat_1(k2_zfmisc_1(A_853, B_854)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.61/3.47  tff(c_14365, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14355, c_14363])).
% 9.61/3.47  tff(c_16237, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_14365])).
% 9.61/3.47  tff(c_16238, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_14366])).
% 9.61/3.47  tff(c_16239, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16228, c_14355])).
% 9.61/3.47  tff(c_16374, plain, (![C_1042, A_1043, B_1044]: (v4_relat_1(C_1042, A_1043) | ~m1_subset_1(C_1042, k1_zfmisc_1(k2_zfmisc_1(A_1043, B_1044))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.61/3.47  tff(c_16420, plain, (![C_1052, A_1053]: (v4_relat_1(C_1052, A_1053) | ~m1_subset_1(C_1052, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_16239, c_16374])).
% 9.61/3.47  tff(c_16426, plain, (![A_1053]: (v4_relat_1('#skF_4', A_1053))), inference(resolution, [status(thm)], [c_16238, c_16420])).
% 9.61/3.47  tff(c_14403, plain, (![B_859, A_860]: (r1_tarski(k7_relat_1(B_859, A_860), B_859) | ~v1_relat_1(B_859))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.61/3.47  tff(c_14407, plain, (![A_860]: (k7_relat_1('#skF_1', A_860)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_14403, c_14386])).
% 9.61/3.47  tff(c_14410, plain, (![A_860]: (k7_relat_1('#skF_1', A_860)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14365, c_14407])).
% 9.61/3.47  tff(c_16231, plain, (![A_860]: (k7_relat_1('#skF_4', A_860)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16228, c_14410])).
% 9.61/3.47  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.61/3.47  tff(c_14367, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14343, c_14343, c_10])).
% 9.61/3.47  tff(c_16235, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16228, c_14367])).
% 9.61/3.47  tff(c_16468, plain, (![A_1064, A_1065, B_1066]: (v4_relat_1(A_1064, A_1065) | ~r1_tarski(A_1064, k2_zfmisc_1(A_1065, B_1066)))), inference(resolution, [status(thm)], [c_14, c_16374])).
% 9.61/3.47  tff(c_16482, plain, (![A_1065, B_1066, A_23]: (v4_relat_1(k7_relat_1(k2_zfmisc_1(A_1065, B_1066), A_23), A_1065) | ~v1_relat_1(k2_zfmisc_1(A_1065, B_1066)))), inference(resolution, [status(thm)], [c_34, c_16468])).
% 9.61/3.47  tff(c_16486, plain, (![A_1065, B_1066, A_23]: (v4_relat_1(k7_relat_1(k2_zfmisc_1(A_1065, B_1066), A_23), A_1065))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16482])).
% 9.61/3.47  tff(c_16450, plain, (![B_1060, A_1061]: (r1_tarski(k1_relat_1(B_1060), A_1061) | ~v4_relat_1(B_1060, A_1061) | ~v1_relat_1(B_1060))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.61/3.47  tff(c_16234, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16228, c_14386])).
% 9.61/3.47  tff(c_16540, plain, (![B_1079]: (k1_relat_1(B_1079)='#skF_4' | ~v4_relat_1(B_1079, '#skF_4') | ~v1_relat_1(B_1079))), inference(resolution, [status(thm)], [c_16450, c_16234])).
% 9.61/3.47  tff(c_16544, plain, (![B_1066, A_23]: (k1_relat_1(k7_relat_1(k2_zfmisc_1('#skF_4', B_1066), A_23))='#skF_4' | ~v1_relat_1(k7_relat_1(k2_zfmisc_1('#skF_4', B_1066), A_23)))), inference(resolution, [status(thm)], [c_16486, c_16540])).
% 9.61/3.47  tff(c_16555, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16237, c_16231, c_16235, c_16231, c_16235, c_16544])).
% 9.61/3.47  tff(c_16563, plain, (![A_12]: (r1_tarski('#skF_4', A_12) | ~v4_relat_1('#skF_4', A_12) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16555, c_20])).
% 9.61/3.47  tff(c_16570, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_16237, c_16426, c_16563])).
% 9.61/3.47  tff(c_17124, plain, (![D_1135, B_1136, C_1137, A_1138]: (m1_subset_1(D_1135, k1_zfmisc_1(k2_zfmisc_1(B_1136, C_1137))) | ~r1_tarski(k1_relat_1(D_1135), B_1136) | ~m1_subset_1(D_1135, k1_zfmisc_1(k2_zfmisc_1(A_1138, C_1137))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.61/3.47  tff(c_18496, plain, (![A_1265, B_1266, C_1267, A_1268]: (m1_subset_1(A_1265, k1_zfmisc_1(k2_zfmisc_1(B_1266, C_1267))) | ~r1_tarski(k1_relat_1(A_1265), B_1266) | ~r1_tarski(A_1265, k2_zfmisc_1(A_1268, C_1267)))), inference(resolution, [status(thm)], [c_14, c_17124])).
% 9.61/3.47  tff(c_18508, plain, (![B_1266, C_1267]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1266, C_1267))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1266))), inference(resolution, [status(thm)], [c_16570, c_18496])).
% 9.61/3.47  tff(c_18532, plain, (![B_1269, C_1270]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1269, C_1270))))), inference(demodulation, [status(thm), theory('equality')], [c_16570, c_16555, c_18508])).
% 9.61/3.47  tff(c_62, plain, (![A_44, B_45, C_46, D_47]: (k2_partfun1(A_44, B_45, C_46, D_47)=k7_relat_1(C_46, D_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_1(C_46))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.61/3.47  tff(c_18542, plain, (![B_1269, C_1270, D_47]: (k2_partfun1(B_1269, C_1270, '#skF_4', D_47)=k7_relat_1('#skF_4', D_47) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_18532, c_62])).
% 9.61/3.47  tff(c_18575, plain, (![B_1269, C_1270, D_47]: (k2_partfun1(B_1269, C_1270, '#skF_4', D_47)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16231, c_18542])).
% 9.61/3.47  tff(c_14430, plain, (![A_862, B_863]: (r1_tarski(A_862, B_863) | ~m1_subset_1(A_862, k1_zfmisc_1(B_863)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.47  tff(c_14434, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_14366, c_14430])).
% 9.61/3.47  tff(c_14438, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_14434, c_14386])).
% 9.61/3.47  tff(c_14448, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14438, c_14366])).
% 9.61/3.47  tff(c_14445, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14438, c_14438, c_14367])).
% 9.61/3.47  tff(c_16195, plain, (![A_1016, B_1017, C_1018, D_1019]: (v1_funct_1(k2_partfun1(A_1016, B_1017, C_1018, D_1019)) | ~m1_subset_1(C_1018, k1_zfmisc_1(k2_zfmisc_1(A_1016, B_1017))) | ~v1_funct_1(C_1018))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.61/3.47  tff(c_16204, plain, (![B_1020, C_1021, D_1022]: (v1_funct_1(k2_partfun1('#skF_4', B_1020, C_1021, D_1022)) | ~m1_subset_1(C_1021, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1021))), inference(superposition, [status(thm), theory('equality')], [c_14445, c_16195])).
% 9.61/3.47  tff(c_16206, plain, (![B_1020, D_1022]: (v1_funct_1(k2_partfun1('#skF_4', B_1020, '#skF_4', D_1022)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_14448, c_16204])).
% 9.61/3.47  tff(c_16212, plain, (![B_1020, D_1022]: (v1_funct_1(k2_partfun1('#skF_4', B_1020, '#skF_4', D_1022)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16206])).
% 9.61/3.47  tff(c_14387, plain, (![A_856]: (A_856='#skF_1' | ~r1_tarski(A_856, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14343, c_14343, c_4])).
% 9.61/3.47  tff(c_14391, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_68, c_14387])).
% 9.61/3.47  tff(c_14428, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14391, c_14349, c_14391, c_14391, c_14349, c_14349, c_14391, c_14355, c_14349, c_14349, c_64])).
% 9.61/3.47  tff(c_14429, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_14428])).
% 9.61/3.47  tff(c_14440, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14438, c_14438, c_14438, c_14429])).
% 9.61/3.47  tff(c_16216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16212, c_14440])).
% 9.61/3.47  tff(c_16217, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_14428])).
% 9.61/3.47  tff(c_16219, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_16217])).
% 9.61/3.47  tff(c_16350, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16228, c_16228, c_16228, c_16219])).
% 9.61/3.47  tff(c_16354, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_14, c_16350])).
% 9.61/3.47  tff(c_18597, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18575, c_16354])).
% 9.61/3.47  tff(c_18603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16570, c_18597])).
% 9.61/3.47  tff(c_18605, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_16217])).
% 9.61/3.47  tff(c_18748, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18614, c_18614, c_18614, c_18614, c_18605])).
% 9.61/3.47  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.47  tff(c_18758, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_18748, c_12])).
% 9.61/3.47  tff(c_18620, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18614, c_18614, c_14386])).
% 9.61/3.47  tff(c_18768, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_18758, c_18620])).
% 9.61/3.47  tff(c_18604, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_16217])).
% 9.61/3.47  tff(c_18747, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18614, c_18614, c_18614, c_18614, c_18614, c_18604])).
% 9.61/3.47  tff(c_18772, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18768, c_18747])).
% 9.61/3.47  tff(c_18779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18622, c_18772])).
% 9.61/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.47  
% 9.61/3.47  Inference rules
% 9.61/3.47  ----------------------
% 9.61/3.47  #Ref     : 0
% 9.61/3.47  #Sup     : 3916
% 9.61/3.47  #Fact    : 0
% 9.61/3.47  #Define  : 0
% 9.61/3.47  #Split   : 34
% 9.61/3.47  #Chain   : 0
% 9.61/3.47  #Close   : 0
% 9.61/3.47  
% 9.61/3.47  Ordering : KBO
% 9.61/3.47  
% 9.61/3.47  Simplification rules
% 9.61/3.47  ----------------------
% 9.61/3.47  #Subsume      : 1023
% 9.61/3.47  #Demod        : 3926
% 9.61/3.47  #Tautology    : 1660
% 9.61/3.47  #SimpNegUnit  : 129
% 9.61/3.47  #BackRed      : 109
% 9.61/3.47  
% 9.61/3.47  #Partial instantiations: 0
% 9.61/3.47  #Strategies tried      : 1
% 9.61/3.47  
% 9.61/3.47  Timing (in seconds)
% 9.61/3.47  ----------------------
% 9.61/3.48  Preprocessing        : 0.37
% 9.61/3.48  Parsing              : 0.20
% 9.61/3.48  CNF conversion       : 0.03
% 9.61/3.48  Main loop            : 2.25
% 9.61/3.48  Inferencing          : 0.70
% 9.61/3.48  Reduction            : 0.84
% 9.61/3.48  Demodulation         : 0.62
% 9.61/3.48  BG Simplification    : 0.06
% 9.61/3.48  Subsumption          : 0.48
% 9.61/3.48  Abstraction          : 0.08
% 9.61/3.48  MUC search           : 0.00
% 9.61/3.48  Cooper               : 0.00
% 9.61/3.48  Total                : 2.69
% 9.61/3.48  Index Insertion      : 0.00
% 9.61/3.48  Index Deletion       : 0.00
% 9.61/3.48  Index Matching       : 0.00
% 9.61/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
