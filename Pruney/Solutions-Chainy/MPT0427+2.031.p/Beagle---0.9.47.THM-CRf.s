%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:00 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 411 expanded)
%              Number of leaves         :   33 ( 145 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 ( 815 expanded)
%              Number of equality atoms :   49 ( 172 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_54,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_135,plain,(
    ! [A_58,C_59,B_60] :
      ( m1_subset_1(A_58,C_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(C_59))
      | ~ r2_hidden(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_159,plain,(
    ! [A_63] :
      ( m1_subset_1(A_63,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_135])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_167,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,'#skF_3')
      | ~ r2_hidden(A_64,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_159,c_30])).

tff(c_177,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_167])).

tff(c_197,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_339,plain,(
    ! [A_86,B_87] :
      ( k6_setfam_1(A_86,B_87) = k1_setfam_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_353,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_339])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_201,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_197,c_12])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( k8_setfam_1(A_17,B_18) = k6_setfam_1(A_17,B_18)
      | k1_xboole_0 = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_565,plain,(
    ! [A_112,B_113] :
      ( k8_setfam_1(A_112,B_113) = k6_setfam_1(A_112,B_113)
      | B_113 = '#skF_4'
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(A_112))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_24])).

tff(c_592,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_565])).

tff(c_603,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_592])).

tff(c_604,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_603])).

tff(c_107,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_2'(A_50,B_51),A_50)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [A_50] : r1_tarski(A_50,A_50) ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_17] :
      ( k8_setfam_1(A_17,k1_xboole_0) = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ! [A_17] : k8_setfam_1(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_206,plain,(
    ! [A_17] : k8_setfam_1(A_17,'#skF_4') = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_46])).

tff(c_178,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_135])).

tff(c_186,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,'#skF_3')
      | ~ r2_hidden(A_66,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_178,c_30])).

tff(c_196,plain,
    ( r1_tarski('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_186])).

tff(c_275,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_208,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_12])).

tff(c_279,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_275,c_208])).

tff(c_38,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_261,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_38])).

tff(c_296,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_261])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_206,c_296])).

tff(c_307,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_609,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_307])).

tff(c_620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_609])).

tff(c_621,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_603])).

tff(c_623,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_261])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k8_setfam_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_628,plain,
    ( m1_subset_1(k1_setfam_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_26])).

tff(c_632,plain,(
    m1_subset_1(k1_setfam_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_628])).

tff(c_642,plain,(
    r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_632,c_30])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_623,c_642])).

tff(c_649,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_1127,plain,(
    ! [A_167,B_168] :
      ( k6_setfam_1(A_167,B_168) = k1_setfam_1(B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(k1_zfmisc_1(A_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1143,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1127])).

tff(c_1346,plain,(
    ! [A_187,B_188] :
      ( k8_setfam_1(A_187,B_188) = k6_setfam_1(A_187,B_188)
      | k1_xboole_0 = B_188
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k1_zfmisc_1(A_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1369,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_1346])).

tff(c_1384,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1369])).

tff(c_1390,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1384])).

tff(c_76,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_88,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_20,c_76])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,B_36),B_36) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    ! [A_11] : r1_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_65])).

tff(c_96,plain,(
    ! [B_48,A_49] :
      ( ~ r1_xboole_0(B_48,A_49)
      | ~ r1_tarski(B_48,A_49)
      | v1_xboole_0(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    ! [A_11] :
      ( ~ r1_tarski(k1_xboole_0,A_11)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_105,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_99])).

tff(c_1395,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_105])).

tff(c_1403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_1395])).

tff(c_1405,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1384])).

tff(c_40,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_setfam_1(B_29),k1_setfam_1(A_28))
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_651,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_128,plain,(
    ! [C_55,B_56,A_57] :
      ( r2_hidden(C_55,B_56)
      | ~ r2_hidden(C_55,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_986,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_1'(A_152),B_153)
      | ~ r1_tarski(A_152,B_153)
      | v1_xboole_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1026,plain,(
    ! [B_154,A_155] :
      ( ~ v1_xboole_0(B_154)
      | ~ r1_tarski(A_155,B_154)
      | v1_xboole_0(A_155) ) ),
    inference(resolution,[status(thm)],[c_986,c_2])).

tff(c_1053,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1026])).

tff(c_1067,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_1053])).

tff(c_1069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_1067])).

tff(c_1071,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_1144,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1127])).

tff(c_1372,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_1346])).

tff(c_1386,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_1372])).

tff(c_1406,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1386])).

tff(c_1412,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_105])).

tff(c_1420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1071,c_1412])).

tff(c_1421,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1386])).

tff(c_1404,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1384])).

tff(c_1423,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_38])).

tff(c_1443,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_1423])).

tff(c_1446,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_1443])).

tff(c_1452,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1446])).

tff(c_1454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1405,c_1452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  
% 3.40/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.40/1.54  
% 3.40/1.54  %Foreground sorts:
% 3.40/1.54  
% 3.40/1.54  
% 3.40/1.54  %Background operators:
% 3.40/1.54  
% 3.40/1.54  
% 3.40/1.54  %Foreground operators:
% 3.40/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.40/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.54  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.40/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.40/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.54  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.40/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.40/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.40/1.54  
% 3.40/1.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.40/1.56  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.40/1.56  tff(f_85, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.40/1.56  tff(f_79, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.40/1.56  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.40/1.56  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.40/1.56  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.40/1.56  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.40/1.56  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.40/1.56  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.40/1.56  tff(f_44, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.40/1.56  tff(f_54, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.40/1.56  tff(f_52, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.40/1.56  tff(f_91, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.40/1.56  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.56  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.40/1.56  tff(c_135, plain, (![A_58, C_59, B_60]: (m1_subset_1(A_58, C_59) | ~m1_subset_1(B_60, k1_zfmisc_1(C_59)) | ~r2_hidden(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.56  tff(c_159, plain, (![A_63]: (m1_subset_1(A_63, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_63, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_135])).
% 3.40/1.56  tff(c_30, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.56  tff(c_167, plain, (![A_64]: (r1_tarski(A_64, '#skF_3') | ~r2_hidden(A_64, '#skF_4'))), inference(resolution, [status(thm)], [c_159, c_30])).
% 3.40/1.56  tff(c_177, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_167])).
% 3.40/1.56  tff(c_197, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_177])).
% 3.40/1.56  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.40/1.56  tff(c_339, plain, (![A_86, B_87]: (k6_setfam_1(A_86, B_87)=k1_setfam_1(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_86))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.40/1.56  tff(c_353, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_339])).
% 3.40/1.56  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.56  tff(c_201, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_197, c_12])).
% 3.40/1.56  tff(c_24, plain, (![A_17, B_18]: (k8_setfam_1(A_17, B_18)=k6_setfam_1(A_17, B_18) | k1_xboole_0=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.56  tff(c_565, plain, (![A_112, B_113]: (k8_setfam_1(A_112, B_113)=k6_setfam_1(A_112, B_113) | B_113='#skF_4' | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(A_112))))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_24])).
% 3.40/1.56  tff(c_592, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_565])).
% 3.40/1.56  tff(c_603, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_353, c_592])).
% 3.40/1.56  tff(c_604, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_603])).
% 3.40/1.56  tff(c_107, plain, (![A_50, B_51]: (r2_hidden('#skF_2'(A_50, B_51), A_50) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.56  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.56  tff(c_115, plain, (![A_50]: (r1_tarski(A_50, A_50))), inference(resolution, [status(thm)], [c_107, c_8])).
% 3.40/1.56  tff(c_20, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.40/1.56  tff(c_22, plain, (![A_17]: (k8_setfam_1(A_17, k1_xboole_0)=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.56  tff(c_46, plain, (![A_17]: (k8_setfam_1(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 3.40/1.56  tff(c_206, plain, (![A_17]: (k8_setfam_1(A_17, '#skF_4')=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_46])).
% 3.40/1.56  tff(c_178, plain, (![A_65]: (m1_subset_1(A_65, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_135])).
% 3.40/1.56  tff(c_186, plain, (![A_66]: (r1_tarski(A_66, '#skF_3') | ~r2_hidden(A_66, '#skF_5'))), inference(resolution, [status(thm)], [c_178, c_30])).
% 3.40/1.56  tff(c_196, plain, (r1_tarski('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_186])).
% 3.40/1.56  tff(c_275, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_196])).
% 3.40/1.56  tff(c_208, plain, (![A_10]: (A_10='#skF_4' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_12])).
% 3.40/1.56  tff(c_279, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_275, c_208])).
% 3.40/1.56  tff(c_38, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.40/1.56  tff(c_261, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_38])).
% 3.40/1.56  tff(c_296, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_261])).
% 3.40/1.56  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_206, c_296])).
% 3.40/1.56  tff(c_307, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_196])).
% 3.40/1.56  tff(c_609, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_604, c_307])).
% 3.40/1.56  tff(c_620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_609])).
% 3.40/1.56  tff(c_621, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_603])).
% 3.40/1.56  tff(c_623, plain, (~r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_621, c_261])).
% 3.40/1.56  tff(c_26, plain, (![A_19, B_20]: (m1_subset_1(k8_setfam_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.40/1.56  tff(c_628, plain, (m1_subset_1(k1_setfam_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_621, c_26])).
% 3.40/1.56  tff(c_632, plain, (m1_subset_1(k1_setfam_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_628])).
% 3.40/1.56  tff(c_642, plain, (r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_632, c_30])).
% 3.40/1.56  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_623, c_642])).
% 3.40/1.56  tff(c_649, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_177])).
% 3.40/1.56  tff(c_1127, plain, (![A_167, B_168]: (k6_setfam_1(A_167, B_168)=k1_setfam_1(B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(k1_zfmisc_1(A_167))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.40/1.56  tff(c_1143, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1127])).
% 3.40/1.56  tff(c_1346, plain, (![A_187, B_188]: (k8_setfam_1(A_187, B_188)=k6_setfam_1(A_187, B_188) | k1_xboole_0=B_188 | ~m1_subset_1(B_188, k1_zfmisc_1(k1_zfmisc_1(A_187))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.56  tff(c_1369, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_1346])).
% 3.40/1.56  tff(c_1384, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1369])).
% 3.40/1.56  tff(c_1390, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1384])).
% 3.40/1.56  tff(c_76, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.56  tff(c_88, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_20, c_76])).
% 3.40/1.56  tff(c_14, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.40/1.56  tff(c_65, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, B_36), B_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.40/1.56  tff(c_68, plain, (![A_11]: (r1_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_65])).
% 3.40/1.56  tff(c_96, plain, (![B_48, A_49]: (~r1_xboole_0(B_48, A_49) | ~r1_tarski(B_48, A_49) | v1_xboole_0(B_48))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.56  tff(c_99, plain, (![A_11]: (~r1_tarski(k1_xboole_0, A_11) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_68, c_96])).
% 3.40/1.56  tff(c_105, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_99])).
% 3.40/1.56  tff(c_1395, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_105])).
% 3.40/1.56  tff(c_1403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_649, c_1395])).
% 3.40/1.56  tff(c_1405, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1384])).
% 3.40/1.56  tff(c_40, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.40/1.56  tff(c_36, plain, (![B_29, A_28]: (r1_tarski(k1_setfam_1(B_29), k1_setfam_1(A_28)) | k1_xboole_0=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.40/1.56  tff(c_651, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_196])).
% 3.40/1.56  tff(c_128, plain, (![C_55, B_56, A_57]: (r2_hidden(C_55, B_56) | ~r2_hidden(C_55, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.56  tff(c_986, plain, (![A_152, B_153]: (r2_hidden('#skF_1'(A_152), B_153) | ~r1_tarski(A_152, B_153) | v1_xboole_0(A_152))), inference(resolution, [status(thm)], [c_4, c_128])).
% 3.40/1.56  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.56  tff(c_1026, plain, (![B_154, A_155]: (~v1_xboole_0(B_154) | ~r1_tarski(A_155, B_154) | v1_xboole_0(A_155))), inference(resolution, [status(thm)], [c_986, c_2])).
% 3.40/1.56  tff(c_1053, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_1026])).
% 3.40/1.56  tff(c_1067, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_651, c_1053])).
% 3.40/1.56  tff(c_1069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_649, c_1067])).
% 3.40/1.56  tff(c_1071, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_196])).
% 3.40/1.56  tff(c_1144, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_1127])).
% 3.40/1.56  tff(c_1372, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_1346])).
% 3.40/1.56  tff(c_1386, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1144, c_1372])).
% 3.40/1.56  tff(c_1406, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1386])).
% 3.40/1.56  tff(c_1412, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1406, c_105])).
% 3.40/1.56  tff(c_1420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1071, c_1412])).
% 3.40/1.56  tff(c_1421, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_1386])).
% 3.40/1.56  tff(c_1404, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_1384])).
% 3.40/1.56  tff(c_1423, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_38])).
% 3.40/1.56  tff(c_1443, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1421, c_1423])).
% 3.40/1.56  tff(c_1446, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_1443])).
% 3.40/1.56  tff(c_1452, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1446])).
% 3.40/1.56  tff(c_1454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1405, c_1452])).
% 3.40/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.56  
% 3.40/1.56  Inference rules
% 3.40/1.56  ----------------------
% 3.40/1.56  #Ref     : 0
% 3.40/1.56  #Sup     : 283
% 3.40/1.56  #Fact    : 0
% 3.40/1.56  #Define  : 0
% 3.40/1.56  #Split   : 9
% 3.40/1.56  #Chain   : 0
% 3.40/1.56  #Close   : 0
% 3.40/1.56  
% 3.40/1.56  Ordering : KBO
% 3.40/1.56  
% 3.40/1.56  Simplification rules
% 3.40/1.56  ----------------------
% 3.40/1.56  #Subsume      : 17
% 3.40/1.56  #Demod        : 171
% 3.40/1.56  #Tautology    : 104
% 3.40/1.56  #SimpNegUnit  : 11
% 3.40/1.56  #BackRed      : 80
% 3.40/1.56  
% 3.40/1.56  #Partial instantiations: 0
% 3.40/1.56  #Strategies tried      : 1
% 3.40/1.56  
% 3.40/1.56  Timing (in seconds)
% 3.40/1.56  ----------------------
% 3.40/1.56  Preprocessing        : 0.30
% 3.40/1.56  Parsing              : 0.16
% 3.40/1.56  CNF conversion       : 0.02
% 3.40/1.56  Main loop            : 0.48
% 3.40/1.56  Inferencing          : 0.17
% 3.40/1.56  Reduction            : 0.15
% 3.40/1.56  Demodulation         : 0.10
% 3.40/1.56  BG Simplification    : 0.02
% 3.40/1.56  Subsumption          : 0.09
% 3.40/1.56  Abstraction          : 0.03
% 3.40/1.56  MUC search           : 0.00
% 3.40/1.56  Cooper               : 0.00
% 3.40/1.56  Total                : 0.83
% 3.40/1.56  Index Insertion      : 0.00
% 3.40/1.56  Index Deletion       : 0.00
% 3.40/1.56  Index Matching       : 0.00
% 3.40/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
