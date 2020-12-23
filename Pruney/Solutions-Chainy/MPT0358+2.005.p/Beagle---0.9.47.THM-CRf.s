%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:00 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 653 expanded)
%              Number of leaves         :   44 ( 236 expanded)
%              Depth                    :   19
%              Number of atoms          :  168 ( 827 expanded)
%              Number of equality atoms :   79 ( 516 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_73,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_118,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_79,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_83,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_115,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_86,plain,(
    ! [A_44] : k1_subset_1(A_44) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_100,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_subset_1('#skF_8') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_101,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_100])).

tff(c_147,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_50,plain,(
    ! [A_26] : r1_tarski(k1_xboole_0,A_26) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_151,plain,(
    ! [A_26] : r1_tarski('#skF_9',A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_50])).

tff(c_94,plain,
    ( k1_subset_1('#skF_8') != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_102,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_94])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_147,c_102])).

tff(c_217,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k1_tarski(A_40),B_41)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_92,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_90,plain,(
    ! [A_47] : ~ v1_xboole_0(k1_zfmisc_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_618,plain,(
    ! [B_111,A_112] :
      ( r2_hidden(B_111,A_112)
      | ~ m1_subset_1(B_111,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_62,plain,(
    ! [C_39,A_35] :
      ( r1_tarski(C_39,A_35)
      | ~ r2_hidden(C_39,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_640,plain,(
    ! [B_111,A_35] :
      ( r1_tarski(B_111,A_35)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_35))
      | v1_xboole_0(k1_zfmisc_1(A_35)) ) ),
    inference(resolution,[status(thm)],[c_618,c_62])).

tff(c_655,plain,(
    ! [B_113,A_114] :
      ( r1_tarski(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_114)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_640])).

tff(c_680,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_92,c_655])).

tff(c_46,plain,(
    ! [A_22,C_24,B_23] :
      ( r1_tarski(A_22,C_24)
      | ~ r1_tarski(B_23,C_24)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_712,plain,(
    ! [A_118] :
      ( r1_tarski(A_118,'#skF_8')
      | ~ r1_tarski(A_118,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_680,c_46])).

tff(c_960,plain,(
    ! [A_128] :
      ( r1_tarski(k1_tarski(A_128),'#skF_8')
      | ~ r2_hidden(A_128,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_712])).

tff(c_74,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | ~ r1_tarski(k1_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1022,plain,(
    ! [A_132] :
      ( r2_hidden(A_132,'#skF_8')
      | ~ r2_hidden(A_132,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_960,c_74])).

tff(c_1032,plain,
    ( r2_hidden('#skF_1'('#skF_9'),'#skF_8')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_1022])).

tff(c_1073,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1032])).

tff(c_54,plain,(
    ! [A_28] : k5_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_58,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_332,plain,(
    ! [A_74,B_75] :
      ( k2_xboole_0(A_74,B_75) = B_75
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_343,plain,(
    ! [B_17] : k2_xboole_0(B_17,B_17) = B_17 ),
    inference(resolution,[status(thm)],[c_40,c_332])).

tff(c_798,plain,(
    ! [A_123,B_124] : k5_xboole_0(k5_xboole_0(A_123,B_124),k2_xboole_0(A_123,B_124)) = k3_xboole_0(A_123,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_834,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_32,A_32)) = k3_xboole_0(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_798])).

tff(c_847,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,A_32) = k3_xboole_0(A_32,A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_834])).

tff(c_1179,plain,(
    ! [A_141,B_142,C_143] : k5_xboole_0(k5_xboole_0(A_141,B_142),C_143) = k5_xboole_0(A_141,k5_xboole_0(B_142,C_143)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1284,plain,(
    ! [A_144,B_145] : k5_xboole_0(A_144,k5_xboole_0(B_145,k5_xboole_0(A_144,B_145))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1179,c_58])).

tff(c_1334,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_32,k3_xboole_0(A_32,A_32))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_847,c_1284])).

tff(c_1358,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,k4_xboole_0(A_32,A_32)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1334])).

tff(c_1391,plain,(
    ! [A_147] : k5_xboole_0(A_147,k5_xboole_0(k1_xboole_0,A_147)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1284])).

tff(c_1483,plain,(
    ! [A_149] : k5_xboole_0(k4_xboole_0(A_149,A_149),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_1391])).

tff(c_1212,plain,(
    ! [A_141,B_142] : k5_xboole_0(A_141,k5_xboole_0(B_142,k5_xboole_0(A_141,B_142))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1179,c_58])).

tff(c_1488,plain,(
    ! [A_149] : k5_xboole_0(k4_xboole_0(A_149,A_149),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1483,c_1212])).

tff(c_1511,plain,(
    ! [A_149] : k4_xboole_0(A_149,A_149) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_1488])).

tff(c_24,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden('#skF_2'(A_7,B_8,C_9),A_7)
      | r2_hidden('#skF_3'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4562,plain,(
    ! [A_227,B_228,C_229] :
      ( ~ r2_hidden('#skF_2'(A_227,B_228,C_229),B_228)
      | r2_hidden('#skF_3'(A_227,B_228,C_229),C_229)
      | k4_xboole_0(A_227,B_228) = C_229 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4565,plain,(
    ! [A_7,C_9] :
      ( r2_hidden('#skF_3'(A_7,A_7,C_9),C_9)
      | k4_xboole_0(A_7,A_7) = C_9 ) ),
    inference(resolution,[status(thm)],[c_24,c_4562])).

tff(c_4584,plain,(
    ! [A_230,C_231] :
      ( r2_hidden('#skF_3'(A_230,A_230,C_231),C_231)
      | k1_xboole_0 = C_231 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_4565])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4648,plain,(
    ! [C_232] :
      ( ~ v1_xboole_0(C_232)
      | k1_xboole_0 = C_232 ) ),
    inference(resolution,[status(thm)],[c_4584,c_4])).

tff(c_4651,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1073,c_4648])).

tff(c_4658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_4651])).

tff(c_4660,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1032])).

tff(c_4659,plain,(
    r2_hidden('#skF_1'('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1032])).

tff(c_4747,plain,(
    ! [A_237,B_238,C_239] : k5_xboole_0(k5_xboole_0(A_237,B_238),C_239) = k5_xboole_0(A_237,k5_xboole_0(B_238,C_239)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5224,plain,(
    ! [A_252,B_253] : k5_xboole_0(A_252,k5_xboole_0(B_253,k5_xboole_0(A_252,B_253))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4747,c_58])).

tff(c_4853,plain,(
    ! [A_240,C_241] : k5_xboole_0(A_240,k5_xboole_0(A_240,C_241)) = k5_xboole_0(k1_xboole_0,C_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4747])).

tff(c_4910,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,A_32) = k5_xboole_0(A_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4853])).

tff(c_4922,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4910])).

tff(c_4832,plain,(
    ! [A_32,C_239] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_239)) = k5_xboole_0(k1_xboole_0,C_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4747])).

tff(c_4924,plain,(
    ! [A_32,C_239] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_239)) = C_239 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4922,c_4832])).

tff(c_5232,plain,(
    ! [B_253,A_252] : k5_xboole_0(B_253,k5_xboole_0(A_252,B_253)) = k5_xboole_0(A_252,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5224,c_4924])).

tff(c_5306,plain,(
    ! [B_253,A_252] : k5_xboole_0(B_253,k5_xboole_0(A_252,B_253)) = A_252 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5232])).

tff(c_56,plain,(
    ! [A_29,B_30,C_31] : k5_xboole_0(k5_xboole_0(A_29,B_30),C_31) = k5_xboole_0(A_29,k5_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5325,plain,(
    ! [B_254,A_255] : k5_xboole_0(B_254,k5_xboole_0(A_255,B_254)) = A_255 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5232])).

tff(c_5334,plain,(
    ! [B_254,A_255] : k5_xboole_0(B_254,A_255) = k5_xboole_0(A_255,B_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_5325,c_4924])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_706,plain,(
    k2_xboole_0('#skF_9','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_680,c_44])).

tff(c_816,plain,(
    k5_xboole_0(k5_xboole_0('#skF_9','#skF_8'),'#skF_8') = k3_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_798])).

tff(c_843,plain,(
    k5_xboole_0(k5_xboole_0('#skF_9','#skF_8'),'#skF_8') = k3_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_816])).

tff(c_6272,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5306,c_56,c_5334,c_843])).

tff(c_1033,plain,(
    ! [A_133,B_134] :
      ( k4_xboole_0(A_133,B_134) = k3_subset_1(A_133,B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1058,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_92,c_1033])).

tff(c_477,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_492,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_477])).

tff(c_5077,plain,(
    ! [A_246,C_247] : k5_xboole_0(A_246,k5_xboole_0(A_246,C_247)) = C_247 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4922,c_4832])).

tff(c_6086,plain,(
    ! [B_274,A_275] : k5_xboole_0(B_274,k4_xboole_0(B_274,A_275)) = k3_xboole_0(A_275,B_274) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_5077])).

tff(c_6132,plain,(
    k5_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k3_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1058,c_6086])).

tff(c_6145,plain,(
    k5_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6132])).

tff(c_6273,plain,(
    k5_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6272,c_6145])).

tff(c_6316,plain,(
    k5_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_6273,c_5306])).

tff(c_216,plain,(
    r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_342,plain,(
    k2_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_216,c_332])).

tff(c_5361,plain,(
    ! [A_32,C_239] : k5_xboole_0(k5_xboole_0(A_32,C_239),C_239) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_4924,c_5325])).

tff(c_6313,plain,(
    k5_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_6273,c_5361])).

tff(c_60,plain,(
    ! [A_33,B_34] : k5_xboole_0(k5_xboole_0(A_33,B_34),k2_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6429,plain,(
    k5_xboole_0('#skF_8',k2_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9'))) = k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6313,c_60])).

tff(c_6435,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6273,c_342,c_6429])).

tff(c_6634,plain,(
    k5_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k4_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_6435,c_492])).

tff(c_6640,plain,(
    k4_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6316,c_6634])).

tff(c_10,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6721,plain,(
    ! [D_289] :
      ( ~ r2_hidden(D_289,'#skF_9')
      | ~ r2_hidden(D_289,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6640,c_10])).

tff(c_6742,plain,
    ( ~ r2_hidden('#skF_1'('#skF_9'),'#skF_8')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_6721])).

tff(c_6751,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4659,c_6742])).

tff(c_6753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4660,c_6751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:38:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.20  
% 5.69/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.20  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_5 > #skF_4
% 5.69/2.20  
% 5.69/2.20  %Foreground sorts:
% 5.69/2.20  
% 5.69/2.20  
% 5.69/2.20  %Background operators:
% 5.69/2.20  
% 5.69/2.20  
% 5.69/2.20  %Foreground operators:
% 5.69/2.20  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.69/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.69/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.69/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.69/2.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.69/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.69/2.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.69/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.69/2.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.69/2.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.69/2.20  tff('#skF_9', type, '#skF_9': $i).
% 5.69/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.20  tff('#skF_8', type, '#skF_8': $i).
% 5.69/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.69/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.20  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.69/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.69/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.69/2.20  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.69/2.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.69/2.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.69/2.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.69/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.69/2.20  
% 6.09/2.22  tff(f_111, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 6.09/2.22  tff(f_125, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 6.09/2.22  tff(f_73, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.09/2.22  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.09/2.22  tff(f_96, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.09/2.22  tff(f_118, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.09/2.22  tff(f_109, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.09/2.22  tff(f_92, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.09/2.22  tff(f_69, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.09/2.22  tff(f_79, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.09/2.22  tff(f_83, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.09/2.22  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.09/2.22  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.09/2.22  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.09/2.22  tff(f_85, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 6.09/2.22  tff(f_81, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.09/2.22  tff(f_43, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.09/2.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.09/2.22  tff(f_115, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.09/2.22  tff(c_86, plain, (![A_44]: (k1_subset_1(A_44)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.09/2.22  tff(c_100, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_subset_1('#skF_8')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.09/2.22  tff(c_101, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_100])).
% 6.09/2.22  tff(c_147, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_101])).
% 6.09/2.22  tff(c_50, plain, (![A_26]: (r1_tarski(k1_xboole_0, A_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.09/2.22  tff(c_151, plain, (![A_26]: (r1_tarski('#skF_9', A_26))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_50])).
% 6.09/2.22  tff(c_94, plain, (k1_subset_1('#skF_8')!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.09/2.22  tff(c_102, plain, (k1_xboole_0!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_94])).
% 6.09/2.22  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_147, c_102])).
% 6.09/2.22  tff(c_217, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_101])).
% 6.09/2.22  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.09/2.22  tff(c_76, plain, (![A_40, B_41]: (r1_tarski(k1_tarski(A_40), B_41) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.09/2.22  tff(c_92, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.09/2.22  tff(c_90, plain, (![A_47]: (~v1_xboole_0(k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.09/2.22  tff(c_618, plain, (![B_111, A_112]: (r2_hidden(B_111, A_112) | ~m1_subset_1(B_111, A_112) | v1_xboole_0(A_112))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.09/2.22  tff(c_62, plain, (![C_39, A_35]: (r1_tarski(C_39, A_35) | ~r2_hidden(C_39, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.09/2.22  tff(c_640, plain, (![B_111, A_35]: (r1_tarski(B_111, A_35) | ~m1_subset_1(B_111, k1_zfmisc_1(A_35)) | v1_xboole_0(k1_zfmisc_1(A_35)))), inference(resolution, [status(thm)], [c_618, c_62])).
% 6.09/2.22  tff(c_655, plain, (![B_113, A_114]: (r1_tarski(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(A_114)))), inference(negUnitSimplification, [status(thm)], [c_90, c_640])).
% 6.09/2.22  tff(c_680, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_92, c_655])).
% 6.09/2.22  tff(c_46, plain, (![A_22, C_24, B_23]: (r1_tarski(A_22, C_24) | ~r1_tarski(B_23, C_24) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.09/2.22  tff(c_712, plain, (![A_118]: (r1_tarski(A_118, '#skF_8') | ~r1_tarski(A_118, '#skF_9'))), inference(resolution, [status(thm)], [c_680, c_46])).
% 6.09/2.22  tff(c_960, plain, (![A_128]: (r1_tarski(k1_tarski(A_128), '#skF_8') | ~r2_hidden(A_128, '#skF_9'))), inference(resolution, [status(thm)], [c_76, c_712])).
% 6.09/2.22  tff(c_74, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | ~r1_tarski(k1_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.09/2.22  tff(c_1022, plain, (![A_132]: (r2_hidden(A_132, '#skF_8') | ~r2_hidden(A_132, '#skF_9'))), inference(resolution, [status(thm)], [c_960, c_74])).
% 6.09/2.22  tff(c_1032, plain, (r2_hidden('#skF_1'('#skF_9'), '#skF_8') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_6, c_1022])).
% 6.09/2.22  tff(c_1073, plain, (v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1032])).
% 6.09/2.22  tff(c_54, plain, (![A_28]: (k5_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.09/2.22  tff(c_58, plain, (![A_32]: (k5_xboole_0(A_32, A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.09/2.22  tff(c_42, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.09/2.22  tff(c_40, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.09/2.22  tff(c_332, plain, (![A_74, B_75]: (k2_xboole_0(A_74, B_75)=B_75 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.09/2.22  tff(c_343, plain, (![B_17]: (k2_xboole_0(B_17, B_17)=B_17)), inference(resolution, [status(thm)], [c_40, c_332])).
% 6.09/2.22  tff(c_798, plain, (![A_123, B_124]: (k5_xboole_0(k5_xboole_0(A_123, B_124), k2_xboole_0(A_123, B_124))=k3_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.09/2.22  tff(c_834, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_32, A_32))=k3_xboole_0(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_58, c_798])).
% 6.09/2.22  tff(c_847, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, A_32)=k3_xboole_0(A_32, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_834])).
% 6.09/2.22  tff(c_1179, plain, (![A_141, B_142, C_143]: (k5_xboole_0(k5_xboole_0(A_141, B_142), C_143)=k5_xboole_0(A_141, k5_xboole_0(B_142, C_143)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.09/2.22  tff(c_1284, plain, (![A_144, B_145]: (k5_xboole_0(A_144, k5_xboole_0(B_145, k5_xboole_0(A_144, B_145)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1179, c_58])).
% 6.09/2.22  tff(c_1334, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_32, k3_xboole_0(A_32, A_32)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_847, c_1284])).
% 6.09/2.22  tff(c_1358, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, k4_xboole_0(A_32, A_32))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1334])).
% 6.09/2.22  tff(c_1391, plain, (![A_147]: (k5_xboole_0(A_147, k5_xboole_0(k1_xboole_0, A_147))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_1284])).
% 6.09/2.22  tff(c_1483, plain, (![A_149]: (k5_xboole_0(k4_xboole_0(A_149, A_149), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1358, c_1391])).
% 6.09/2.22  tff(c_1212, plain, (![A_141, B_142]: (k5_xboole_0(A_141, k5_xboole_0(B_142, k5_xboole_0(A_141, B_142)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1179, c_58])).
% 6.09/2.22  tff(c_1488, plain, (![A_149]: (k5_xboole_0(k4_xboole_0(A_149, A_149), k5_xboole_0(k1_xboole_0, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1483, c_1212])).
% 6.09/2.22  tff(c_1511, plain, (![A_149]: (k4_xboole_0(A_149, A_149)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_1488])).
% 6.09/2.22  tff(c_24, plain, (![A_7, B_8, C_9]: (r2_hidden('#skF_2'(A_7, B_8, C_9), A_7) | r2_hidden('#skF_3'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.09/2.22  tff(c_4562, plain, (![A_227, B_228, C_229]: (~r2_hidden('#skF_2'(A_227, B_228, C_229), B_228) | r2_hidden('#skF_3'(A_227, B_228, C_229), C_229) | k4_xboole_0(A_227, B_228)=C_229)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.09/2.22  tff(c_4565, plain, (![A_7, C_9]: (r2_hidden('#skF_3'(A_7, A_7, C_9), C_9) | k4_xboole_0(A_7, A_7)=C_9)), inference(resolution, [status(thm)], [c_24, c_4562])).
% 6.09/2.22  tff(c_4584, plain, (![A_230, C_231]: (r2_hidden('#skF_3'(A_230, A_230, C_231), C_231) | k1_xboole_0=C_231)), inference(demodulation, [status(thm), theory('equality')], [c_1511, c_4565])).
% 6.09/2.22  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.09/2.22  tff(c_4648, plain, (![C_232]: (~v1_xboole_0(C_232) | k1_xboole_0=C_232)), inference(resolution, [status(thm)], [c_4584, c_4])).
% 6.09/2.22  tff(c_4651, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1073, c_4648])).
% 6.09/2.22  tff(c_4658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_4651])).
% 6.09/2.22  tff(c_4660, plain, (~v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_1032])).
% 6.09/2.22  tff(c_4659, plain, (r2_hidden('#skF_1'('#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_1032])).
% 6.09/2.22  tff(c_4747, plain, (![A_237, B_238, C_239]: (k5_xboole_0(k5_xboole_0(A_237, B_238), C_239)=k5_xboole_0(A_237, k5_xboole_0(B_238, C_239)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.09/2.22  tff(c_5224, plain, (![A_252, B_253]: (k5_xboole_0(A_252, k5_xboole_0(B_253, k5_xboole_0(A_252, B_253)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4747, c_58])).
% 6.09/2.22  tff(c_4853, plain, (![A_240, C_241]: (k5_xboole_0(A_240, k5_xboole_0(A_240, C_241))=k5_xboole_0(k1_xboole_0, C_241))), inference(superposition, [status(thm), theory('equality')], [c_58, c_4747])).
% 6.09/2.22  tff(c_4910, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, A_32)=k5_xboole_0(A_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_4853])).
% 6.09/2.22  tff(c_4922, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4910])).
% 6.09/2.22  tff(c_4832, plain, (![A_32, C_239]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_239))=k5_xboole_0(k1_xboole_0, C_239))), inference(superposition, [status(thm), theory('equality')], [c_58, c_4747])).
% 6.09/2.22  tff(c_4924, plain, (![A_32, C_239]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_239))=C_239)), inference(demodulation, [status(thm), theory('equality')], [c_4922, c_4832])).
% 6.09/2.22  tff(c_5232, plain, (![B_253, A_252]: (k5_xboole_0(B_253, k5_xboole_0(A_252, B_253))=k5_xboole_0(A_252, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5224, c_4924])).
% 6.09/2.22  tff(c_5306, plain, (![B_253, A_252]: (k5_xboole_0(B_253, k5_xboole_0(A_252, B_253))=A_252)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5232])).
% 6.09/2.22  tff(c_56, plain, (![A_29, B_30, C_31]: (k5_xboole_0(k5_xboole_0(A_29, B_30), C_31)=k5_xboole_0(A_29, k5_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.09/2.22  tff(c_5325, plain, (![B_254, A_255]: (k5_xboole_0(B_254, k5_xboole_0(A_255, B_254))=A_255)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5232])).
% 6.09/2.22  tff(c_5334, plain, (![B_254, A_255]: (k5_xboole_0(B_254, A_255)=k5_xboole_0(A_255, B_254))), inference(superposition, [status(thm), theory('equality')], [c_5325, c_4924])).
% 6.09/2.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.09/2.22  tff(c_44, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.09/2.22  tff(c_706, plain, (k2_xboole_0('#skF_9', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_680, c_44])).
% 6.09/2.22  tff(c_816, plain, (k5_xboole_0(k5_xboole_0('#skF_9', '#skF_8'), '#skF_8')=k3_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_706, c_798])).
% 6.09/2.22  tff(c_843, plain, (k5_xboole_0(k5_xboole_0('#skF_9', '#skF_8'), '#skF_8')=k3_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_816])).
% 6.09/2.22  tff(c_6272, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5306, c_56, c_5334, c_843])).
% 6.09/2.22  tff(c_1033, plain, (![A_133, B_134]: (k4_xboole_0(A_133, B_134)=k3_subset_1(A_133, B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.09/2.22  tff(c_1058, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_92, c_1033])).
% 6.09/2.22  tff(c_477, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.09/2.22  tff(c_492, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_477])).
% 6.09/2.22  tff(c_5077, plain, (![A_246, C_247]: (k5_xboole_0(A_246, k5_xboole_0(A_246, C_247))=C_247)), inference(demodulation, [status(thm), theory('equality')], [c_4922, c_4832])).
% 6.09/2.22  tff(c_6086, plain, (![B_274, A_275]: (k5_xboole_0(B_274, k4_xboole_0(B_274, A_275))=k3_xboole_0(A_275, B_274))), inference(superposition, [status(thm), theory('equality')], [c_492, c_5077])).
% 6.09/2.22  tff(c_6132, plain, (k5_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k3_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1058, c_6086])).
% 6.09/2.22  tff(c_6145, plain, (k5_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k3_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6132])).
% 6.09/2.22  tff(c_6273, plain, (k5_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6272, c_6145])).
% 6.09/2.22  tff(c_6316, plain, (k5_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_6273, c_5306])).
% 6.09/2.22  tff(c_216, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_101])).
% 6.09/2.22  tff(c_342, plain, (k2_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_216, c_332])).
% 6.09/2.22  tff(c_5361, plain, (![A_32, C_239]: (k5_xboole_0(k5_xboole_0(A_32, C_239), C_239)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_4924, c_5325])).
% 6.09/2.22  tff(c_6313, plain, (k5_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_6273, c_5361])).
% 6.09/2.22  tff(c_60, plain, (![A_33, B_34]: (k5_xboole_0(k5_xboole_0(A_33, B_34), k2_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.09/2.22  tff(c_6429, plain, (k5_xboole_0('#skF_8', k2_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9')))=k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6313, c_60])).
% 6.09/2.22  tff(c_6435, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6273, c_342, c_6429])).
% 6.09/2.22  tff(c_6634, plain, (k5_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k4_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6435, c_492])).
% 6.09/2.22  tff(c_6640, plain, (k4_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6316, c_6634])).
% 6.09/2.22  tff(c_10, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.09/2.22  tff(c_6721, plain, (![D_289]: (~r2_hidden(D_289, '#skF_9') | ~r2_hidden(D_289, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6640, c_10])).
% 6.09/2.22  tff(c_6742, plain, (~r2_hidden('#skF_1'('#skF_9'), '#skF_8') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_6, c_6721])).
% 6.09/2.22  tff(c_6751, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4659, c_6742])).
% 6.09/2.22  tff(c_6753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4660, c_6751])).
% 6.09/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.22  
% 6.09/2.22  Inference rules
% 6.09/2.22  ----------------------
% 6.09/2.22  #Ref     : 0
% 6.09/2.22  #Sup     : 1586
% 6.09/2.22  #Fact    : 0
% 6.09/2.22  #Define  : 0
% 6.09/2.22  #Split   : 7
% 6.09/2.22  #Chain   : 0
% 6.09/2.22  #Close   : 0
% 6.09/2.22  
% 6.09/2.22  Ordering : KBO
% 6.09/2.22  
% 6.09/2.22  Simplification rules
% 6.09/2.22  ----------------------
% 6.09/2.22  #Subsume      : 90
% 6.09/2.22  #Demod        : 1048
% 6.09/2.22  #Tautology    : 933
% 6.09/2.22  #SimpNegUnit  : 28
% 6.09/2.22  #BackRed      : 23
% 6.09/2.22  
% 6.09/2.22  #Partial instantiations: 0
% 6.09/2.22  #Strategies tried      : 1
% 6.09/2.22  
% 6.09/2.22  Timing (in seconds)
% 6.09/2.22  ----------------------
% 6.09/2.23  Preprocessing        : 0.37
% 6.09/2.23  Parsing              : 0.19
% 6.09/2.23  CNF conversion       : 0.03
% 6.09/2.23  Main loop            : 1.05
% 6.09/2.23  Inferencing          : 0.33
% 6.09/2.23  Reduction            : 0.42
% 6.09/2.23  Demodulation         : 0.32
% 6.09/2.23  BG Simplification    : 0.04
% 6.09/2.23  Subsumption          : 0.18
% 6.09/2.23  Abstraction          : 0.05
% 6.09/2.23  MUC search           : 0.00
% 6.09/2.23  Cooper               : 0.00
% 6.09/2.23  Total                : 1.46
% 6.09/2.23  Index Insertion      : 0.00
% 6.09/2.23  Index Deletion       : 0.00
% 6.09/2.23  Index Matching       : 0.00
% 6.09/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
