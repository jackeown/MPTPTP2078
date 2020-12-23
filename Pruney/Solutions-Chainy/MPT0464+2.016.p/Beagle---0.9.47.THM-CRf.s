%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:45 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 140 expanded)
%              Number of leaves         :   41 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 235 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_135,plain,(
    ! [A_83,B_84] : k1_enumset1(A_83,A_83,B_84) = k2_tarski(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_147,plain,(
    ! [B_84,A_83] : r2_hidden(B_84,k2_tarski(A_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_10])).

tff(c_54,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_308,plain,(
    ! [A_123,B_124,C_125] :
      ( r1_tarski(k2_tarski(A_123,B_124),C_125)
      | ~ r2_hidden(B_124,C_125)
      | ~ r2_hidden(A_123,C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_323,plain,(
    ! [A_19,C_125] :
      ( r1_tarski(k1_tarski(A_19),C_125)
      | ~ r2_hidden(A_19,C_125)
      | ~ r2_hidden(A_19,C_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_308])).

tff(c_36,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [A_22,B_23,C_24] : k2_enumset1(A_22,A_22,B_23,C_24) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_715,plain,(
    ! [A_205,B_206,C_207,D_208] : k2_xboole_0(k2_tarski(A_205,B_206),k2_tarski(C_207,D_208)) = k2_enumset1(A_205,B_206,C_207,D_208) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_732,plain,(
    ! [A_19,C_207,D_208] : k2_xboole_0(k1_tarski(A_19),k2_tarski(C_207,D_208)) = k2_enumset1(A_19,A_19,C_207,D_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_715])).

tff(c_739,plain,(
    ! [A_209,C_210,D_211] : k2_xboole_0(k1_tarski(A_209),k2_tarski(C_210,D_211)) = k1_enumset1(A_209,C_210,D_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_732])).

tff(c_52,plain,(
    ! [A_39,B_40] : k2_xboole_0(k1_tarski(A_39),B_40) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_753,plain,(
    ! [A_212,C_213,D_214] : k1_enumset1(A_212,C_213,D_214) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_52])).

tff(c_756,plain,(
    ! [A_215,B_216] : k2_tarski(A_215,B_216) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_753])).

tff(c_758,plain,(
    ! [A_19] : k1_tarski(A_19) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_756])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_169,plain,(
    ! [A_92,B_93] : k1_setfam_1(k2_tarski(A_92,B_93)) = k3_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_178,plain,(
    ! [A_19] : k3_xboole_0(A_19,A_19) = k1_setfam_1(k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_169])).

tff(c_181,plain,(
    ! [A_19] : k1_setfam_1(k1_tarski(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_245,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(k1_setfam_1(B_112),k1_setfam_1(A_113))
      | k1_xboole_0 = A_113
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_254,plain,(
    ! [B_112,A_19] :
      ( r1_tarski(k1_setfam_1(B_112),A_19)
      | k1_tarski(A_19) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_19),B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_245])).

tff(c_1241,plain,(
    ! [B_265,A_266] :
      ( r1_tarski(k1_setfam_1(B_265),A_266)
      | ~ r1_tarski(k1_tarski(A_266),B_265) ) ),
    inference(negUnitSimplification,[status(thm)],[c_758,c_254])).

tff(c_1254,plain,(
    ! [C_267,A_268] :
      ( r1_tarski(k1_setfam_1(C_267),A_268)
      | ~ r2_hidden(A_268,C_267) ) ),
    inference(resolution,[status(thm)],[c_323,c_1241])).

tff(c_1402,plain,(
    ! [A_298,B_299,A_300] :
      ( r1_tarski(k3_xboole_0(A_298,B_299),A_300)
      | ~ r2_hidden(A_300,k2_tarski(A_298,B_299)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1254])).

tff(c_1417,plain,(
    ! [A_83,B_84] : r1_tarski(k3_xboole_0(A_83,B_84),B_84) ),
    inference(resolution,[status(thm)],[c_147,c_1402])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,k1_zfmisc_1(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_218,plain,(
    ! [B_103,A_104] :
      ( v1_relat_1(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104))
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_232,plain,(
    ! [A_108,B_109] :
      ( v1_relat_1(A_108)
      | ~ v1_relat_1(B_109)
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_58,c_218])).

tff(c_240,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k3_xboole_0(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_232])).

tff(c_68,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_913,plain,(
    ! [C_229,A_230,B_231] :
      ( r1_tarski(k5_relat_1(C_229,A_230),k5_relat_1(C_229,B_231))
      | ~ r1_tarski(A_230,B_231)
      | ~ v1_relat_1(C_229)
      | ~ v1_relat_1(B_231)
      | ~ v1_relat_1(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_620,plain,(
    ! [C_176,A_177,B_178] :
      ( r1_tarski(k5_relat_1(C_176,A_177),k5_relat_1(C_176,B_178))
      | ~ r1_tarski(A_177,B_178)
      | ~ v1_relat_1(C_176)
      | ~ v1_relat_1(B_178)
      | ~ v1_relat_1(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_272,plain,(
    ! [A_116,B_117,C_118] :
      ( r1_tarski(A_116,k3_xboole_0(B_117,C_118))
      | ~ r1_tarski(A_116,C_118)
      | ~ r1_tarski(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_298,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_272,c_66])).

tff(c_362,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_623,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_620,c_362])).

tff(c_629,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_4,c_623])).

tff(c_633,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_240,c_629])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_633])).

tff(c_638,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_916,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_913,c_638])).

tff(c_922,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_916])).

tff(c_936,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_922])).

tff(c_939,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_240,c_936])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_939])).

tff(c_944,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_922])).

tff(c_1455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1417,c_944])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.69  
% 3.64/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.69  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.64/1.69  
% 3.64/1.69  %Foreground sorts:
% 3.64/1.69  
% 3.64/1.69  
% 3.64/1.69  %Background operators:
% 3.64/1.69  
% 3.64/1.69  
% 3.64/1.69  %Foreground operators:
% 3.64/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.64/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.64/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.64/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.64/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.64/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.64/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.64/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.64/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.64/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.64/1.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.64/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.64/1.69  
% 3.64/1.71  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.64/1.71  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.64/1.71  tff(f_75, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.64/1.71  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.64/1.71  tff(f_70, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.64/1.71  tff(f_58, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.64/1.71  tff(f_52, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.64/1.71  tff(f_73, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.64/1.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.64/1.71  tff(f_85, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.64/1.71  tff(f_115, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 3.64/1.71  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.64/1.71  tff(f_79, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.64/1.71  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.64/1.71  tff(f_104, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 3.64/1.71  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.64/1.71  tff(c_135, plain, (![A_83, B_84]: (k1_enumset1(A_83, A_83, B_84)=k2_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.64/1.71  tff(c_10, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.64/1.71  tff(c_147, plain, (![B_84, A_83]: (r2_hidden(B_84, k2_tarski(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_10])).
% 3.64/1.71  tff(c_54, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.64/1.71  tff(c_34, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.64/1.71  tff(c_308, plain, (![A_123, B_124, C_125]: (r1_tarski(k2_tarski(A_123, B_124), C_125) | ~r2_hidden(B_124, C_125) | ~r2_hidden(A_123, C_125))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.64/1.71  tff(c_323, plain, (![A_19, C_125]: (r1_tarski(k1_tarski(A_19), C_125) | ~r2_hidden(A_19, C_125) | ~r2_hidden(A_19, C_125))), inference(superposition, [status(thm), theory('equality')], [c_34, c_308])).
% 3.64/1.71  tff(c_36, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.64/1.71  tff(c_38, plain, (![A_22, B_23, C_24]: (k2_enumset1(A_22, A_22, B_23, C_24)=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.64/1.71  tff(c_715, plain, (![A_205, B_206, C_207, D_208]: (k2_xboole_0(k2_tarski(A_205, B_206), k2_tarski(C_207, D_208))=k2_enumset1(A_205, B_206, C_207, D_208))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.64/1.71  tff(c_732, plain, (![A_19, C_207, D_208]: (k2_xboole_0(k1_tarski(A_19), k2_tarski(C_207, D_208))=k2_enumset1(A_19, A_19, C_207, D_208))), inference(superposition, [status(thm), theory('equality')], [c_34, c_715])).
% 3.64/1.71  tff(c_739, plain, (![A_209, C_210, D_211]: (k2_xboole_0(k1_tarski(A_209), k2_tarski(C_210, D_211))=k1_enumset1(A_209, C_210, D_211))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_732])).
% 3.64/1.71  tff(c_52, plain, (![A_39, B_40]: (k2_xboole_0(k1_tarski(A_39), B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.64/1.71  tff(c_753, plain, (![A_212, C_213, D_214]: (k1_enumset1(A_212, C_213, D_214)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_739, c_52])).
% 3.64/1.71  tff(c_756, plain, (![A_215, B_216]: (k2_tarski(A_215, B_216)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_753])).
% 3.64/1.71  tff(c_758, plain, (![A_19]: (k1_tarski(A_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_756])).
% 3.64/1.71  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.64/1.71  tff(c_169, plain, (![A_92, B_93]: (k1_setfam_1(k2_tarski(A_92, B_93))=k3_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.64/1.71  tff(c_178, plain, (![A_19]: (k3_xboole_0(A_19, A_19)=k1_setfam_1(k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_169])).
% 3.64/1.71  tff(c_181, plain, (![A_19]: (k1_setfam_1(k1_tarski(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_178])).
% 3.64/1.71  tff(c_245, plain, (![B_112, A_113]: (r1_tarski(k1_setfam_1(B_112), k1_setfam_1(A_113)) | k1_xboole_0=A_113 | ~r1_tarski(A_113, B_112))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.64/1.71  tff(c_254, plain, (![B_112, A_19]: (r1_tarski(k1_setfam_1(B_112), A_19) | k1_tarski(A_19)=k1_xboole_0 | ~r1_tarski(k1_tarski(A_19), B_112))), inference(superposition, [status(thm), theory('equality')], [c_181, c_245])).
% 3.64/1.71  tff(c_1241, plain, (![B_265, A_266]: (r1_tarski(k1_setfam_1(B_265), A_266) | ~r1_tarski(k1_tarski(A_266), B_265))), inference(negUnitSimplification, [status(thm)], [c_758, c_254])).
% 3.64/1.71  tff(c_1254, plain, (![C_267, A_268]: (r1_tarski(k1_setfam_1(C_267), A_268) | ~r2_hidden(A_268, C_267))), inference(resolution, [status(thm)], [c_323, c_1241])).
% 3.64/1.71  tff(c_1402, plain, (![A_298, B_299, A_300]: (r1_tarski(k3_xboole_0(A_298, B_299), A_300) | ~r2_hidden(A_300, k2_tarski(A_298, B_299)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1254])).
% 3.64/1.71  tff(c_1417, plain, (![A_83, B_84]: (r1_tarski(k3_xboole_0(A_83, B_84), B_84))), inference(resolution, [status(thm)], [c_147, c_1402])).
% 3.64/1.71  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.64/1.71  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.64/1.71  tff(c_58, plain, (![A_43, B_44]: (m1_subset_1(A_43, k1_zfmisc_1(B_44)) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.64/1.71  tff(c_218, plain, (![B_103, A_104]: (v1_relat_1(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.64/1.71  tff(c_232, plain, (![A_108, B_109]: (v1_relat_1(A_108) | ~v1_relat_1(B_109) | ~r1_tarski(A_108, B_109))), inference(resolution, [status(thm)], [c_58, c_218])).
% 3.64/1.71  tff(c_240, plain, (![A_3, B_4]: (v1_relat_1(k3_xboole_0(A_3, B_4)) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_4, c_232])).
% 3.64/1.71  tff(c_68, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.64/1.71  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.64/1.71  tff(c_913, plain, (![C_229, A_230, B_231]: (r1_tarski(k5_relat_1(C_229, A_230), k5_relat_1(C_229, B_231)) | ~r1_tarski(A_230, B_231) | ~v1_relat_1(C_229) | ~v1_relat_1(B_231) | ~v1_relat_1(A_230))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.64/1.71  tff(c_620, plain, (![C_176, A_177, B_178]: (r1_tarski(k5_relat_1(C_176, A_177), k5_relat_1(C_176, B_178)) | ~r1_tarski(A_177, B_178) | ~v1_relat_1(C_176) | ~v1_relat_1(B_178) | ~v1_relat_1(A_177))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.64/1.71  tff(c_272, plain, (![A_116, B_117, C_118]: (r1_tarski(A_116, k3_xboole_0(B_117, C_118)) | ~r1_tarski(A_116, C_118) | ~r1_tarski(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.71  tff(c_66, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.64/1.71  tff(c_298, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_272, c_66])).
% 3.64/1.71  tff(c_362, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_298])).
% 3.64/1.71  tff(c_623, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_620, c_362])).
% 3.64/1.71  tff(c_629, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_4, c_623])).
% 3.64/1.71  tff(c_633, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_240, c_629])).
% 3.64/1.71  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_633])).
% 3.64/1.71  tff(c_638, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_298])).
% 3.64/1.71  tff(c_916, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_913, c_638])).
% 3.64/1.71  tff(c_922, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_916])).
% 3.64/1.71  tff(c_936, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_922])).
% 3.64/1.71  tff(c_939, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_240, c_936])).
% 3.64/1.71  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_939])).
% 3.64/1.71  tff(c_944, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_922])).
% 3.64/1.71  tff(c_1455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1417, c_944])).
% 3.64/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.71  
% 3.64/1.71  Inference rules
% 3.64/1.71  ----------------------
% 3.64/1.71  #Ref     : 0
% 3.64/1.71  #Sup     : 326
% 3.64/1.71  #Fact    : 0
% 3.64/1.71  #Define  : 0
% 3.64/1.71  #Split   : 3
% 3.64/1.71  #Chain   : 0
% 3.64/1.71  #Close   : 0
% 3.64/1.71  
% 3.64/1.71  Ordering : KBO
% 3.64/1.71  
% 3.64/1.71  Simplification rules
% 3.64/1.71  ----------------------
% 3.64/1.71  #Subsume      : 43
% 3.64/1.71  #Demod        : 138
% 3.64/1.71  #Tautology    : 168
% 3.64/1.71  #SimpNegUnit  : 8
% 3.64/1.71  #BackRed      : 4
% 3.64/1.71  
% 3.64/1.71  #Partial instantiations: 0
% 3.64/1.71  #Strategies tried      : 1
% 3.64/1.71  
% 3.64/1.71  Timing (in seconds)
% 3.64/1.71  ----------------------
% 3.64/1.71  Preprocessing        : 0.35
% 3.64/1.71  Parsing              : 0.18
% 3.64/1.71  CNF conversion       : 0.03
% 3.64/1.71  Main loop            : 0.49
% 3.64/1.71  Inferencing          : 0.19
% 3.64/1.71  Reduction            : 0.16
% 3.64/1.71  Demodulation         : 0.12
% 3.64/1.71  BG Simplification    : 0.02
% 3.64/1.71  Subsumption          : 0.09
% 3.64/1.71  Abstraction          : 0.03
% 3.64/1.71  MUC search           : 0.00
% 3.64/1.71  Cooper               : 0.00
% 3.64/1.71  Total                : 0.88
% 3.64/1.71  Index Insertion      : 0.00
% 3.64/1.71  Index Deletion       : 0.00
% 3.64/1.71  Index Matching       : 0.00
% 3.64/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
