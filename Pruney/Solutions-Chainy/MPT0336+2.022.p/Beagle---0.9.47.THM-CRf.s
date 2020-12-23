%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:03 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 180 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  115 ( 280 expanded)
%              Number of equality atoms :   33 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_152,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(A_42,B_43)
      | k4_xboole_0(A_42,B_43) != A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [B_43,A_42] :
      ( r1_xboole_0(B_43,A_42)
      | k4_xboole_0(A_42,B_43) != A_42 ) ),
    inference(resolution,[status(thm)],[c_152,c_6])).

tff(c_44,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_136,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_142,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_136])).

tff(c_1168,plain,(
    ! [A_116,C_117,B_118] :
      ( ~ r1_xboole_0(A_116,C_117)
      | ~ r1_xboole_0(A_116,B_118)
      | r1_xboole_0(A_116,k2_xboole_0(B_118,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3397,plain,(
    ! [B_245,C_246,A_247] :
      ( r1_xboole_0(k2_xboole_0(B_245,C_246),A_247)
      | ~ r1_xboole_0(A_247,C_246)
      | ~ r1_xboole_0(A_247,B_245) ) ),
    inference(resolution,[status(thm)],[c_1168,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_3420,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_2')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_3397,c_50])).

tff(c_3436,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_3420])).

tff(c_3455,plain,(
    k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_158,c_3436])).

tff(c_160,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_181,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_160])).

tff(c_40,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,k1_tarski(B_31)) = A_30
      | r2_hidden(B_31,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_507,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_xboole_0(A_74,C_75)
      | ~ r1_xboole_0(B_76,C_75)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_9535,plain,(
    ! [A_361,A_362,B_363] :
      ( r1_xboole_0(A_361,A_362)
      | ~ r1_tarski(A_361,B_363)
      | k4_xboole_0(A_362,B_363) != A_362 ) ),
    inference(resolution,[status(thm)],[c_158,c_507])).

tff(c_9556,plain,(
    ! [A_366] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),A_366)
      | k4_xboole_0(A_366,k1_tarski('#skF_5')) != A_366 ) ),
    inference(resolution,[status(thm)],[c_49,c_9535])).

tff(c_10727,plain,(
    ! [A_410] :
      ( r1_xboole_0(A_410,k3_xboole_0('#skF_3','#skF_2'))
      | k4_xboole_0(A_410,k1_tarski('#skF_5')) != A_410 ) ),
    inference(resolution,[status(thm)],[c_9556,c_6])).

tff(c_20,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_304,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_141,plain,(
    ! [A_18] : r1_xboole_0(k1_xboole_0,A_18) ),
    inference(resolution,[status(thm)],[c_20,c_136])).

tff(c_178,plain,(
    ! [A_18] : k4_xboole_0(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_141,c_160])).

tff(c_351,plain,(
    ! [B_66] : k3_xboole_0(k1_xboole_0,B_66) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_178])).

tff(c_369,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_351])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_339,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_304])).

tff(c_424,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_339])).

tff(c_706,plain,(
    ! [B_98,A_99,C_100] :
      ( r1_xboole_0(B_98,k4_xboole_0(A_99,C_100))
      | ~ r1_xboole_0(A_99,k4_xboole_0(B_98,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_720,plain,(
    ! [A_12,A_99] :
      ( r1_xboole_0(A_12,k4_xboole_0(A_99,A_12))
      | ~ r1_xboole_0(A_99,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_706])).

tff(c_755,plain,(
    ! [A_101,A_102] : r1_xboole_0(A_101,k4_xboole_0(A_102,A_101)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_720])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_792,plain,(
    ! [A_101,A_102] : k4_xboole_0(A_101,k4_xboole_0(A_102,A_101)) = A_101 ),
    inference(resolution,[status(thm)],[c_755,c_30])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4560,plain,(
    ! [A_273,A_274,B_275] :
      ( r1_xboole_0(A_273,k4_xboole_0(A_274,k4_xboole_0(A_273,B_275)))
      | ~ r1_xboole_0(A_274,k3_xboole_0(A_273,B_275)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_706])).

tff(c_4659,plain,(
    ! [A_276,A_277] :
      ( r1_xboole_0(A_276,A_277)
      | ~ r1_xboole_0(A_277,k3_xboole_0(A_276,A_277)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_4560])).

tff(c_4777,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4659])).

tff(c_10757,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_5')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_10727,c_4777])).

tff(c_11595,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_5')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10757])).

tff(c_11607,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_11595])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_645,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,B_86)
      | ~ r2_hidden(C_87,A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9243,plain,(
    ! [C_353,A_354,B_355] :
      ( ~ r2_hidden(C_353,A_354)
      | ~ r2_hidden(C_353,B_355)
      | k4_xboole_0(A_354,B_355) != A_354 ) ),
    inference(resolution,[status(thm)],[c_158,c_645])).

tff(c_9255,plain,(
    ! [B_355] :
      ( ~ r2_hidden('#skF_5',B_355)
      | k4_xboole_0('#skF_4',B_355) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_46,c_9243])).

tff(c_11619,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_11607,c_9255])).

tff(c_11644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_11619])).

tff(c_11645,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_10757])).

tff(c_11739,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_11645,c_30])).

tff(c_11747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3455,c_11739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:15:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.45/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.63  
% 7.45/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.45/2.63  
% 7.45/2.63  %Foreground sorts:
% 7.45/2.63  
% 7.45/2.63  
% 7.45/2.63  %Background operators:
% 7.45/2.63  
% 7.45/2.63  
% 7.45/2.63  %Foreground operators:
% 7.45/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.45/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.45/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.45/2.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.45/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.45/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.45/2.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.45/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.45/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.45/2.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.45/2.63  tff('#skF_2', type, '#skF_2': $i).
% 7.45/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.45/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.45/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.45/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.45/2.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.45/2.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.45/2.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.45/2.63  
% 7.60/2.64  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.60/2.64  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.60/2.64  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.60/2.64  tff(f_79, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.60/2.64  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.60/2.64  tff(f_96, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.60/2.64  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.60/2.64  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 7.60/2.64  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.60/2.64  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.60/2.64  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.60/2.64  tff(f_83, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 7.60/2.64  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.60/2.64  tff(c_152, plain, (![A_42, B_43]: (r1_xboole_0(A_42, B_43) | k4_xboole_0(A_42, B_43)!=A_42)), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.60/2.64  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.60/2.64  tff(c_158, plain, (![B_43, A_42]: (r1_xboole_0(B_43, A_42) | k4_xboole_0(A_42, B_43)!=A_42)), inference(resolution, [status(thm)], [c_152, c_6])).
% 7.60/2.64  tff(c_44, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.60/2.64  tff(c_136, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.60/2.64  tff(c_142, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_136])).
% 7.60/2.64  tff(c_1168, plain, (![A_116, C_117, B_118]: (~r1_xboole_0(A_116, C_117) | ~r1_xboole_0(A_116, B_118) | r1_xboole_0(A_116, k2_xboole_0(B_118, C_117)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.60/2.64  tff(c_3397, plain, (![B_245, C_246, A_247]: (r1_xboole_0(k2_xboole_0(B_245, C_246), A_247) | ~r1_xboole_0(A_247, C_246) | ~r1_xboole_0(A_247, B_245))), inference(resolution, [status(thm)], [c_1168, c_6])).
% 7.60/2.64  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.60/2.64  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.60/2.64  tff(c_50, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 7.60/2.64  tff(c_3420, plain, (~r1_xboole_0('#skF_3', '#skF_2') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_3397, c_50])).
% 7.60/2.64  tff(c_3436, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_3420])).
% 7.60/2.64  tff(c_3455, plain, (k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_158, c_3436])).
% 7.60/2.64  tff(c_160, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.60/2.64  tff(c_181, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_44, c_160])).
% 7.60/2.64  tff(c_40, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k1_tarski(B_31))=A_30 | r2_hidden(B_31, A_30))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.60/2.64  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.60/2.64  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.60/2.64  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_48])).
% 7.60/2.64  tff(c_507, plain, (![A_74, C_75, B_76]: (r1_xboole_0(A_74, C_75) | ~r1_xboole_0(B_76, C_75) | ~r1_tarski(A_74, B_76))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.60/2.64  tff(c_9535, plain, (![A_361, A_362, B_363]: (r1_xboole_0(A_361, A_362) | ~r1_tarski(A_361, B_363) | k4_xboole_0(A_362, B_363)!=A_362)), inference(resolution, [status(thm)], [c_158, c_507])).
% 7.60/2.64  tff(c_9556, plain, (![A_366]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), A_366) | k4_xboole_0(A_366, k1_tarski('#skF_5'))!=A_366)), inference(resolution, [status(thm)], [c_49, c_9535])).
% 7.60/2.64  tff(c_10727, plain, (![A_410]: (r1_xboole_0(A_410, k3_xboole_0('#skF_3', '#skF_2')) | k4_xboole_0(A_410, k1_tarski('#skF_5'))!=A_410)), inference(resolution, [status(thm)], [c_9556, c_6])).
% 7.60/2.64  tff(c_20, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.60/2.64  tff(c_304, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.60/2.64  tff(c_141, plain, (![A_18]: (r1_xboole_0(k1_xboole_0, A_18))), inference(resolution, [status(thm)], [c_20, c_136])).
% 7.60/2.64  tff(c_178, plain, (![A_18]: (k4_xboole_0(k1_xboole_0, A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_141, c_160])).
% 7.60/2.64  tff(c_351, plain, (![B_66]: (k3_xboole_0(k1_xboole_0, B_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_304, c_178])).
% 7.60/2.64  tff(c_369, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_351])).
% 7.60/2.64  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.60/2.64  tff(c_339, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_304])).
% 7.60/2.64  tff(c_424, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_369, c_339])).
% 7.60/2.64  tff(c_706, plain, (![B_98, A_99, C_100]: (r1_xboole_0(B_98, k4_xboole_0(A_99, C_100)) | ~r1_xboole_0(A_99, k4_xboole_0(B_98, C_100)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.60/2.64  tff(c_720, plain, (![A_12, A_99]: (r1_xboole_0(A_12, k4_xboole_0(A_99, A_12)) | ~r1_xboole_0(A_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_424, c_706])).
% 7.60/2.64  tff(c_755, plain, (![A_101, A_102]: (r1_xboole_0(A_101, k4_xboole_0(A_102, A_101)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_720])).
% 7.60/2.64  tff(c_30, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.60/2.64  tff(c_792, plain, (![A_101, A_102]: (k4_xboole_0(A_101, k4_xboole_0(A_102, A_101))=A_101)), inference(resolution, [status(thm)], [c_755, c_30])).
% 7.60/2.64  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.60/2.64  tff(c_4560, plain, (![A_273, A_274, B_275]: (r1_xboole_0(A_273, k4_xboole_0(A_274, k4_xboole_0(A_273, B_275))) | ~r1_xboole_0(A_274, k3_xboole_0(A_273, B_275)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_706])).
% 7.60/2.64  tff(c_4659, plain, (![A_276, A_277]: (r1_xboole_0(A_276, A_277) | ~r1_xboole_0(A_277, k3_xboole_0(A_276, A_277)))), inference(superposition, [status(thm), theory('equality')], [c_792, c_4560])).
% 7.60/2.64  tff(c_4777, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4659])).
% 7.60/2.64  tff(c_10757, plain, (r1_xboole_0('#skF_2', '#skF_3') | k4_xboole_0('#skF_3', k1_tarski('#skF_5'))!='#skF_3'), inference(resolution, [status(thm)], [c_10727, c_4777])).
% 7.60/2.64  tff(c_11595, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_5'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_10757])).
% 7.60/2.64  tff(c_11607, plain, (r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_11595])).
% 7.60/2.64  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.60/2.64  tff(c_645, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, B_86) | ~r2_hidden(C_87, A_85))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.60/2.64  tff(c_9243, plain, (![C_353, A_354, B_355]: (~r2_hidden(C_353, A_354) | ~r2_hidden(C_353, B_355) | k4_xboole_0(A_354, B_355)!=A_354)), inference(resolution, [status(thm)], [c_158, c_645])).
% 7.60/2.64  tff(c_9255, plain, (![B_355]: (~r2_hidden('#skF_5', B_355) | k4_xboole_0('#skF_4', B_355)!='#skF_4')), inference(resolution, [status(thm)], [c_46, c_9243])).
% 7.60/2.64  tff(c_11619, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_11607, c_9255])).
% 7.60/2.64  tff(c_11644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_11619])).
% 7.60/2.64  tff(c_11645, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_10757])).
% 7.60/2.64  tff(c_11739, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_11645, c_30])).
% 7.60/2.64  tff(c_11747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3455, c_11739])).
% 7.60/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.64  
% 7.60/2.64  Inference rules
% 7.60/2.64  ----------------------
% 7.60/2.64  #Ref     : 1
% 7.60/2.64  #Sup     : 3029
% 7.60/2.64  #Fact    : 0
% 7.60/2.64  #Define  : 0
% 7.60/2.64  #Split   : 6
% 7.60/2.64  #Chain   : 0
% 7.60/2.64  #Close   : 0
% 7.60/2.64  
% 7.60/2.64  Ordering : KBO
% 7.60/2.64  
% 7.60/2.64  Simplification rules
% 7.60/2.64  ----------------------
% 7.60/2.64  #Subsume      : 726
% 7.60/2.64  #Demod        : 1525
% 7.60/2.64  #Tautology    : 1322
% 7.60/2.64  #SimpNegUnit  : 27
% 7.60/2.64  #BackRed      : 6
% 7.60/2.64  
% 7.60/2.64  #Partial instantiations: 0
% 7.60/2.64  #Strategies tried      : 1
% 7.60/2.64  
% 7.60/2.64  Timing (in seconds)
% 7.60/2.64  ----------------------
% 7.60/2.65  Preprocessing        : 0.31
% 7.60/2.65  Parsing              : 0.17
% 7.60/2.65  CNF conversion       : 0.02
% 7.60/2.65  Main loop            : 1.59
% 7.60/2.65  Inferencing          : 0.44
% 7.60/2.65  Reduction            : 0.67
% 7.60/2.65  Demodulation         : 0.50
% 7.60/2.65  BG Simplification    : 0.04
% 7.60/2.65  Subsumption          : 0.33
% 7.60/2.65  Abstraction          : 0.06
% 7.60/2.65  MUC search           : 0.00
% 7.60/2.65  Cooper               : 0.00
% 7.60/2.65  Total                : 1.93
% 7.60/2.65  Index Insertion      : 0.00
% 7.60/2.65  Index Deletion       : 0.00
% 7.60/2.65  Index Matching       : 0.00
% 7.60/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
