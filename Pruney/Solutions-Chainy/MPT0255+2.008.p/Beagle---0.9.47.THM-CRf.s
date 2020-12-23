%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:40 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   51 (  94 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 ( 113 expanded)
%              Number of equality atoms :   29 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_14,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_433,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_454,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_433])).

tff(c_461,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_454])).

tff(c_94,plain,(
    ! [A_66] : k2_tarski(A_66,A_66) = k1_tarski(A_66) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ! [B_54,C_55] : r1_tarski(k1_xboole_0,k2_tarski(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,(
    ! [A_66] : r1_tarski(k1_xboole_0,k1_tarski(A_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_48])).

tff(c_56,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_175,plain,(
    ! [A_74,B_75] : k3_xboole_0(A_74,k2_xboole_0(A_74,B_75)) = A_74 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k2_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_175])).

tff(c_187,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_184])).

tff(c_44,plain,(
    ! [C_55,B_54] : r1_tarski(k1_tarski(C_55),k2_tarski(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_195,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_44])).

tff(c_321,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(B_85,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_323,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_195,c_321])).

tff(c_338,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_323])).

tff(c_52,plain,(
    ! [B_59] : k4_xboole_0(k1_tarski(B_59),k1_tarski(B_59)) != k1_tarski(B_59) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_355,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_52])).

tff(c_375,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_338,c_355])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.33  
% 2.47/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.34  
% 2.47/1.34  %Foreground sorts:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Background operators:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Foreground operators:
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.34  
% 2.47/1.35  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.47/1.35  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.47/1.35  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.47/1.35  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.35  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.47/1.35  tff(f_89, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.47/1.35  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.47/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.47/1.35  tff(f_85, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.47/1.35  tff(c_14, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/1.35  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.35  tff(c_433, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.35  tff(c_454, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_433])).
% 2.47/1.35  tff(c_461, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_454])).
% 2.47/1.35  tff(c_94, plain, (![A_66]: (k2_tarski(A_66, A_66)=k1_tarski(A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.35  tff(c_48, plain, (![B_54, C_55]: (r1_tarski(k1_xboole_0, k2_tarski(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.35  tff(c_99, plain, (![A_66]: (r1_tarski(k1_xboole_0, k1_tarski(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_48])).
% 2.47/1.35  tff(c_56, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.47/1.35  tff(c_175, plain, (![A_74, B_75]: (k3_xboole_0(A_74, k2_xboole_0(A_74, B_75))=A_74)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.35  tff(c_184, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k2_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_175])).
% 2.47/1.35  tff(c_187, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_184])).
% 2.47/1.35  tff(c_44, plain, (![C_55, B_54]: (r1_tarski(k1_tarski(C_55), k2_tarski(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.35  tff(c_195, plain, (r1_tarski(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_187, c_44])).
% 2.47/1.35  tff(c_321, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(B_85, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.35  tff(c_323, plain, (k1_tarski('#skF_2')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_195, c_321])).
% 2.47/1.35  tff(c_338, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_99, c_323])).
% 2.47/1.35  tff(c_52, plain, (![B_59]: (k4_xboole_0(k1_tarski(B_59), k1_tarski(B_59))!=k1_tarski(B_59))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.47/1.35  tff(c_355, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_338, c_52])).
% 2.47/1.35  tff(c_375, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_338, c_338, c_355])).
% 2.47/1.35  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_461, c_375])).
% 2.47/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  Inference rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Ref     : 0
% 2.47/1.35  #Sup     : 112
% 2.47/1.35  #Fact    : 0
% 2.47/1.35  #Define  : 0
% 2.47/1.35  #Split   : 0
% 2.47/1.35  #Chain   : 0
% 2.47/1.35  #Close   : 0
% 2.47/1.35  
% 2.47/1.35  Ordering : KBO
% 2.47/1.35  
% 2.47/1.35  Simplification rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Subsume      : 4
% 2.47/1.35  #Demod        : 47
% 2.47/1.35  #Tautology    : 83
% 2.47/1.35  #SimpNegUnit  : 0
% 2.47/1.35  #BackRed      : 4
% 2.47/1.35  
% 2.47/1.35  #Partial instantiations: 0
% 2.47/1.35  #Strategies tried      : 1
% 2.47/1.35  
% 2.47/1.35  Timing (in seconds)
% 2.47/1.35  ----------------------
% 2.47/1.35  Preprocessing        : 0.35
% 2.47/1.35  Parsing              : 0.19
% 2.47/1.35  CNF conversion       : 0.02
% 2.47/1.35  Main loop            : 0.23
% 2.47/1.35  Inferencing          : 0.07
% 2.47/1.35  Reduction            : 0.09
% 2.47/1.35  Demodulation         : 0.07
% 2.47/1.35  BG Simplification    : 0.02
% 2.47/1.35  Subsumption          : 0.04
% 2.47/1.35  Abstraction          : 0.02
% 2.47/1.35  MUC search           : 0.00
% 2.47/1.35  Cooper               : 0.00
% 2.47/1.35  Total                : 0.61
% 2.47/1.35  Index Insertion      : 0.00
% 2.47/1.35  Index Deletion       : 0.00
% 2.47/1.35  Index Matching       : 0.00
% 2.47/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
