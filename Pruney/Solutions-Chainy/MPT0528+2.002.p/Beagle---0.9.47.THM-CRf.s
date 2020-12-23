%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:11 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 112 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k8_relat_1(A,k8_relat_1(A,B)) = k8_relat_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k8_relat_1(A_19,B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden(k4_tarski('#skF_1'(A_41,B_42,C_43),'#skF_2'(A_41,B_42,C_43)),B_42)
      | r2_hidden(k4_tarski('#skF_3'(A_41,B_42,C_43),'#skF_4'(A_41,B_42,C_43)),C_43)
      | k8_relat_1(A_41,B_42) = C_43
      | ~ v1_relat_1(C_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_1,B_2,C_12] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),C_12)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),C_12)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(k4_tarski('#skF_3'(A_47,B_48,B_48),'#skF_4'(A_47,B_48,B_48)),B_48)
      | k8_relat_1(A_47,B_48) = B_48
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_18,plain,(
    ! [E_18,A_1,D_17,B_2] :
      ( r2_hidden(E_18,A_1)
      | ~ r2_hidden(k4_tarski(D_17,E_18),k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_107,plain,(
    ! [A_47,A_1,B_2] :
      ( r2_hidden('#skF_4'(A_47,k8_relat_1(A_1,B_2),k8_relat_1(A_1,B_2)),A_1)
      | ~ v1_relat_1(B_2)
      | k8_relat_1(A_47,k8_relat_1(A_1,B_2)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(k8_relat_1(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_93,c_18])).

tff(c_75,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(k4_tarski('#skF_3'(A_41,B_42,B_42),'#skF_4'(A_41,B_42,B_42)),B_42)
      | k8_relat_1(A_41,B_42) = B_42
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2,C_12] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),B_2)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),B_2)
      | ~ r2_hidden('#skF_4'(A_1,B_2,C_12),A_1)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_149,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_66,B_67,C_68),'#skF_2'(A_66,B_67,C_68)),C_68)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_66,B_67,C_68),'#skF_4'(A_66,B_67,C_68)),B_67)
      | ~ r2_hidden('#skF_4'(A_66,B_67,C_68),A_66)
      | k8_relat_1(A_66,B_67) = C_68
      | ~ v1_relat_1(C_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_69,B_70,B_70),'#skF_4'(A_69,B_70,B_70)),B_70)
      | ~ r2_hidden('#skF_4'(A_69,B_70,B_70),A_69)
      | k8_relat_1(A_69,B_70) = B_70
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_4,c_149])).

tff(c_179,plain,(
    ! [A_71,B_72] :
      ( ~ r2_hidden('#skF_4'(A_71,B_72,B_72),A_71)
      | k8_relat_1(A_71,B_72) = B_72
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_75,c_162])).

tff(c_190,plain,(
    ! [B_73,A_74] :
      ( ~ v1_relat_1(B_73)
      | k8_relat_1(A_74,k8_relat_1(A_74,B_73)) = k8_relat_1(A_74,B_73)
      | ~ v1_relat_1(k8_relat_1(A_74,B_73)) ) ),
    inference(resolution,[status(thm)],[c_107,c_179])).

tff(c_194,plain,(
    ! [A_75,B_76] :
      ( k8_relat_1(A_75,k8_relat_1(A_75,B_76)) = k8_relat_1(A_75,B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_20,c_190])).

tff(c_22,plain,(
    k8_relat_1('#skF_5',k8_relat_1('#skF_5','#skF_6')) != k8_relat_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_236,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_22])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.24  
% 2.20/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.25  %$ r2_hidden > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.20/1.25  
% 2.20/1.25  %Foreground sorts:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Background operators:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Foreground operators:
% 2.20/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.20/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.20/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.20/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.20/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.25  
% 2.20/1.26  tff(f_48, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k8_relat_1(A, k8_relat_1(A, B)) = k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_relat_1)).
% 2.20/1.26  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.20/1.26  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 2.20/1.26  tff(c_24, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.20/1.26  tff(c_20, plain, (![A_19, B_20]: (v1_relat_1(k8_relat_1(A_19, B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.26  tff(c_54, plain, (![A_41, B_42, C_43]: (r2_hidden(k4_tarski('#skF_1'(A_41, B_42, C_43), '#skF_2'(A_41, B_42, C_43)), B_42) | r2_hidden(k4_tarski('#skF_3'(A_41, B_42, C_43), '#skF_4'(A_41, B_42, C_43)), C_43) | k8_relat_1(A_41, B_42)=C_43 | ~v1_relat_1(C_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.26  tff(c_8, plain, (![A_1, B_2, C_12]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), C_12) | r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), C_12) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.26  tff(c_93, plain, (![A_47, B_48]: (r2_hidden(k4_tarski('#skF_3'(A_47, B_48, B_48), '#skF_4'(A_47, B_48, B_48)), B_48) | k8_relat_1(A_47, B_48)=B_48 | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_54, c_8])).
% 2.20/1.26  tff(c_18, plain, (![E_18, A_1, D_17, B_2]: (r2_hidden(E_18, A_1) | ~r2_hidden(k4_tarski(D_17, E_18), k8_relat_1(A_1, B_2)) | ~v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.26  tff(c_107, plain, (![A_47, A_1, B_2]: (r2_hidden('#skF_4'(A_47, k8_relat_1(A_1, B_2), k8_relat_1(A_1, B_2)), A_1) | ~v1_relat_1(B_2) | k8_relat_1(A_47, k8_relat_1(A_1, B_2))=k8_relat_1(A_1, B_2) | ~v1_relat_1(k8_relat_1(A_1, B_2)))), inference(resolution, [status(thm)], [c_93, c_18])).
% 2.20/1.26  tff(c_75, plain, (![A_41, B_42]: (r2_hidden(k4_tarski('#skF_3'(A_41, B_42, B_42), '#skF_4'(A_41, B_42, B_42)), B_42) | k8_relat_1(A_41, B_42)=B_42 | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_54, c_8])).
% 2.20/1.26  tff(c_4, plain, (![A_1, B_2, C_12]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), B_2) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), B_2) | ~r2_hidden('#skF_4'(A_1, B_2, C_12), A_1) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.26  tff(c_149, plain, (![A_66, B_67, C_68]: (~r2_hidden(k4_tarski('#skF_1'(A_66, B_67, C_68), '#skF_2'(A_66, B_67, C_68)), C_68) | ~r2_hidden(k4_tarski('#skF_3'(A_66, B_67, C_68), '#skF_4'(A_66, B_67, C_68)), B_67) | ~r2_hidden('#skF_4'(A_66, B_67, C_68), A_66) | k8_relat_1(A_66, B_67)=C_68 | ~v1_relat_1(C_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.26  tff(c_162, plain, (![A_69, B_70]: (~r2_hidden(k4_tarski('#skF_3'(A_69, B_70, B_70), '#skF_4'(A_69, B_70, B_70)), B_70) | ~r2_hidden('#skF_4'(A_69, B_70, B_70), A_69) | k8_relat_1(A_69, B_70)=B_70 | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_4, c_149])).
% 2.20/1.26  tff(c_179, plain, (![A_71, B_72]: (~r2_hidden('#skF_4'(A_71, B_72, B_72), A_71) | k8_relat_1(A_71, B_72)=B_72 | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_75, c_162])).
% 2.20/1.26  tff(c_190, plain, (![B_73, A_74]: (~v1_relat_1(B_73) | k8_relat_1(A_74, k8_relat_1(A_74, B_73))=k8_relat_1(A_74, B_73) | ~v1_relat_1(k8_relat_1(A_74, B_73)))), inference(resolution, [status(thm)], [c_107, c_179])).
% 2.20/1.26  tff(c_194, plain, (![A_75, B_76]: (k8_relat_1(A_75, k8_relat_1(A_75, B_76))=k8_relat_1(A_75, B_76) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_20, c_190])).
% 2.20/1.26  tff(c_22, plain, (k8_relat_1('#skF_5', k8_relat_1('#skF_5', '#skF_6'))!=k8_relat_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.20/1.26  tff(c_236, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_194, c_22])).
% 2.20/1.26  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_236])).
% 2.20/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  Inference rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Ref     : 0
% 2.20/1.26  #Sup     : 48
% 2.20/1.26  #Fact    : 0
% 2.20/1.26  #Define  : 0
% 2.20/1.26  #Split   : 0
% 2.20/1.26  #Chain   : 0
% 2.20/1.26  #Close   : 0
% 2.20/1.26  
% 2.20/1.26  Ordering : KBO
% 2.20/1.26  
% 2.20/1.26  Simplification rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Subsume      : 11
% 2.20/1.26  #Demod        : 1
% 2.20/1.26  #Tautology    : 6
% 2.20/1.26  #SimpNegUnit  : 0
% 2.20/1.26  #BackRed      : 0
% 2.20/1.26  
% 2.20/1.26  #Partial instantiations: 0
% 2.20/1.26  #Strategies tried      : 1
% 2.20/1.26  
% 2.20/1.26  Timing (in seconds)
% 2.20/1.26  ----------------------
% 2.20/1.26  Preprocessing        : 0.27
% 2.20/1.26  Parsing              : 0.14
% 2.20/1.26  CNF conversion       : 0.02
% 2.20/1.26  Main loop            : 0.23
% 2.20/1.26  Inferencing          : 0.11
% 2.20/1.26  Reduction            : 0.05
% 2.20/1.26  Demodulation         : 0.04
% 2.20/1.26  BG Simplification    : 0.02
% 2.20/1.26  Subsumption          : 0.06
% 2.20/1.26  Abstraction          : 0.01
% 2.20/1.26  MUC search           : 0.00
% 2.20/1.26  Cooper               : 0.00
% 2.20/1.26  Total                : 0.53
% 2.20/1.26  Index Insertion      : 0.00
% 2.20/1.26  Index Deletion       : 0.00
% 2.20/1.26  Index Matching       : 0.00
% 2.20/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
