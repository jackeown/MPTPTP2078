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
% DateTime   : Thu Dec  3 10:01:42 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   55 (  78 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 106 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( r1_xboole_0(k2_relat_1(B_22),A_21)
      | k10_relat_1(B_22,A_21) != k1_xboole_0
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_99,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_99])).

tff(c_122,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_137,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_122])).

tff(c_143,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_137])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_172,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_192,plain,(
    ! [A_44,B_45] :
      ( ~ r1_xboole_0(A_44,B_45)
      | v1_xboole_0(k3_xboole_0(A_44,B_45)) ) ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_215,plain,(
    ! [A_48,B_49] :
      ( ~ r1_xboole_0(A_48,B_49)
      | v1_xboole_0(k3_xboole_0(B_49,A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_192])).

tff(c_226,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_215])).

tff(c_236,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_239,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_236])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_239])).

tff(c_244,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    ! [B_29,A_30] :
      ( ~ v1_xboole_0(B_29)
      | B_29 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_92,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_248,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_244,c_92])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.98/1.21  
% 1.98/1.21  %Foreground sorts:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Background operators:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Foreground operators:
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.98/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.98/1.21  
% 1.98/1.22  tff(f_83, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 1.98/1.22  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.98/1.22  tff(f_54, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.98/1.22  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.98/1.22  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.98/1.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.98/1.22  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.98/1.22  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.98/1.22  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.22  tff(f_64, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.98/1.22  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.22  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.22  tff(c_30, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.22  tff(c_28, plain, (![B_22, A_21]: (r1_xboole_0(k2_relat_1(B_22), A_21) | k10_relat_1(B_22, A_21)!=k1_xboole_0 | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.98/1.22  tff(c_18, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.22  tff(c_32, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.22  tff(c_99, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.98/1.22  tff(c_103, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_99])).
% 1.98/1.22  tff(c_122, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.22  tff(c_137, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_103, c_122])).
% 1.98/1.22  tff(c_143, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_137])).
% 1.98/1.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.22  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.22  tff(c_172, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.98/1.22  tff(c_192, plain, (![A_44, B_45]: (~r1_xboole_0(A_44, B_45) | v1_xboole_0(k3_xboole_0(A_44, B_45)))), inference(resolution, [status(thm)], [c_6, c_172])).
% 1.98/1.22  tff(c_215, plain, (![A_48, B_49]: (~r1_xboole_0(A_48, B_49) | v1_xboole_0(k3_xboole_0(B_49, A_48)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_192])).
% 1.98/1.22  tff(c_226, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_143, c_215])).
% 1.98/1.22  tff(c_236, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_226])).
% 1.98/1.22  tff(c_239, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_236])).
% 1.98/1.22  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_239])).
% 1.98/1.22  tff(c_244, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_226])).
% 1.98/1.22  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.98/1.22  tff(c_89, plain, (![B_29, A_30]: (~v1_xboole_0(B_29) | B_29=A_30 | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.98/1.22  tff(c_92, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_8, c_89])).
% 1.98/1.22  tff(c_248, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_244, c_92])).
% 1.98/1.22  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_248])).
% 1.98/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  Inference rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Ref     : 0
% 1.98/1.22  #Sup     : 56
% 1.98/1.22  #Fact    : 0
% 1.98/1.22  #Define  : 0
% 1.98/1.22  #Split   : 3
% 1.98/1.22  #Chain   : 0
% 1.98/1.22  #Close   : 0
% 1.98/1.22  
% 1.98/1.22  Ordering : KBO
% 1.98/1.22  
% 1.98/1.22  Simplification rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Subsume      : 5
% 1.98/1.22  #Demod        : 6
% 1.98/1.22  #Tautology    : 28
% 1.98/1.22  #SimpNegUnit  : 1
% 1.98/1.22  #BackRed      : 0
% 1.98/1.22  
% 1.98/1.22  #Partial instantiations: 0
% 1.98/1.22  #Strategies tried      : 1
% 1.98/1.22  
% 1.98/1.22  Timing (in seconds)
% 1.98/1.22  ----------------------
% 1.98/1.23  Preprocessing        : 0.29
% 1.98/1.23  Parsing              : 0.16
% 1.98/1.23  CNF conversion       : 0.02
% 1.98/1.23  Main loop            : 0.17
% 1.98/1.23  Inferencing          : 0.06
% 1.98/1.23  Reduction            : 0.05
% 1.98/1.23  Demodulation         : 0.04
% 1.98/1.23  BG Simplification    : 0.01
% 1.98/1.23  Subsumption          : 0.03
% 1.98/1.23  Abstraction          : 0.01
% 1.98/1.23  MUC search           : 0.00
% 1.98/1.23  Cooper               : 0.00
% 1.98/1.23  Total                : 0.48
% 1.98/1.23  Index Insertion      : 0.00
% 1.98/1.23  Index Deletion       : 0.00
% 1.98/1.23  Index Matching       : 0.00
% 1.98/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
