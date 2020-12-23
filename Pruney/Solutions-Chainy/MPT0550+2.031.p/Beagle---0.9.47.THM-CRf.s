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
% DateTime   : Thu Dec  3 10:00:55 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  87 expanded)
%              Number of equality atoms :   20 (  37 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_151,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(k1_relat_1(B_38),A_39)
      | k9_relat_1(B_38,A_39) != k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_207,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(A_46,k1_relat_1(B_47))
      | k9_relat_1(B_47,A_46) != k1_xboole_0
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,(
    k4_xboole_0('#skF_3',k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_69,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_69])).

tff(c_90,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_84])).

tff(c_119,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,k3_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [C_34] :
      ( ~ r1_xboole_0('#skF_3',k1_relat_1('#skF_4'))
      | ~ r2_hidden(C_34,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_119])).

tff(c_133,plain,(
    ~ r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_217,plain,
    ( k9_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_207,c_133])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_217])).

tff(c_228,plain,(
    ! [C_48] : ~ r2_hidden(C_48,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_232,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_228])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.92/1.21  
% 1.92/1.21  %Foreground sorts:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Background operators:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Foreground operators:
% 1.92/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.92/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.92/1.21  
% 1.92/1.22  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 1.92/1.22  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.92/1.22  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 1.92/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.92/1.22  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.92/1.22  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.92/1.22  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.92/1.22  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.92/1.22  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.92/1.22  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.22  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.92/1.22  tff(c_24, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.92/1.22  tff(c_151, plain, (![B_38, A_39]: (r1_xboole_0(k1_relat_1(B_38), A_39) | k9_relat_1(B_38, A_39)!=k1_xboole_0 | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.92/1.22  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.22  tff(c_207, plain, (![A_46, B_47]: (r1_xboole_0(A_46, k1_relat_1(B_47)) | k9_relat_1(B_47, A_46)!=k1_xboole_0 | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_151, c_2])).
% 1.92/1.22  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.22  tff(c_26, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.92/1.22  tff(c_56, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.22  tff(c_64, plain, (k4_xboole_0('#skF_3', k1_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_56])).
% 1.92/1.22  tff(c_69, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.22  tff(c_84, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_69])).
% 1.92/1.22  tff(c_90, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_84])).
% 1.92/1.22  tff(c_119, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.22  tff(c_125, plain, (![C_34]: (~r1_xboole_0('#skF_3', k1_relat_1('#skF_4')) | ~r2_hidden(C_34, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_119])).
% 1.92/1.22  tff(c_133, plain, (~r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_125])).
% 1.92/1.22  tff(c_217, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_207, c_133])).
% 1.92/1.22  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_217])).
% 1.92/1.22  tff(c_228, plain, (![C_48]: (~r2_hidden(C_48, '#skF_3'))), inference(splitRight, [status(thm)], [c_125])).
% 1.92/1.22  tff(c_232, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_228])).
% 1.92/1.22  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_232])).
% 1.92/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  Inference rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Ref     : 0
% 1.92/1.22  #Sup     : 50
% 1.92/1.22  #Fact    : 0
% 1.92/1.22  #Define  : 0
% 1.92/1.22  #Split   : 2
% 1.92/1.22  #Chain   : 0
% 1.92/1.22  #Close   : 0
% 1.92/1.22  
% 1.92/1.22  Ordering : KBO
% 1.92/1.22  
% 1.92/1.22  Simplification rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Subsume      : 0
% 1.92/1.22  #Demod        : 14
% 1.92/1.22  #Tautology    : 30
% 1.92/1.22  #SimpNegUnit  : 3
% 1.92/1.22  #BackRed      : 0
% 1.92/1.22  
% 1.92/1.22  #Partial instantiations: 0
% 1.92/1.22  #Strategies tried      : 1
% 1.92/1.22  
% 1.92/1.22  Timing (in seconds)
% 1.92/1.22  ----------------------
% 1.92/1.22  Preprocessing        : 0.29
% 1.92/1.22  Parsing              : 0.16
% 1.92/1.22  CNF conversion       : 0.02
% 1.92/1.22  Main loop            : 0.17
% 1.92/1.22  Inferencing          : 0.07
% 1.92/1.22  Reduction            : 0.05
% 1.92/1.22  Demodulation         : 0.04
% 1.92/1.22  BG Simplification    : 0.01
% 1.92/1.22  Subsumption          : 0.02
% 1.92/1.22  Abstraction          : 0.01
% 1.92/1.22  MUC search           : 0.00
% 1.92/1.22  Cooper               : 0.00
% 1.92/1.22  Total                : 0.49
% 1.92/1.22  Index Insertion      : 0.00
% 1.92/1.22  Index Deletion       : 0.00
% 1.92/1.22  Index Matching       : 0.00
% 1.92/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
