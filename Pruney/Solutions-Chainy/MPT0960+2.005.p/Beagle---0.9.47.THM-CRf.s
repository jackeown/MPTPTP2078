%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:37 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  46 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k3_relat_1 > k1_wellord2 > k1_setfam_1 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_57,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_30,plain,(
    ! [A_19] : v1_relat_1(k1_wellord2(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_11] :
      ( k3_relat_1(k1_wellord2(A_11)) = A_11
      | ~ v1_relat_1(k1_wellord2(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    ! [A_11] : k3_relat_1(k1_wellord2(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24])).

tff(c_83,plain,(
    ! [A_26] :
      ( k2_wellord1(A_26,k3_relat_1(A_26)) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    ! [A_11] :
      ( k2_wellord1(k1_wellord2(A_11),A_11) = k1_wellord2(A_11)
      | ~ v1_relat_1(k1_wellord2(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_83])).

tff(c_96,plain,(
    ! [A_11] : k2_wellord1(k1_wellord2(A_11),A_11) = k1_wellord2(A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_92])).

tff(c_8,plain,(
    ! [A_7,B_9] :
      ( k3_xboole_0(A_7,k2_zfmisc_1(B_9,B_9)) = k2_wellord1(A_7,B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [B_30,A_31] : k1_setfam_1(k2_tarski(B_30,A_31)) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_106])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_209,plain,(
    ! [B_36,A_37] : r1_tarski(k3_xboole_0(B_36,A_37),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_2])).

tff(c_256,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k2_wellord1(A_44,B_45),k2_zfmisc_1(B_45,B_45))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_209])).

tff(c_259,plain,(
    ! [A_11] :
      ( r1_tarski(k1_wellord2(A_11),k2_zfmisc_1(A_11,A_11))
      | ~ v1_relat_1(k1_wellord2(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_256])).

tff(c_264,plain,(
    ! [A_11] : r1_tarski(k1_wellord2(A_11),k2_zfmisc_1(A_11,A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_259])).

tff(c_32,plain,(
    ~ r1_tarski(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k3_relat_1 > k1_wellord2 > k1_setfam_1 > #skF_3 > #skF_2 > #skF_1
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.18  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.87/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.18  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.87/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.18  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.87/1.18  
% 1.87/1.19  tff(f_57, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.87/1.19  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 1.87/1.19  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord1)).
% 1.87/1.19  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 1.87/1.19  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.87/1.19  tff(f_31, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.87/1.19  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.87/1.19  tff(f_60, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 1.87/1.19  tff(c_30, plain, (![A_19]: (v1_relat_1(k1_wellord2(A_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.19  tff(c_24, plain, (![A_11]: (k3_relat_1(k1_wellord2(A_11))=A_11 | ~v1_relat_1(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.19  tff(c_38, plain, (![A_11]: (k3_relat_1(k1_wellord2(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24])).
% 1.87/1.19  tff(c_83, plain, (![A_26]: (k2_wellord1(A_26, k3_relat_1(A_26))=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.87/1.19  tff(c_92, plain, (![A_11]: (k2_wellord1(k1_wellord2(A_11), A_11)=k1_wellord2(A_11) | ~v1_relat_1(k1_wellord2(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_83])).
% 1.87/1.19  tff(c_96, plain, (![A_11]: (k2_wellord1(k1_wellord2(A_11), A_11)=k1_wellord2(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_92])).
% 1.87/1.19  tff(c_8, plain, (![A_7, B_9]: (k3_xboole_0(A_7, k2_zfmisc_1(B_9, B_9))=k2_wellord1(A_7, B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.87/1.19  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.19  tff(c_106, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.19  tff(c_121, plain, (![B_30, A_31]: (k1_setfam_1(k2_tarski(B_30, A_31))=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_4, c_106])).
% 1.87/1.19  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.19  tff(c_156, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_121, c_6])).
% 1.87/1.19  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.19  tff(c_209, plain, (![B_36, A_37]: (r1_tarski(k3_xboole_0(B_36, A_37), A_37))), inference(superposition, [status(thm), theory('equality')], [c_156, c_2])).
% 1.87/1.19  tff(c_256, plain, (![A_44, B_45]: (r1_tarski(k2_wellord1(A_44, B_45), k2_zfmisc_1(B_45, B_45)) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_8, c_209])).
% 1.87/1.19  tff(c_259, plain, (![A_11]: (r1_tarski(k1_wellord2(A_11), k2_zfmisc_1(A_11, A_11)) | ~v1_relat_1(k1_wellord2(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_256])).
% 1.87/1.19  tff(c_264, plain, (![A_11]: (r1_tarski(k1_wellord2(A_11), k2_zfmisc_1(A_11, A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_259])).
% 1.87/1.19  tff(c_32, plain, (~r1_tarski(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.19  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_32])).
% 1.87/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  Inference rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Ref     : 0
% 1.87/1.19  #Sup     : 53
% 1.87/1.19  #Fact    : 0
% 1.87/1.19  #Define  : 0
% 1.87/1.19  #Split   : 0
% 1.87/1.19  #Chain   : 0
% 1.87/1.19  #Close   : 0
% 1.87/1.19  
% 1.87/1.19  Ordering : KBO
% 1.87/1.19  
% 1.87/1.19  Simplification rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Subsume      : 1
% 1.87/1.19  #Demod        : 25
% 1.87/1.19  #Tautology    : 40
% 1.87/1.19  #SimpNegUnit  : 0
% 1.87/1.19  #BackRed      : 1
% 1.87/1.19  
% 1.87/1.19  #Partial instantiations: 0
% 1.87/1.19  #Strategies tried      : 1
% 1.87/1.19  
% 1.87/1.19  Timing (in seconds)
% 1.87/1.19  ----------------------
% 1.87/1.19  Preprocessing        : 0.27
% 1.87/1.19  Parsing              : 0.14
% 1.87/1.19  CNF conversion       : 0.02
% 1.87/1.19  Main loop            : 0.16
% 1.87/1.19  Inferencing          : 0.06
% 1.87/1.19  Reduction            : 0.05
% 1.87/1.19  Demodulation         : 0.04
% 1.87/1.19  BG Simplification    : 0.01
% 1.87/1.19  Subsumption          : 0.02
% 1.87/1.19  Abstraction          : 0.01
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.20  Total                : 0.46
% 1.87/1.20  Index Insertion      : 0.00
% 1.87/1.20  Index Deletion       : 0.00
% 1.87/1.20  Index Matching       : 0.00
% 1.87/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
