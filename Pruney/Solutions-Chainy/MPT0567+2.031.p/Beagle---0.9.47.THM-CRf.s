%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:18 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  71 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_26,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_2'(A_10,B_11,C_12),B_11)
      | ~ r2_hidden(A_10,k10_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(k1_tarski(A_27),B_28) = B_28
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_77,plain,(
    ! [A_27] : ~ r2_hidden(A_27,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k3_xboole_0(A_23,B_24))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    ! [A_3] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_50,plain,(
    ! [A_3] : ~ v1_relat_1(A_3) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_64,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_28])).

tff(c_65,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_3'(A_31,B_32),k1_relat_1(B_32))
      | ~ r2_hidden(A_31,k2_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_89,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_3'(A_31,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_31,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_83])).

tff(c_92,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_3'(A_31,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_31,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_22,c_89])).

tff(c_99,plain,(
    ! [A_36] : ~ r2_hidden(A_36,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_92])).

tff(c_111,plain,(
    ! [A_37,C_38] :
      ( ~ r2_hidden(A_37,k10_relat_1(C_38,k1_xboole_0))
      | ~ v1_relat_1(C_38) ) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_122,plain,(
    ! [C_39] :
      ( ~ v1_relat_1(C_39)
      | k10_relat_1(C_39,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_111])).

tff(c_131,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_122])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  %$ r2_hidden > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.88/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.88/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.19  
% 1.88/1.20  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.88/1.20  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.88/1.20  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.88/1.20  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.88/1.20  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.88/1.20  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.88/1.20  tff(f_46, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.88/1.20  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.20  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 1.88/1.20  tff(c_26, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.88/1.20  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.88/1.20  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.20  tff(c_14, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_2'(A_10, B_11, C_12), B_11) | ~r2_hidden(A_10, k10_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.20  tff(c_66, plain, (![A_27, B_28]: (k2_xboole_0(k1_tarski(A_27), B_28)=B_28 | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.20  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.20  tff(c_77, plain, (![A_27]: (~r2_hidden(A_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_8])).
% 1.88/1.20  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.20  tff(c_46, plain, (![A_23, B_24]: (v1_relat_1(k3_xboole_0(A_23, B_24)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.20  tff(c_49, plain, (![A_3]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_46])).
% 1.88/1.20  tff(c_50, plain, (![A_3]: (~v1_relat_1(A_3))), inference(splitLeft, [status(thm)], [c_49])).
% 1.88/1.20  tff(c_64, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_28])).
% 1.88/1.20  tff(c_65, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_49])).
% 1.88/1.20  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.88/1.20  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.88/1.20  tff(c_83, plain, (![A_31, B_32]: (r2_hidden('#skF_3'(A_31, B_32), k1_relat_1(B_32)) | ~r2_hidden(A_31, k2_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.20  tff(c_89, plain, (![A_31]: (r2_hidden('#skF_3'(A_31, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_31, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_83])).
% 1.88/1.20  tff(c_92, plain, (![A_31]: (r2_hidden('#skF_3'(A_31, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_31, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_22, c_89])).
% 1.88/1.20  tff(c_99, plain, (![A_36]: (~r2_hidden(A_36, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_77, c_92])).
% 1.88/1.20  tff(c_111, plain, (![A_37, C_38]: (~r2_hidden(A_37, k10_relat_1(C_38, k1_xboole_0)) | ~v1_relat_1(C_38))), inference(resolution, [status(thm)], [c_14, c_99])).
% 1.88/1.20  tff(c_122, plain, (![C_39]: (~v1_relat_1(C_39) | k10_relat_1(C_39, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_111])).
% 1.88/1.20  tff(c_131, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_122])).
% 1.88/1.20  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_131])).
% 1.88/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  Inference rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Ref     : 0
% 1.88/1.20  #Sup     : 24
% 1.88/1.20  #Fact    : 0
% 1.88/1.20  #Define  : 0
% 1.88/1.20  #Split   : 1
% 1.88/1.20  #Chain   : 0
% 1.88/1.20  #Close   : 0
% 1.88/1.20  
% 1.88/1.20  Ordering : KBO
% 1.88/1.20  
% 1.88/1.20  Simplification rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Subsume      : 1
% 1.88/1.20  #Demod        : 2
% 1.88/1.20  #Tautology    : 12
% 1.88/1.20  #SimpNegUnit  : 4
% 1.88/1.20  #BackRed      : 1
% 1.88/1.20  
% 1.88/1.20  #Partial instantiations: 0
% 1.88/1.20  #Strategies tried      : 1
% 1.88/1.20  
% 1.88/1.20  Timing (in seconds)
% 1.88/1.20  ----------------------
% 1.88/1.21  Preprocessing        : 0.29
% 1.88/1.21  Parsing              : 0.16
% 1.88/1.21  CNF conversion       : 0.02
% 1.88/1.21  Main loop            : 0.14
% 1.88/1.21  Inferencing          : 0.06
% 1.88/1.21  Reduction            : 0.03
% 1.88/1.21  Demodulation         : 0.02
% 1.88/1.21  BG Simplification    : 0.01
% 1.88/1.21  Subsumption          : 0.02
% 1.88/1.21  Abstraction          : 0.01
% 1.88/1.21  MUC search           : 0.00
% 1.88/1.21  Cooper               : 0.00
% 1.88/1.21  Total                : 0.46
% 1.88/1.21  Index Insertion      : 0.00
% 1.88/1.21  Index Deletion       : 0.00
% 1.88/1.21  Index Matching       : 0.00
% 1.88/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
