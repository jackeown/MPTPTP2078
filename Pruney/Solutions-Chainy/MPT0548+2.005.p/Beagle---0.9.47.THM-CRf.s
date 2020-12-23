%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:36 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  54 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    ! [A_23,B_24] : ~ r2_hidden(A_23,k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_64])).

tff(c_76,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_64])).

tff(c_81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_76])).

tff(c_16,plain,(
    ! [A_10] :
      ( v1_relat_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_81,c_16])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_137,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden('#skF_2'(A_36,B_37,C_38),k1_relat_1(C_38))
      | ~ r2_hidden(A_36,k9_relat_1(C_38,B_37))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_2'(A_36,B_37,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_36,k9_relat_1(k1_xboole_0,B_37))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_137])).

tff(c_146,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_2'(A_36,B_37,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_36,k9_relat_1(k1_xboole_0,B_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_143])).

tff(c_162,plain,(
    ! [A_39,B_40] : ~ r2_hidden(A_39,k9_relat_1(k1_xboole_0,B_40)) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_146])).

tff(c_175,plain,(
    ! [B_41] : v1_xboole_0(k9_relat_1(k1_xboole_0,B_41)) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,(
    ! [B_41] : k9_relat_1(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_175,c_6])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.89/1.19  
% 1.89/1.19  %Foreground sorts:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Background operators:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Foreground operators:
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.89/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.89/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.89/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.19  
% 1.89/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.89/1.20  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.89/1.20  tff(f_44, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.89/1.20  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.89/1.20  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.89/1.20  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.89/1.20  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.89/1.20  tff(f_65, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.89/1.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.20  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.89/1.20  tff(c_64, plain, (![A_23, B_24]: (~r2_hidden(A_23, k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.20  tff(c_67, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_64])).
% 1.89/1.20  tff(c_76, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_64])).
% 1.89/1.20  tff(c_81, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_76])).
% 1.89/1.20  tff(c_16, plain, (![A_10]: (v1_relat_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.20  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_16])).
% 1.89/1.20  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.20  tff(c_137, plain, (![A_36, B_37, C_38]: (r2_hidden('#skF_2'(A_36, B_37, C_38), k1_relat_1(C_38)) | ~r2_hidden(A_36, k9_relat_1(C_38, B_37)) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.89/1.20  tff(c_143, plain, (![A_36, B_37]: (r2_hidden('#skF_2'(A_36, B_37, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_36, k9_relat_1(k1_xboole_0, B_37)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_137])).
% 1.89/1.20  tff(c_146, plain, (![A_36, B_37]: (r2_hidden('#skF_2'(A_36, B_37, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_36, k9_relat_1(k1_xboole_0, B_37)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_143])).
% 1.89/1.20  tff(c_162, plain, (![A_39, B_40]: (~r2_hidden(A_39, k9_relat_1(k1_xboole_0, B_40)))), inference(negUnitSimplification, [status(thm)], [c_67, c_146])).
% 1.89/1.20  tff(c_175, plain, (![B_41]: (v1_xboole_0(k9_relat_1(k1_xboole_0, B_41)))), inference(resolution, [status(thm)], [c_4, c_162])).
% 1.89/1.20  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.20  tff(c_184, plain, (![B_41]: (k9_relat_1(k1_xboole_0, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_175, c_6])).
% 1.89/1.20  tff(c_30, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_30])).
% 1.89/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  Inference rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Ref     : 0
% 1.89/1.20  #Sup     : 37
% 1.89/1.20  #Fact    : 0
% 1.89/1.20  #Define  : 0
% 1.89/1.20  #Split   : 0
% 1.89/1.20  #Chain   : 0
% 1.89/1.20  #Close   : 0
% 1.89/1.20  
% 1.89/1.20  Ordering : KBO
% 1.89/1.20  
% 1.89/1.20  Simplification rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Subsume      : 4
% 1.89/1.20  #Demod        : 10
% 1.89/1.20  #Tautology    : 20
% 1.89/1.20  #SimpNegUnit  : 1
% 1.89/1.20  #BackRed      : 3
% 1.89/1.20  
% 1.89/1.20  #Partial instantiations: 0
% 1.89/1.20  #Strategies tried      : 1
% 1.89/1.20  
% 1.89/1.20  Timing (in seconds)
% 1.89/1.20  ----------------------
% 1.89/1.20  Preprocessing        : 0.28
% 1.89/1.20  Parsing              : 0.16
% 1.89/1.20  CNF conversion       : 0.02
% 1.89/1.20  Main loop            : 0.14
% 1.89/1.20  Inferencing          : 0.06
% 1.89/1.20  Reduction            : 0.04
% 1.89/1.20  Demodulation         : 0.03
% 1.89/1.20  BG Simplification    : 0.01
% 1.89/1.20  Subsumption          : 0.02
% 1.89/1.20  Abstraction          : 0.01
% 1.89/1.20  MUC search           : 0.00
% 1.89/1.20  Cooper               : 0.00
% 1.89/1.20  Total                : 0.44
% 1.89/1.20  Index Insertion      : 0.00
% 1.89/1.20  Index Deletion       : 0.00
% 1.89/1.20  Index Matching       : 0.00
% 1.89/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
