%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:46 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   45 (  53 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  62 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_112,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_1'(A_37,B_38),B_38)
      | r2_hidden('#skF_2'(A_37,B_38),A_37)
      | B_38 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_94,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,k3_xboole_0(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_97,plain,(
    ! [A_9,C_31] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_31,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_94])).

tff(c_99,plain,(
    ! [C_31] : ~ r2_hidden(C_31,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_97])).

tff(c_129,plain,(
    ! [B_38] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_38),B_38)
      | k1_xboole_0 = B_38 ) ),
    inference(resolution,[status(thm)],[c_112,c_99])).

tff(c_49,plain,(
    ! [B_24] : k2_zfmisc_1(k1_xboole_0,B_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_24])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_286,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden('#skF_4'(A_57,B_58,C_59),k1_relat_1(C_59))
      | ~ r2_hidden(A_57,k9_relat_1(C_59,B_58))
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_289,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_4'(A_57,B_58,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_57,k9_relat_1(k1_xboole_0,B_58))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_286])).

tff(c_291,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_4'(A_57,B_58,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_57,k9_relat_1(k1_xboole_0,B_58)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_289])).

tff(c_293,plain,(
    ! [A_60,B_61] : ~ r2_hidden(A_60,k9_relat_1(k1_xboole_0,B_61)) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_291])).

tff(c_318,plain,(
    ! [B_61] : k9_relat_1(k1_xboole_0,B_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_293])).

tff(c_38,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.24  
% 1.88/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.24  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 1.88/1.24  
% 1.88/1.24  %Foreground sorts:
% 1.88/1.24  
% 1.88/1.24  
% 1.88/1.24  %Background operators:
% 1.88/1.24  
% 1.88/1.24  
% 1.88/1.24  %Foreground operators:
% 1.88/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.88/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.88/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.88/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.24  
% 1.88/1.25  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.88/1.25  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.88/1.25  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.88/1.25  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.88/1.25  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.88/1.25  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.88/1.25  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.25  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 1.88/1.25  tff(f_75, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.88/1.25  tff(c_112, plain, (![A_37, B_38]: (r2_hidden('#skF_1'(A_37, B_38), B_38) | r2_hidden('#skF_2'(A_37, B_38), A_37) | B_38=A_37)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.25  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.25  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.25  tff(c_94, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.25  tff(c_97, plain, (![A_9, C_31]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_94])).
% 1.88/1.25  tff(c_99, plain, (![C_31]: (~r2_hidden(C_31, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_97])).
% 1.88/1.25  tff(c_129, plain, (![B_38]: (r2_hidden('#skF_1'(k1_xboole_0, B_38), B_38) | k1_xboole_0=B_38)), inference(resolution, [status(thm)], [c_112, c_99])).
% 1.88/1.25  tff(c_49, plain, (![B_24]: (k2_zfmisc_1(k1_xboole_0, B_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.25  tff(c_24, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.25  tff(c_53, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_49, c_24])).
% 1.88/1.25  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.88/1.25  tff(c_286, plain, (![A_57, B_58, C_59]: (r2_hidden('#skF_4'(A_57, B_58, C_59), k1_relat_1(C_59)) | ~r2_hidden(A_57, k9_relat_1(C_59, B_58)) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.88/1.25  tff(c_289, plain, (![A_57, B_58]: (r2_hidden('#skF_4'(A_57, B_58, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_57, k9_relat_1(k1_xboole_0, B_58)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_286])).
% 1.88/1.25  tff(c_291, plain, (![A_57, B_58]: (r2_hidden('#skF_4'(A_57, B_58, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_57, k9_relat_1(k1_xboole_0, B_58)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_289])).
% 1.88/1.25  tff(c_293, plain, (![A_60, B_61]: (~r2_hidden(A_60, k9_relat_1(k1_xboole_0, B_61)))), inference(negUnitSimplification, [status(thm)], [c_99, c_291])).
% 1.88/1.25  tff(c_318, plain, (![B_61]: (k9_relat_1(k1_xboole_0, B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_129, c_293])).
% 1.88/1.25  tff(c_38, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.88/1.25  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_38])).
% 1.88/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.25  
% 1.88/1.25  Inference rules
% 1.88/1.25  ----------------------
% 1.88/1.25  #Ref     : 0
% 1.88/1.25  #Sup     : 61
% 1.88/1.25  #Fact    : 0
% 1.88/1.25  #Define  : 0
% 1.88/1.25  #Split   : 0
% 1.88/1.25  #Chain   : 0
% 1.88/1.25  #Close   : 0
% 1.88/1.25  
% 1.88/1.25  Ordering : KBO
% 1.88/1.25  
% 1.88/1.25  Simplification rules
% 1.88/1.25  ----------------------
% 1.88/1.25  #Subsume      : 12
% 1.88/1.25  #Demod        : 14
% 1.88/1.25  #Tautology    : 28
% 1.88/1.25  #SimpNegUnit  : 2
% 1.88/1.25  #BackRed      : 2
% 1.88/1.25  
% 1.88/1.25  #Partial instantiations: 0
% 1.88/1.25  #Strategies tried      : 1
% 1.88/1.25  
% 1.88/1.25  Timing (in seconds)
% 1.88/1.25  ----------------------
% 1.88/1.25  Preprocessing        : 0.28
% 1.88/1.25  Parsing              : 0.15
% 1.88/1.25  CNF conversion       : 0.02
% 1.88/1.25  Main loop            : 0.19
% 1.88/1.25  Inferencing          : 0.08
% 1.88/1.25  Reduction            : 0.05
% 1.88/1.25  Demodulation         : 0.04
% 1.88/1.25  BG Simplification    : 0.01
% 1.88/1.25  Subsumption          : 0.03
% 1.88/1.25  Abstraction          : 0.01
% 1.88/1.25  MUC search           : 0.00
% 1.88/1.25  Cooper               : 0.00
% 1.88/1.25  Total                : 0.49
% 1.88/1.25  Index Insertion      : 0.00
% 1.88/1.25  Index Deletion       : 0.00
% 1.88/1.26  Index Matching       : 0.00
% 1.88/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
