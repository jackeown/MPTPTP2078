%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:47 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  56 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_20,B_21] : ~ r2_hidden(A_20,k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73,plain,(
    ! [A_24] : ~ r2_hidden(A_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_78,plain,(
    ! [B_2] : r1_xboole_0(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    ! [B_38,A_39] :
      ( k7_relat_1(B_38,A_39) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_38),A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_133,plain,(
    ! [A_39] :
      ( k7_relat_1(k1_xboole_0,A_39) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_39)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_123])).

tff(c_138,plain,(
    ! [A_40] : k7_relat_1(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_78,c_133])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_143,plain,(
    ! [A_40] :
      ( k9_relat_1(k1_xboole_0,A_40) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_18])).

tff(c_148,plain,(
    ! [A_40] : k9_relat_1(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_20,c_143])).

tff(c_28,plain,(
    k9_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.21  
% 1.86/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.22  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.86/1.22  
% 1.86/1.22  %Foreground sorts:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Background operators:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Foreground operators:
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.86/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.86/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.22  
% 1.94/1.24  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.94/1.24  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.94/1.24  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.94/1.24  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.94/1.24  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.94/1.24  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.94/1.24  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.94/1.24  tff(f_70, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.94/1.24  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.24  tff(c_59, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.24  tff(c_61, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_59])).
% 1.94/1.24  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.24  tff(c_65, plain, (![A_20, B_21]: (~r2_hidden(A_20, k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.24  tff(c_73, plain, (![A_24]: (~r2_hidden(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_65])).
% 1.94/1.24  tff(c_78, plain, (![B_2]: (r1_xboole_0(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_73])).
% 1.94/1.24  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.24  tff(c_123, plain, (![B_38, A_39]: (k7_relat_1(B_38, A_39)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_38), A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.94/1.24  tff(c_133, plain, (![A_39]: (k7_relat_1(k1_xboole_0, A_39)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_39) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_123])).
% 1.94/1.24  tff(c_138, plain, (![A_40]: (k7_relat_1(k1_xboole_0, A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_78, c_133])).
% 1.94/1.24  tff(c_18, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.24  tff(c_143, plain, (![A_40]: (k9_relat_1(k1_xboole_0, A_40)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_138, c_18])).
% 1.94/1.24  tff(c_148, plain, (![A_40]: (k9_relat_1(k1_xboole_0, A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_20, c_143])).
% 1.94/1.24  tff(c_28, plain, (k9_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.24  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_28])).
% 1.94/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  Inference rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Ref     : 0
% 1.94/1.24  #Sup     : 30
% 1.94/1.24  #Fact    : 0
% 1.94/1.24  #Define  : 0
% 1.94/1.24  #Split   : 0
% 1.94/1.24  #Chain   : 0
% 1.94/1.24  #Close   : 0
% 1.94/1.24  
% 1.94/1.24  Ordering : KBO
% 1.94/1.24  
% 1.94/1.24  Simplification rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Subsume      : 3
% 1.94/1.24  #Demod        : 8
% 1.94/1.24  #Tautology    : 19
% 1.94/1.24  #SimpNegUnit  : 0
% 1.94/1.24  #BackRed      : 1
% 1.94/1.24  
% 1.94/1.24  #Partial instantiations: 0
% 1.94/1.24  #Strategies tried      : 1
% 1.94/1.24  
% 1.94/1.24  Timing (in seconds)
% 1.94/1.24  ----------------------
% 1.94/1.24  Preprocessing        : 0.26
% 1.94/1.24  Parsing              : 0.14
% 1.94/1.24  CNF conversion       : 0.02
% 1.94/1.24  Main loop            : 0.15
% 1.94/1.24  Inferencing          : 0.07
% 1.94/1.24  Reduction            : 0.04
% 1.94/1.24  Demodulation         : 0.03
% 1.94/1.24  BG Simplification    : 0.01
% 1.94/1.24  Subsumption          : 0.02
% 1.94/1.24  Abstraction          : 0.01
% 1.94/1.25  MUC search           : 0.00
% 1.94/1.25  Cooper               : 0.00
% 1.94/1.25  Total                : 0.45
% 1.94/1.25  Index Insertion      : 0.00
% 1.94/1.25  Index Deletion       : 0.00
% 1.94/1.25  Index Matching       : 0.00
% 1.94/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
