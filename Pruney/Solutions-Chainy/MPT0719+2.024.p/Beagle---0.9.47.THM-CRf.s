%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:46 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  63 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 115 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
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

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_45,plain,(
    ! [A_21] :
      ( v1_funct_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_2'(A_31,B_32),k1_relat_1(B_32))
      | v5_funct_1(B_32,A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_2'(A_31,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_31)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_66])).

tff(c_71,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_2'(A_31,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_49,c_69])).

tff(c_90,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_2'(A_39,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_49,c_69])).

tff(c_10,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,B_27)
      | ~ r2_hidden(C_28,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_55,plain,(
    ! [C_28,A_6] :
      ( ~ r2_hidden(C_28,k1_xboole_0)
      | ~ r2_hidden(C_28,A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_52])).

tff(c_94,plain,(
    ! [A_40,A_41] :
      ( ~ r2_hidden('#skF_2'(A_40,k1_xboole_0),A_41)
      | v5_funct_1(k1_xboole_0,A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_90,c_55])).

tff(c_106,plain,(
    ! [A_42] :
      ( v5_funct_1(k1_xboole_0,A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_71,c_94])).

tff(c_26,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_109,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_26])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.68  
% 2.14/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.68  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.14/1.68  
% 2.14/1.68  %Foreground sorts:
% 2.14/1.68  
% 2.14/1.68  
% 2.14/1.68  %Background operators:
% 2.14/1.68  
% 2.14/1.68  
% 2.14/1.68  %Foreground operators:
% 2.14/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.68  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.14/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.68  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.14/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.68  
% 2.21/1.70  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.21/1.70  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.21/1.70  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.21/1.70  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.21/1.70  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.21/1.70  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.21/1.70  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.21/1.70  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.21/1.70  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.70  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.70  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.21/1.70  tff(c_40, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.70  tff(c_44, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_40])).
% 2.21/1.70  tff(c_45, plain, (![A_21]: (v1_funct_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.21/1.70  tff(c_49, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_45])).
% 2.21/1.70  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.70  tff(c_66, plain, (![A_31, B_32]: (r2_hidden('#skF_2'(A_31, B_32), k1_relat_1(B_32)) | v5_funct_1(B_32, A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.21/1.70  tff(c_69, plain, (![A_31]: (r2_hidden('#skF_2'(A_31, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_31) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_16, c_66])).
% 2.21/1.70  tff(c_71, plain, (![A_31]: (r2_hidden('#skF_2'(A_31, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_49, c_69])).
% 2.21/1.70  tff(c_90, plain, (![A_39]: (r2_hidden('#skF_2'(A_39, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_49, c_69])).
% 2.21/1.70  tff(c_10, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.70  tff(c_52, plain, (![A_26, B_27, C_28]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_28, B_27) | ~r2_hidden(C_28, A_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.70  tff(c_55, plain, (![C_28, A_6]: (~r2_hidden(C_28, k1_xboole_0) | ~r2_hidden(C_28, A_6))), inference(resolution, [status(thm)], [c_10, c_52])).
% 2.21/1.70  tff(c_94, plain, (![A_40, A_41]: (~r2_hidden('#skF_2'(A_40, k1_xboole_0), A_41) | v5_funct_1(k1_xboole_0, A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_90, c_55])).
% 2.21/1.70  tff(c_106, plain, (![A_42]: (v5_funct_1(k1_xboole_0, A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(resolution, [status(thm)], [c_71, c_94])).
% 2.21/1.70  tff(c_26, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.70  tff(c_109, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_26])).
% 2.21/1.70  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_109])).
% 2.21/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.70  
% 2.21/1.70  Inference rules
% 2.21/1.70  ----------------------
% 2.21/1.70  #Ref     : 0
% 2.21/1.70  #Sup     : 17
% 2.21/1.70  #Fact    : 0
% 2.21/1.70  #Define  : 0
% 2.21/1.70  #Split   : 0
% 2.21/1.70  #Chain   : 0
% 2.21/1.70  #Close   : 0
% 2.21/1.70  
% 2.21/1.70  Ordering : KBO
% 2.21/1.70  
% 2.21/1.70  Simplification rules
% 2.21/1.70  ----------------------
% 2.21/1.70  #Subsume      : 3
% 2.21/1.70  #Demod        : 9
% 2.21/1.70  #Tautology    : 7
% 2.21/1.70  #SimpNegUnit  : 0
% 2.21/1.70  #BackRed      : 0
% 2.21/1.70  
% 2.21/1.70  #Partial instantiations: 0
% 2.21/1.70  #Strategies tried      : 1
% 2.21/1.70  
% 2.21/1.70  Timing (in seconds)
% 2.21/1.70  ----------------------
% 2.21/1.70  Preprocessing        : 0.51
% 2.21/1.70  Parsing              : 0.30
% 2.21/1.70  CNF conversion       : 0.04
% 2.21/1.70  Main loop            : 0.24
% 2.21/1.71  Inferencing          : 0.10
% 2.21/1.71  Reduction            : 0.07
% 2.21/1.71  Demodulation         : 0.06
% 2.21/1.71  BG Simplification    : 0.02
% 2.21/1.71  Subsumption          : 0.04
% 2.21/1.71  Abstraction          : 0.01
% 2.21/1.71  MUC search           : 0.00
% 2.21/1.71  Cooper               : 0.00
% 2.21/1.71  Total                : 0.80
% 2.21/1.71  Index Insertion      : 0.00
% 2.21/1.71  Index Deletion       : 0.00
% 2.21/1.71  Index Matching       : 0.00
% 2.21/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
