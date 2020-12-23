%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:36 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   42 (  60 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 155 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_wellord1 > r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ~ ( v2_wellord1(A)
            & k3_relat_1(A) != k1_xboole_0
            & ! [B] :
                ~ ( r2_hidden(B,k3_relat_1(A))
                  & ! [C] :
                      ( r2_hidden(C,k3_relat_1(A))
                     => r2_hidden(k4_tarski(B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( r2_wellord1(A,k3_relat_1(A))
      <=> v2_wellord1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_wellord1(B,A)
       => ! [C] :
            ~ ( r1_tarski(C,A)
              & C != k1_xboole_0
              & ! [D] :
                  ~ ( r2_hidden(D,C)
                    & ! [E] :
                        ( r2_hidden(E,C)
                       => r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    v2_wellord1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_wellord1(A_6,k3_relat_1(A_6))
      | ~ v2_wellord1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_1'(A_31,B_32),A_31)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_31] : r1_tarski(A_31,A_31) ),
    inference(resolution,[status(thm)],[c_32,c_4])).

tff(c_16,plain,(
    k3_relat_1('#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_69,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_2'(A_51,B_52,C_53),C_53)
      | k1_xboole_0 = C_53
      | ~ r1_tarski(C_53,A_51)
      | ~ r2_wellord1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_51,B_52,C_53,B_2] :
      ( r2_hidden('#skF_2'(A_51,B_52,C_53),B_2)
      | ~ r1_tarski(C_53,B_2)
      | k1_xboole_0 = C_53
      | ~ r1_tarski(C_53,A_51)
      | ~ r2_wellord1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_24,plain,(
    ! [B_25] :
      ( r2_hidden('#skF_4'(B_25),k3_relat_1('#skF_3'))
      | ~ r2_hidden(B_25,k3_relat_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_77,plain,(
    ! [A_58,B_59,C_60,E_61] :
      ( r2_hidden(k4_tarski('#skF_2'(A_58,B_59,C_60),E_61),B_59)
      | ~ r2_hidden(E_61,C_60)
      | k1_xboole_0 = C_60
      | ~ r1_tarski(C_60,A_58)
      | ~ r2_wellord1(B_59,A_58)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [B_25] :
      ( ~ r2_hidden(k4_tarski(B_25,'#skF_4'(B_25)),'#skF_3')
      | ~ r2_hidden(B_25,k3_relat_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_83,plain,(
    ! [A_58,C_60] :
      ( ~ r2_hidden('#skF_2'(A_58,'#skF_3',C_60),k3_relat_1('#skF_3'))
      | ~ r2_hidden('#skF_4'('#skF_2'(A_58,'#skF_3',C_60)),C_60)
      | k1_xboole_0 = C_60
      | ~ r1_tarski(C_60,A_58)
      | ~ r2_wellord1('#skF_3',A_58)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_77,c_22])).

tff(c_88,plain,(
    ! [A_62,C_63] :
      ( ~ r2_hidden('#skF_2'(A_62,'#skF_3',C_63),k3_relat_1('#skF_3'))
      | ~ r2_hidden('#skF_4'('#skF_2'(A_62,'#skF_3',C_63)),C_63)
      | k1_xboole_0 = C_63
      | ~ r1_tarski(C_63,A_62)
      | ~ r2_wellord1('#skF_3',A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_83])).

tff(c_96,plain,(
    ! [A_62] :
      ( k3_relat_1('#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_relat_1('#skF_3'),A_62)
      | ~ r2_wellord1('#skF_3',A_62)
      | ~ r2_hidden('#skF_2'(A_62,'#skF_3',k3_relat_1('#skF_3')),k3_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_88])).

tff(c_101,plain,(
    ! [A_64] :
      ( ~ r1_tarski(k3_relat_1('#skF_3'),A_64)
      | ~ r2_wellord1('#skF_3',A_64)
      | ~ r2_hidden('#skF_2'(A_64,'#skF_3',k3_relat_1('#skF_3')),k3_relat_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_96])).

tff(c_105,plain,(
    ! [A_51] :
      ( ~ r1_tarski(k3_relat_1('#skF_3'),k3_relat_1('#skF_3'))
      | k3_relat_1('#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_relat_1('#skF_3'),A_51)
      | ~ r2_wellord1('#skF_3',A_51)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_72,c_101])).

tff(c_112,plain,(
    ! [A_51] :
      ( k3_relat_1('#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_relat_1('#skF_3'),A_51)
      | ~ r2_wellord1('#skF_3',A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_37,c_105])).

tff(c_118,plain,(
    ! [A_65] :
      ( ~ r1_tarski(k3_relat_1('#skF_3'),A_65)
      | ~ r2_wellord1('#skF_3',A_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_112])).

tff(c_123,plain,(
    ~ r2_wellord1('#skF_3',k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37,c_118])).

tff(c_126,plain,
    ( ~ v2_wellord1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_123])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:13:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.23  
% 2.24/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.23  %$ r2_wellord1 > r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.24/1.23  
% 2.24/1.23  %Foreground sorts:
% 2.24/1.23  
% 2.24/1.23  
% 2.24/1.23  %Background operators:
% 2.24/1.23  
% 2.24/1.23  
% 2.24/1.23  %Foreground operators:
% 2.24/1.23  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.24/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.24/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.24/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.23  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.24/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.24/1.23  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.24/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.23  
% 2.24/1.24  tff(f_76, negated_conjecture, ~(![A]: (v1_relat_1(A) => ~((v2_wellord1(A) & ~(k3_relat_1(A) = k1_xboole_0)) & (![B]: ~(r2_hidden(B, k3_relat_1(A)) & (![C]: (r2_hidden(C, k3_relat_1(A)) => r2_hidden(k4_tarski(B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord1)).
% 2.24/1.24  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (r2_wellord1(A, k3_relat_1(A)) <=> v2_wellord1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord1)).
% 2.24/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.24/1.24  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r2_wellord1(B, A) => (![C]: ~((r1_tarski(C, A) & ~(C = k1_xboole_0)) & (![D]: ~(r2_hidden(D, C) & (![E]: (r2_hidden(E, C) => r2_hidden(k4_tarski(D, E), B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_wellord1)).
% 2.24/1.24  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.24  tff(c_18, plain, (v2_wellord1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.24  tff(c_8, plain, (![A_6]: (r2_wellord1(A_6, k3_relat_1(A_6)) | ~v2_wellord1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.24/1.24  tff(c_32, plain, (![A_31, B_32]: (r2_hidden('#skF_1'(A_31, B_32), A_31) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.24  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.24  tff(c_37, plain, (![A_31]: (r1_tarski(A_31, A_31))), inference(resolution, [status(thm)], [c_32, c_4])).
% 2.24/1.24  tff(c_16, plain, (k3_relat_1('#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.24  tff(c_69, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_2'(A_51, B_52, C_53), C_53) | k1_xboole_0=C_53 | ~r1_tarski(C_53, A_51) | ~r2_wellord1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.24  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.24  tff(c_72, plain, (![A_51, B_52, C_53, B_2]: (r2_hidden('#skF_2'(A_51, B_52, C_53), B_2) | ~r1_tarski(C_53, B_2) | k1_xboole_0=C_53 | ~r1_tarski(C_53, A_51) | ~r2_wellord1(B_52, A_51) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_69, c_2])).
% 2.24/1.24  tff(c_24, plain, (![B_25]: (r2_hidden('#skF_4'(B_25), k3_relat_1('#skF_3')) | ~r2_hidden(B_25, k3_relat_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.24  tff(c_77, plain, (![A_58, B_59, C_60, E_61]: (r2_hidden(k4_tarski('#skF_2'(A_58, B_59, C_60), E_61), B_59) | ~r2_hidden(E_61, C_60) | k1_xboole_0=C_60 | ~r1_tarski(C_60, A_58) | ~r2_wellord1(B_59, A_58) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.24  tff(c_22, plain, (![B_25]: (~r2_hidden(k4_tarski(B_25, '#skF_4'(B_25)), '#skF_3') | ~r2_hidden(B_25, k3_relat_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.24  tff(c_83, plain, (![A_58, C_60]: (~r2_hidden('#skF_2'(A_58, '#skF_3', C_60), k3_relat_1('#skF_3')) | ~r2_hidden('#skF_4'('#skF_2'(A_58, '#skF_3', C_60)), C_60) | k1_xboole_0=C_60 | ~r1_tarski(C_60, A_58) | ~r2_wellord1('#skF_3', A_58) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_77, c_22])).
% 2.24/1.24  tff(c_88, plain, (![A_62, C_63]: (~r2_hidden('#skF_2'(A_62, '#skF_3', C_63), k3_relat_1('#skF_3')) | ~r2_hidden('#skF_4'('#skF_2'(A_62, '#skF_3', C_63)), C_63) | k1_xboole_0=C_63 | ~r1_tarski(C_63, A_62) | ~r2_wellord1('#skF_3', A_62))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_83])).
% 2.24/1.24  tff(c_96, plain, (![A_62]: (k3_relat_1('#skF_3')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_3'), A_62) | ~r2_wellord1('#skF_3', A_62) | ~r2_hidden('#skF_2'(A_62, '#skF_3', k3_relat_1('#skF_3')), k3_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_24, c_88])).
% 2.24/1.24  tff(c_101, plain, (![A_64]: (~r1_tarski(k3_relat_1('#skF_3'), A_64) | ~r2_wellord1('#skF_3', A_64) | ~r2_hidden('#skF_2'(A_64, '#skF_3', k3_relat_1('#skF_3')), k3_relat_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_16, c_96])).
% 2.24/1.24  tff(c_105, plain, (![A_51]: (~r1_tarski(k3_relat_1('#skF_3'), k3_relat_1('#skF_3')) | k3_relat_1('#skF_3')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_3'), A_51) | ~r2_wellord1('#skF_3', A_51) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_101])).
% 2.24/1.24  tff(c_112, plain, (![A_51]: (k3_relat_1('#skF_3')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_3'), A_51) | ~r2_wellord1('#skF_3', A_51))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_37, c_105])).
% 2.24/1.24  tff(c_118, plain, (![A_65]: (~r1_tarski(k3_relat_1('#skF_3'), A_65) | ~r2_wellord1('#skF_3', A_65))), inference(negUnitSimplification, [status(thm)], [c_16, c_112])).
% 2.24/1.24  tff(c_123, plain, (~r2_wellord1('#skF_3', k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_37, c_118])).
% 2.24/1.24  tff(c_126, plain, (~v2_wellord1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_123])).
% 2.24/1.24  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_126])).
% 2.24/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.24  
% 2.24/1.24  Inference rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Ref     : 0
% 2.24/1.24  #Sup     : 19
% 2.24/1.24  #Fact    : 0
% 2.24/1.24  #Define  : 0
% 2.24/1.24  #Split   : 0
% 2.24/1.24  #Chain   : 0
% 2.24/1.24  #Close   : 0
% 2.24/1.24  
% 2.24/1.24  Ordering : KBO
% 2.24/1.24  
% 2.24/1.24  Simplification rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Subsume      : 3
% 2.24/1.24  #Demod        : 6
% 2.24/1.24  #Tautology    : 2
% 2.24/1.24  #SimpNegUnit  : 3
% 2.24/1.24  #BackRed      : 0
% 2.24/1.24  
% 2.24/1.24  #Partial instantiations: 0
% 2.24/1.24  #Strategies tried      : 1
% 2.24/1.24  
% 2.24/1.24  Timing (in seconds)
% 2.24/1.24  ----------------------
% 2.33/1.24  Preprocessing        : 0.27
% 2.33/1.24  Parsing              : 0.15
% 2.33/1.24  CNF conversion       : 0.02
% 2.33/1.24  Main loop            : 0.17
% 2.33/1.25  Inferencing          : 0.08
% 2.33/1.25  Reduction            : 0.04
% 2.33/1.25  Demodulation         : 0.03
% 2.33/1.25  BG Simplification    : 0.01
% 2.33/1.25  Subsumption          : 0.04
% 2.33/1.25  Abstraction          : 0.01
% 2.33/1.25  MUC search           : 0.00
% 2.33/1.25  Cooper               : 0.00
% 2.33/1.25  Total                : 0.47
% 2.33/1.25  Index Insertion      : 0.00
% 2.33/1.25  Index Deletion       : 0.00
% 2.33/1.25  Index Matching       : 0.00
% 2.33/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
