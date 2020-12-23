%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:38 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   52 (  73 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 134 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_61,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(k1_tarski(A_16),B_17)
      | r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,B_34)
      | ~ r2_hidden(C_35,A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_85,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,k1_tarski(A_45))
      | r2_hidden(A_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_131,plain,(
    ! [A_56,B_57,A_58] :
      ( ~ r2_hidden('#skF_1'(A_56,B_57),k1_tarski(A_58))
      | r2_hidden(A_58,A_56)
      | r1_xboole_0(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_158,plain,(
    ! [A_59,A_60] :
      ( r2_hidden(A_59,A_60)
      | r1_xboole_0(A_60,k1_tarski(A_59)) ) ),
    inference(resolution,[status(thm)],[c_4,c_131])).

tff(c_20,plain,(
    ! [B_21,A_20] :
      ( k10_relat_1(B_21,A_20) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_191,plain,(
    ! [B_64,A_65] :
      ( k10_relat_1(B_64,k1_tarski(A_65)) = k1_xboole_0
      | ~ v1_relat_1(B_64)
      | r2_hidden(A_65,k2_relat_1(B_64)) ) ),
    inference(resolution,[status(thm)],[c_158,c_20])).

tff(c_26,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_194,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_191,c_62])).

tff(c_197,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_194])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_197])).

tff(c_200,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_61])).

tff(c_208,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_211,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_26])).

tff(c_52,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),B_27)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [B_19] : ~ r1_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_57,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(resolution,[status(thm)],[c_52,c_18])).

tff(c_230,plain,(
    ! [B_72,A_73] :
      ( r1_xboole_0(k2_relat_1(B_72),A_73)
      | k10_relat_1(B_72,A_73) != k1_xboole_0
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_364,plain,(
    ! [C_98,A_99,B_100] :
      ( ~ r2_hidden(C_98,A_99)
      | ~ r2_hidden(C_98,k2_relat_1(B_100))
      | k10_relat_1(B_100,A_99) != k1_xboole_0
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_230,c_2])).

tff(c_422,plain,(
    ! [A_106,B_107] :
      ( ~ r2_hidden(A_106,k2_relat_1(B_107))
      | k10_relat_1(B_107,k1_tarski(A_106)) != k1_xboole_0
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_57,c_364])).

tff(c_431,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_208,c_422])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_211,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.34  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.34  
% 2.51/1.34  %Foreground sorts:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Background operators:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Foreground operators:
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.51/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.51/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.51/1.34  
% 2.51/1.36  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.51/1.36  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.51/1.36  tff(f_56, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.51/1.36  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.51/1.36  tff(f_61, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.51/1.36  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.36  tff(c_32, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.36  tff(c_61, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.51/1.36  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.36  tff(c_16, plain, (![A_16, B_17]: (r1_xboole_0(k1_tarski(A_16), B_17) | r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.36  tff(c_63, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, B_34) | ~r2_hidden(C_35, A_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.36  tff(c_85, plain, (![C_43, B_44, A_45]: (~r2_hidden(C_43, B_44) | ~r2_hidden(C_43, k1_tarski(A_45)) | r2_hidden(A_45, B_44))), inference(resolution, [status(thm)], [c_16, c_63])).
% 2.51/1.36  tff(c_131, plain, (![A_56, B_57, A_58]: (~r2_hidden('#skF_1'(A_56, B_57), k1_tarski(A_58)) | r2_hidden(A_58, A_56) | r1_xboole_0(A_56, B_57))), inference(resolution, [status(thm)], [c_6, c_85])).
% 2.51/1.36  tff(c_158, plain, (![A_59, A_60]: (r2_hidden(A_59, A_60) | r1_xboole_0(A_60, k1_tarski(A_59)))), inference(resolution, [status(thm)], [c_4, c_131])).
% 2.51/1.36  tff(c_20, plain, (![B_21, A_20]: (k10_relat_1(B_21, A_20)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.51/1.36  tff(c_191, plain, (![B_64, A_65]: (k10_relat_1(B_64, k1_tarski(A_65))=k1_xboole_0 | ~v1_relat_1(B_64) | r2_hidden(A_65, k2_relat_1(B_64)))), inference(resolution, [status(thm)], [c_158, c_20])).
% 2.51/1.36  tff(c_26, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.36  tff(c_62, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.51/1.36  tff(c_194, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_191, c_62])).
% 2.51/1.36  tff(c_197, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_194])).
% 2.51/1.36  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_197])).
% 2.51/1.36  tff(c_200, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 2.51/1.36  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_61])).
% 2.51/1.36  tff(c_208, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 2.51/1.36  tff(c_211, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_208, c_26])).
% 2.51/1.36  tff(c_52, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), B_27) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.36  tff(c_18, plain, (![B_19]: (~r1_xboole_0(k1_tarski(B_19), k1_tarski(B_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.51/1.36  tff(c_57, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(resolution, [status(thm)], [c_52, c_18])).
% 2.51/1.36  tff(c_230, plain, (![B_72, A_73]: (r1_xboole_0(k2_relat_1(B_72), A_73) | k10_relat_1(B_72, A_73)!=k1_xboole_0 | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.51/1.36  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.36  tff(c_364, plain, (![C_98, A_99, B_100]: (~r2_hidden(C_98, A_99) | ~r2_hidden(C_98, k2_relat_1(B_100)) | k10_relat_1(B_100, A_99)!=k1_xboole_0 | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_230, c_2])).
% 2.51/1.36  tff(c_422, plain, (![A_106, B_107]: (~r2_hidden(A_106, k2_relat_1(B_107)) | k10_relat_1(B_107, k1_tarski(A_106))!=k1_xboole_0 | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_57, c_364])).
% 2.51/1.36  tff(c_431, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_208, c_422])).
% 2.51/1.36  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_211, c_431])).
% 2.51/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  Inference rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Ref     : 0
% 2.51/1.36  #Sup     : 94
% 2.51/1.36  #Fact    : 0
% 2.51/1.36  #Define  : 0
% 2.51/1.36  #Split   : 2
% 2.51/1.36  #Chain   : 0
% 2.51/1.36  #Close   : 0
% 2.51/1.36  
% 2.51/1.36  Ordering : KBO
% 2.51/1.36  
% 2.51/1.36  Simplification rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Subsume      : 10
% 2.51/1.36  #Demod        : 16
% 2.51/1.36  #Tautology    : 31
% 2.51/1.36  #SimpNegUnit  : 1
% 2.51/1.36  #BackRed      : 0
% 2.51/1.36  
% 2.51/1.36  #Partial instantiations: 0
% 2.51/1.36  #Strategies tried      : 1
% 2.51/1.36  
% 2.51/1.36  Timing (in seconds)
% 2.51/1.36  ----------------------
% 2.51/1.37  Preprocessing        : 0.31
% 2.51/1.37  Parsing              : 0.16
% 2.51/1.37  CNF conversion       : 0.02
% 2.51/1.37  Main loop            : 0.28
% 2.51/1.37  Inferencing          : 0.11
% 2.51/1.37  Reduction            : 0.07
% 2.51/1.37  Demodulation         : 0.05
% 2.51/1.37  BG Simplification    : 0.01
% 2.51/1.37  Subsumption          : 0.06
% 2.51/1.37  Abstraction          : 0.02
% 2.51/1.37  MUC search           : 0.00
% 2.51/1.37  Cooper               : 0.00
% 2.51/1.37  Total                : 0.63
% 2.51/1.37  Index Insertion      : 0.00
% 2.51/1.37  Index Deletion       : 0.00
% 2.51/1.37  Index Matching       : 0.00
% 2.51/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
