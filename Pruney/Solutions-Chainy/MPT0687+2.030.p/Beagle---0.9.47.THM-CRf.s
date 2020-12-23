%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:37 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 163 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

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

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_33,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

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

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(k1_tarski(A_8),B_9)
      | r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | ~ r2_hidden(C_22,B_21)
      | ~ r2_hidden(C_22,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [C_27,B_28,A_29] :
      ( ~ r2_hidden(C_27,B_28)
      | ~ r2_hidden(C_27,k1_tarski(A_29))
      | r2_hidden(A_29,B_28) ) ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_189,plain,(
    ! [A_48,B_49,A_50] :
      ( ~ r2_hidden('#skF_1'(A_48,B_49),k1_tarski(A_50))
      | r2_hidden(A_50,A_48)
      | r1_xboole_0(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_219,plain,(
    ! [A_51,A_52] :
      ( r2_hidden(A_51,A_52)
      | r1_xboole_0(A_52,k1_tarski(A_51)) ) ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k10_relat_1(B_11,A_10) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_312,plain,(
    ! [B_67,A_68] :
      ( k10_relat_1(B_67,k1_tarski(A_68)) = k1_xboole_0
      | ~ v1_relat_1(B_67)
      | r2_hidden(A_68,k2_relat_1(B_67)) ) ),
    inference(resolution,[status(thm)],[c_219,c_12])).

tff(c_18,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_18])).

tff(c_326,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_312,c_38])).

tff(c_333,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_326])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_333])).

tff(c_337,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_336,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_342,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,B_70)
      | ~ r2_hidden(C_71,A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_357,plain,(
    ! [C_76,B_77,A_78] :
      ( ~ r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,k1_tarski(A_78))
      | r2_hidden(A_78,B_77) ) ),
    inference(resolution,[status(thm)],[c_10,c_342])).

tff(c_368,plain,(
    ! [A_80,B_81,A_82] :
      ( ~ r2_hidden('#skF_1'(A_80,B_81),k1_tarski(A_82))
      | r2_hidden(A_82,A_80)
      | r1_xboole_0(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_357])).

tff(c_393,plain,(
    ! [A_85,B_86] :
      ( r2_hidden(A_85,k1_tarski(A_85))
      | r1_xboole_0(k1_tarski(A_85),B_86) ) ),
    inference(resolution,[status(thm)],[c_6,c_368])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden(A_6,B_7)
      | ~ r1_xboole_0(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_414,plain,(
    ! [A_87,B_88] :
      ( ~ r2_hidden(A_87,B_88)
      | r2_hidden(A_87,k1_tarski(A_87)) ) ),
    inference(resolution,[status(thm)],[c_393,c_8])).

tff(c_424,plain,(
    r2_hidden('#skF_2',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_336,c_414])).

tff(c_348,plain,(
    ! [B_72,A_73] :
      ( r1_xboole_0(k2_relat_1(B_72),A_73)
      | k10_relat_1(B_72,A_73) != k1_xboole_0
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_454,plain,(
    ! [C_91,A_92,B_93] :
      ( ~ r2_hidden(C_91,A_92)
      | ~ r2_hidden(C_91,k2_relat_1(B_93))
      | k10_relat_1(B_93,A_92) != k1_xboole_0
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_348,c_2])).

tff(c_695,plain,(
    ! [B_115] :
      ( ~ r2_hidden('#skF_2',k2_relat_1(B_115))
      | k10_relat_1(B_115,k1_tarski('#skF_2')) != k1_xboole_0
      | ~ v1_relat_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_424,c_454])).

tff(c_702,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_336,c_695])).

tff(c_707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_337,c_702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.43  
% 2.52/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.43  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.52/1.43  
% 2.52/1.43  %Foreground sorts:
% 2.52/1.43  
% 2.52/1.43  
% 2.52/1.43  %Background operators:
% 2.52/1.43  
% 2.52/1.43  
% 2.52/1.43  %Foreground operators:
% 2.52/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.52/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.52/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.52/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.52/1.43  
% 2.80/1.44  tff(f_67, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.80/1.44  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.80/1.44  tff(f_53, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.80/1.44  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.80/1.44  tff(f_48, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.80/1.44  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.80/1.44  tff(c_24, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.80/1.44  tff(c_33, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 2.80/1.44  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.80/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.80/1.44  tff(c_10, plain, (![A_8, B_9]: (r1_xboole_0(k1_tarski(A_8), B_9) | r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.44  tff(c_34, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | ~r2_hidden(C_22, B_21) | ~r2_hidden(C_22, A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.80/1.44  tff(c_48, plain, (![C_27, B_28, A_29]: (~r2_hidden(C_27, B_28) | ~r2_hidden(C_27, k1_tarski(A_29)) | r2_hidden(A_29, B_28))), inference(resolution, [status(thm)], [c_10, c_34])).
% 2.80/1.44  tff(c_189, plain, (![A_48, B_49, A_50]: (~r2_hidden('#skF_1'(A_48, B_49), k1_tarski(A_50)) | r2_hidden(A_50, A_48) | r1_xboole_0(A_48, B_49))), inference(resolution, [status(thm)], [c_6, c_48])).
% 2.80/1.44  tff(c_219, plain, (![A_51, A_52]: (r2_hidden(A_51, A_52) | r1_xboole_0(A_52, k1_tarski(A_51)))), inference(resolution, [status(thm)], [c_4, c_189])).
% 2.80/1.44  tff(c_12, plain, (![B_11, A_10]: (k10_relat_1(B_11, A_10)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.44  tff(c_312, plain, (![B_67, A_68]: (k10_relat_1(B_67, k1_tarski(A_68))=k1_xboole_0 | ~v1_relat_1(B_67) | r2_hidden(A_68, k2_relat_1(B_67)))), inference(resolution, [status(thm)], [c_219, c_12])).
% 2.80/1.44  tff(c_18, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.80/1.44  tff(c_38, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_33, c_18])).
% 2.80/1.44  tff(c_326, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_312, c_38])).
% 2.80/1.44  tff(c_333, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_326])).
% 2.80/1.44  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_333])).
% 2.80/1.44  tff(c_337, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 2.80/1.44  tff(c_336, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_24])).
% 2.80/1.44  tff(c_342, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, B_70) | ~r2_hidden(C_71, A_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.80/1.44  tff(c_357, plain, (![C_76, B_77, A_78]: (~r2_hidden(C_76, B_77) | ~r2_hidden(C_76, k1_tarski(A_78)) | r2_hidden(A_78, B_77))), inference(resolution, [status(thm)], [c_10, c_342])).
% 2.80/1.44  tff(c_368, plain, (![A_80, B_81, A_82]: (~r2_hidden('#skF_1'(A_80, B_81), k1_tarski(A_82)) | r2_hidden(A_82, A_80) | r1_xboole_0(A_80, B_81))), inference(resolution, [status(thm)], [c_6, c_357])).
% 2.80/1.44  tff(c_393, plain, (![A_85, B_86]: (r2_hidden(A_85, k1_tarski(A_85)) | r1_xboole_0(k1_tarski(A_85), B_86))), inference(resolution, [status(thm)], [c_6, c_368])).
% 2.80/1.44  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden(A_6, B_7) | ~r1_xboole_0(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.44  tff(c_414, plain, (![A_87, B_88]: (~r2_hidden(A_87, B_88) | r2_hidden(A_87, k1_tarski(A_87)))), inference(resolution, [status(thm)], [c_393, c_8])).
% 2.80/1.44  tff(c_424, plain, (r2_hidden('#skF_2', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_336, c_414])).
% 2.80/1.44  tff(c_348, plain, (![B_72, A_73]: (r1_xboole_0(k2_relat_1(B_72), A_73) | k10_relat_1(B_72, A_73)!=k1_xboole_0 | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.44  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.80/1.44  tff(c_454, plain, (![C_91, A_92, B_93]: (~r2_hidden(C_91, A_92) | ~r2_hidden(C_91, k2_relat_1(B_93)) | k10_relat_1(B_93, A_92)!=k1_xboole_0 | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_348, c_2])).
% 2.80/1.44  tff(c_695, plain, (![B_115]: (~r2_hidden('#skF_2', k2_relat_1(B_115)) | k10_relat_1(B_115, k1_tarski('#skF_2'))!=k1_xboole_0 | ~v1_relat_1(B_115))), inference(resolution, [status(thm)], [c_424, c_454])).
% 2.80/1.44  tff(c_702, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_336, c_695])).
% 2.80/1.44  tff(c_707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_337, c_702])).
% 2.80/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  Inference rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Ref     : 0
% 2.80/1.44  #Sup     : 166
% 2.80/1.44  #Fact    : 0
% 2.80/1.44  #Define  : 0
% 2.80/1.44  #Split   : 1
% 2.80/1.44  #Chain   : 0
% 2.80/1.44  #Close   : 0
% 2.80/1.44  
% 2.80/1.44  Ordering : KBO
% 2.80/1.44  
% 2.80/1.44  Simplification rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Subsume      : 53
% 2.80/1.44  #Demod        : 16
% 2.80/1.44  #Tautology    : 32
% 2.80/1.44  #SimpNegUnit  : 2
% 2.80/1.44  #BackRed      : 0
% 2.80/1.44  
% 2.80/1.44  #Partial instantiations: 0
% 2.80/1.44  #Strategies tried      : 1
% 2.80/1.44  
% 2.80/1.44  Timing (in seconds)
% 2.80/1.44  ----------------------
% 2.80/1.45  Preprocessing        : 0.26
% 2.80/1.45  Parsing              : 0.15
% 2.80/1.45  CNF conversion       : 0.02
% 2.80/1.45  Main loop            : 0.40
% 2.80/1.45  Inferencing          : 0.17
% 2.80/1.45  Reduction            : 0.08
% 2.80/1.45  Demodulation         : 0.05
% 2.80/1.45  BG Simplification    : 0.02
% 2.80/1.45  Subsumption          : 0.09
% 2.80/1.45  Abstraction          : 0.02
% 2.80/1.45  MUC search           : 0.00
% 2.80/1.45  Cooper               : 0.00
% 2.80/1.45  Total                : 0.70
% 2.80/1.45  Index Insertion      : 0.00
% 2.80/1.45  Index Deletion       : 0.00
% 2.80/1.45  Index Matching       : 0.00
% 2.80/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
