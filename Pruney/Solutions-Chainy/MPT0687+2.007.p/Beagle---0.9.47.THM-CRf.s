%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:34 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   46 (  62 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 116 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,
    ( r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_54,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_1'(A_22,B_23),B_23)
      | r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_59,plain,(
    ! [A_22,A_6] :
      ( '#skF_1'(A_22,k1_tarski(A_6)) = A_6
      | r1_xboole_0(A_22,k1_tarski(A_6)) ) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_102,plain,(
    ! [B_35,A_36] :
      ( k10_relat_1(B_35,A_36) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_298,plain,(
    ! [B_64,A_65] :
      ( k10_relat_1(B_64,k1_tarski(A_65)) = k1_xboole_0
      | ~ v1_relat_1(B_64)
      | '#skF_1'(k2_relat_1(B_64),k1_tarski(A_65)) = A_65 ) ),
    inference(resolution,[status(thm)],[c_59,c_102])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2032,plain,(
    ! [A_153,B_154] :
      ( r2_hidden(A_153,k2_relat_1(B_154))
      | r1_xboole_0(k2_relat_1(B_154),k1_tarski(A_153))
      | k10_relat_1(B_154,k1_tarski(A_153)) = k1_xboole_0
      | ~ v1_relat_1(B_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_6])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(B_15,A_14) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2040,plain,(
    ! [A_155,B_156] :
      ( r2_hidden(A_155,k2_relat_1(B_156))
      | k10_relat_1(B_156,k1_tarski(A_155)) = k1_xboole_0
      | ~ v1_relat_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_2032,c_24])).

tff(c_30,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_30])).

tff(c_2083,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2040,c_67])).

tff(c_2097,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2083])).

tff(c_2099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2097])).

tff(c_2101,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2100,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2148,plain,(
    ! [B_168,A_169] :
      ( r1_xboole_0(k2_relat_1(B_168),A_169)
      | k10_relat_1(B_168,A_169) != k1_xboole_0
      | ~ v1_relat_1(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2336,plain,(
    ! [C_192,A_193,B_194] :
      ( ~ r2_hidden(C_192,A_193)
      | ~ r2_hidden(C_192,k2_relat_1(B_194))
      | k10_relat_1(B_194,A_193) != k1_xboole_0
      | ~ v1_relat_1(B_194) ) ),
    inference(resolution,[status(thm)],[c_2148,c_2])).

tff(c_2385,plain,(
    ! [C_198,B_199] :
      ( ~ r2_hidden(C_198,k2_relat_1(B_199))
      | k10_relat_1(B_199,k1_tarski(C_198)) != k1_xboole_0
      | ~ v1_relat_1(B_199) ) ),
    inference(resolution,[status(thm)],[c_10,c_2336])).

tff(c_2396,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2100,c_2385])).

tff(c_2410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2101,c_2396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:01:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.63  
% 3.89/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.63  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.89/1.63  
% 3.89/1.63  %Foreground sorts:
% 3.89/1.63  
% 3.89/1.63  
% 3.89/1.63  %Background operators:
% 3.89/1.63  
% 3.89/1.63  
% 3.89/1.63  %Foreground operators:
% 3.89/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.89/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.89/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.89/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.89/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.89/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.89/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.89/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.89/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.89/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.89/1.63  
% 3.89/1.64  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 3.89/1.64  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.89/1.64  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.89/1.64  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 3.89/1.64  tff(c_28, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.89/1.64  tff(c_36, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5')) | k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.89/1.64  tff(c_66, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.89/1.64  tff(c_54, plain, (![A_22, B_23]: (r2_hidden('#skF_1'(A_22, B_23), B_23) | r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.64  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.89/1.64  tff(c_59, plain, (![A_22, A_6]: ('#skF_1'(A_22, k1_tarski(A_6))=A_6 | r1_xboole_0(A_22, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_54, c_8])).
% 3.89/1.64  tff(c_102, plain, (![B_35, A_36]: (k10_relat_1(B_35, A_36)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.64  tff(c_298, plain, (![B_64, A_65]: (k10_relat_1(B_64, k1_tarski(A_65))=k1_xboole_0 | ~v1_relat_1(B_64) | '#skF_1'(k2_relat_1(B_64), k1_tarski(A_65))=A_65)), inference(resolution, [status(thm)], [c_59, c_102])).
% 3.89/1.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.64  tff(c_2032, plain, (![A_153, B_154]: (r2_hidden(A_153, k2_relat_1(B_154)) | r1_xboole_0(k2_relat_1(B_154), k1_tarski(A_153)) | k10_relat_1(B_154, k1_tarski(A_153))=k1_xboole_0 | ~v1_relat_1(B_154))), inference(superposition, [status(thm), theory('equality')], [c_298, c_6])).
% 3.89/1.64  tff(c_24, plain, (![B_15, A_14]: (k10_relat_1(B_15, A_14)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.64  tff(c_2040, plain, (![A_155, B_156]: (r2_hidden(A_155, k2_relat_1(B_156)) | k10_relat_1(B_156, k1_tarski(A_155))=k1_xboole_0 | ~v1_relat_1(B_156))), inference(resolution, [status(thm)], [c_2032, c_24])).
% 3.89/1.64  tff(c_30, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.89/1.64  tff(c_67, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_30])).
% 3.89/1.64  tff(c_2083, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2040, c_67])).
% 3.89/1.64  tff(c_2097, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2083])).
% 3.89/1.64  tff(c_2099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2097])).
% 3.89/1.64  tff(c_2101, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.89/1.64  tff(c_2100, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_36])).
% 3.89/1.64  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.89/1.64  tff(c_2148, plain, (![B_168, A_169]: (r1_xboole_0(k2_relat_1(B_168), A_169) | k10_relat_1(B_168, A_169)!=k1_xboole_0 | ~v1_relat_1(B_168))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.64  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.64  tff(c_2336, plain, (![C_192, A_193, B_194]: (~r2_hidden(C_192, A_193) | ~r2_hidden(C_192, k2_relat_1(B_194)) | k10_relat_1(B_194, A_193)!=k1_xboole_0 | ~v1_relat_1(B_194))), inference(resolution, [status(thm)], [c_2148, c_2])).
% 3.89/1.64  tff(c_2385, plain, (![C_198, B_199]: (~r2_hidden(C_198, k2_relat_1(B_199)) | k10_relat_1(B_199, k1_tarski(C_198))!=k1_xboole_0 | ~v1_relat_1(B_199))), inference(resolution, [status(thm)], [c_10, c_2336])).
% 3.89/1.64  tff(c_2396, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2100, c_2385])).
% 3.89/1.64  tff(c_2410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2101, c_2396])).
% 3.89/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.64  
% 3.89/1.64  Inference rules
% 3.89/1.64  ----------------------
% 3.89/1.64  #Ref     : 0
% 3.89/1.64  #Sup     : 583
% 3.89/1.64  #Fact    : 0
% 3.89/1.64  #Define  : 0
% 3.89/1.64  #Split   : 1
% 3.89/1.64  #Chain   : 0
% 3.89/1.64  #Close   : 0
% 3.89/1.64  
% 3.89/1.64  Ordering : KBO
% 3.89/1.64  
% 3.89/1.64  Simplification rules
% 3.89/1.64  ----------------------
% 3.89/1.64  #Subsume      : 189
% 3.89/1.64  #Demod        : 126
% 3.89/1.64  #Tautology    : 224
% 3.89/1.64  #SimpNegUnit  : 2
% 3.89/1.64  #BackRed      : 0
% 3.89/1.64  
% 3.89/1.64  #Partial instantiations: 0
% 3.89/1.64  #Strategies tried      : 1
% 3.89/1.64  
% 3.89/1.64  Timing (in seconds)
% 3.89/1.64  ----------------------
% 3.89/1.64  Preprocessing        : 0.28
% 3.89/1.64  Parsing              : 0.14
% 3.89/1.64  CNF conversion       : 0.02
% 3.89/1.64  Main loop            : 0.61
% 3.89/1.64  Inferencing          : 0.23
% 3.89/1.64  Reduction            : 0.15
% 3.89/1.64  Demodulation         : 0.09
% 3.89/1.64  BG Simplification    : 0.03
% 3.89/1.64  Subsumption          : 0.16
% 3.89/1.64  Abstraction          : 0.04
% 3.89/1.64  MUC search           : 0.00
% 3.89/1.64  Cooper               : 0.00
% 3.89/1.64  Total                : 0.92
% 3.89/1.64  Index Insertion      : 0.00
% 3.89/1.64  Index Deletion       : 0.00
% 3.89/1.64  Index Matching       : 0.00
% 3.89/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
