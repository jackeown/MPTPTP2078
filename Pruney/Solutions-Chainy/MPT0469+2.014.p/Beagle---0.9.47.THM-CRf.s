%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:53 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  69 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_46,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_32,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [C_49,A_50] :
      ( r2_hidden(k4_tarski(C_49,'#skF_5'(A_50,k1_relat_1(A_50),C_49)),A_50)
      | ~ r2_hidden(C_49,k1_relat_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [A_36,B_37] : ~ r2_hidden(A_36,k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_108,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_98,c_71])).

tff(c_120,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_108])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_120])).

tff(c_129,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_12,plain,(
    ! [A_7] : k1_subset_1(A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_8] : v1_xboole_0(k1_subset_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_41,plain,(
    ! [A_33] :
      ( v1_relat_1(A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_33,c_41])).

tff(c_130,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_154,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_6'(A_58,B_59),k1_relat_1(B_59))
      | ~ r2_hidden(A_58,k2_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_157,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_6'(A_58,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_58,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_154])).

tff(c_159,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_6'(A_58,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_58,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_157])).

tff(c_161,plain,(
    ! [A_60] : ~ r2_hidden(A_60,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_159])).

tff(c_165,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_161])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:52:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.18  
% 1.67/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.18  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.67/1.18  
% 1.67/1.18  %Foreground sorts:
% 1.67/1.18  
% 1.67/1.18  
% 1.67/1.18  %Background operators:
% 1.67/1.18  
% 1.67/1.18  
% 1.67/1.18  %Foreground operators:
% 1.67/1.18  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.67/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.67/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.67/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.67/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.67/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.67/1.18  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.67/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.67/1.18  
% 1.88/1.19  tff(f_71, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.19  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.88/1.19  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.88/1.19  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.88/1.19  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.88/1.19  tff(f_44, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.88/1.19  tff(f_46, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.88/1.19  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.88/1.19  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 1.88/1.19  tff(c_32, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.88/1.19  tff(c_76, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 1.88/1.19  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.19  tff(c_98, plain, (![C_49, A_50]: (r2_hidden(k4_tarski(C_49, '#skF_5'(A_50, k1_relat_1(A_50), C_49)), A_50) | ~r2_hidden(C_49, k1_relat_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.19  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.19  tff(c_68, plain, (![A_36, B_37]: (~r2_hidden(A_36, k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.19  tff(c_71, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 1.88/1.19  tff(c_108, plain, (![C_51]: (~r2_hidden(C_51, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_98, c_71])).
% 1.88/1.19  tff(c_120, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_108])).
% 1.88/1.19  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_120])).
% 1.88/1.19  tff(c_129, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.88/1.19  tff(c_12, plain, (![A_7]: (k1_subset_1(A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.88/1.19  tff(c_14, plain, (![A_8]: (v1_xboole_0(k1_subset_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.19  tff(c_33, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 1.88/1.19  tff(c_41, plain, (![A_33]: (v1_relat_1(A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.19  tff(c_45, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_41])).
% 1.88/1.19  tff(c_130, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.88/1.19  tff(c_154, plain, (![A_58, B_59]: (r2_hidden('#skF_6'(A_58, B_59), k1_relat_1(B_59)) | ~r2_hidden(A_58, k2_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.88/1.19  tff(c_157, plain, (![A_58]: (r2_hidden('#skF_6'(A_58, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_58, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_154])).
% 1.88/1.19  tff(c_159, plain, (![A_58]: (r2_hidden('#skF_6'(A_58, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_58, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_157])).
% 1.88/1.19  tff(c_161, plain, (![A_60]: (~r2_hidden(A_60, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_71, c_159])).
% 1.88/1.19  tff(c_165, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_161])).
% 1.88/1.19  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_165])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 26
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 1
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 1
% 1.88/1.19  #Demod        : 3
% 1.88/1.19  #Tautology    : 17
% 1.88/1.19  #SimpNegUnit  : 3
% 1.88/1.19  #BackRed      : 0
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.19  Preprocessing        : 0.28
% 1.88/1.19  Parsing              : 0.15
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.14
% 1.88/1.19  Inferencing          : 0.06
% 1.88/1.19  Reduction            : 0.04
% 1.88/1.19  Demodulation         : 0.03
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.02
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.45
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
