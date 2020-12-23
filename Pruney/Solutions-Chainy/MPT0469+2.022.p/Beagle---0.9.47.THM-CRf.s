%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:54 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  66 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_30,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [C_44,A_45] :
      ( r2_hidden(k4_tarski(C_44,'#skF_5'(A_45,k1_relat_1(A_45),C_44)),A_45)
      | ~ r2_hidden(C_44,k1_relat_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,(
    ! [A_33,B_34] : ~ r2_hidden(A_33,k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_98,plain,(
    ! [C_48] : ~ r2_hidden(C_48,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_87,c_61])).

tff(c_110,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_110])).

tff(c_119,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ! [A_31] :
      ( v1_relat_1(A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_120,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_144,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_6'(A_55,B_56),k1_relat_1(B_56))
      | ~ r2_hidden(A_55,k2_relat_1(B_56))
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_147,plain,(
    ! [A_55] :
      ( r2_hidden('#skF_6'(A_55,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_55,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_144])).

tff(c_149,plain,(
    ! [A_55] :
      ( r2_hidden('#skF_6'(A_55,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_55,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_147])).

tff(c_151,plain,(
    ! [A_57] : ~ r2_hidden(A_57,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_149])).

tff(c_155,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_151])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:17:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.66/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.15  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.15  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.66/1.15  
% 1.66/1.16  tff(f_68, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.66/1.16  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.66/1.16  tff(f_55, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.66/1.16  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.66/1.16  tff(f_43, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.66/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.66/1.16  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.66/1.16  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 1.66/1.16  tff(c_30, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.66/1.16  tff(c_66, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 1.66/1.16  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.66/1.16  tff(c_87, plain, (![C_44, A_45]: (r2_hidden(k4_tarski(C_44, '#skF_5'(A_45, k1_relat_1(A_45), C_44)), A_45) | ~r2_hidden(C_44, k1_relat_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.66/1.16  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.66/1.16  tff(c_58, plain, (![A_33, B_34]: (~r2_hidden(A_33, k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.16  tff(c_61, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_58])).
% 1.66/1.16  tff(c_98, plain, (![C_48]: (~r2_hidden(C_48, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_87, c_61])).
% 1.66/1.16  tff(c_110, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_98])).
% 1.66/1.16  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_110])).
% 1.66/1.16  tff(c_119, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 1.66/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.66/1.16  tff(c_38, plain, (![A_31]: (v1_relat_1(A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.16  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 1.66/1.16  tff(c_120, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 1.66/1.16  tff(c_144, plain, (![A_55, B_56]: (r2_hidden('#skF_6'(A_55, B_56), k1_relat_1(B_56)) | ~r2_hidden(A_55, k2_relat_1(B_56)) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.66/1.16  tff(c_147, plain, (![A_55]: (r2_hidden('#skF_6'(A_55, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_55, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_120, c_144])).
% 1.66/1.16  tff(c_149, plain, (![A_55]: (r2_hidden('#skF_6'(A_55, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_55, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_147])).
% 1.66/1.16  tff(c_151, plain, (![A_57]: (~r2_hidden(A_57, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_61, c_149])).
% 1.66/1.16  tff(c_155, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_151])).
% 1.66/1.16  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_155])).
% 1.66/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  Inference rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Ref     : 0
% 1.66/1.16  #Sup     : 24
% 1.66/1.16  #Fact    : 0
% 1.66/1.16  #Define  : 0
% 1.66/1.16  #Split   : 1
% 1.66/1.16  #Chain   : 0
% 1.66/1.16  #Close   : 0
% 1.66/1.16  
% 1.66/1.16  Ordering : KBO
% 1.66/1.16  
% 1.66/1.16  Simplification rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Subsume      : 1
% 1.66/1.16  #Demod        : 2
% 1.66/1.16  #Tautology    : 15
% 1.66/1.16  #SimpNegUnit  : 3
% 1.66/1.16  #BackRed      : 0
% 1.66/1.16  
% 1.66/1.16  #Partial instantiations: 0
% 1.66/1.16  #Strategies tried      : 1
% 1.66/1.16  
% 1.66/1.16  Timing (in seconds)
% 1.66/1.16  ----------------------
% 1.66/1.17  Preprocessing        : 0.27
% 1.66/1.17  Parsing              : 0.15
% 1.66/1.17  CNF conversion       : 0.02
% 1.66/1.17  Main loop            : 0.13
% 1.66/1.17  Inferencing          : 0.05
% 1.66/1.17  Reduction            : 0.03
% 1.66/1.17  Demodulation         : 0.02
% 1.66/1.17  BG Simplification    : 0.01
% 1.66/1.17  Subsumption          : 0.02
% 1.66/1.17  Abstraction          : 0.00
% 1.66/1.17  MUC search           : 0.00
% 1.66/1.17  Cooper               : 0.00
% 1.66/1.17  Total                : 0.43
% 1.66/1.17  Index Insertion      : 0.00
% 1.66/1.17  Index Deletion       : 0.00
% 1.66/1.17  Index Matching       : 0.00
% 1.66/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
