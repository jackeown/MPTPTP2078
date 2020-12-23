%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:00 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   48 (  69 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  88 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_34,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_91,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),B_49)
      | r2_hidden('#skF_2'(A_48,B_49),A_48)
      | B_49 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [A_36,B_37] : ~ r2_hidden(A_36,k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_63])).

tff(c_99,plain,(
    ! [B_49] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_49),B_49)
      | k1_xboole_0 = B_49 ) ),
    inference(resolution,[status(thm)],[c_91,c_66])).

tff(c_126,plain,(
    ! [C_57,A_58] :
      ( r2_hidden(k4_tarski(C_57,'#skF_6'(A_58,k1_relat_1(A_58),C_57)),A_58)
      | ~ r2_hidden(C_57,k1_relat_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_126,c_66])).

tff(c_149,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_137])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_149])).

tff(c_170,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_196,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_74)
      | r2_hidden('#skF_2'(A_73,B_74),A_73)
      | B_74 = A_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_204,plain,(
    ! [B_74] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_74),B_74)
      | k1_xboole_0 = B_74 ) ),
    inference(resolution,[status(thm)],[c_196,c_66])).

tff(c_36,plain,(
    ! [B_34] : k2_zfmisc_1(k1_xboole_0,B_34) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_30])).

tff(c_171,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_216,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_7'(A_76,B_77),k1_relat_1(B_77))
      | ~ r2_hidden(A_76,k2_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_219,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_7'(A_76,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_76,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_216])).

tff(c_221,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_7'(A_76,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_76,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_219])).

tff(c_223,plain,(
    ! [A_78] : ~ r2_hidden(A_78,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_221])).

tff(c_227,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_223])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.20  
% 1.86/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.20  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 1.86/1.20  
% 1.86/1.20  %Foreground sorts:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Background operators:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Foreground operators:
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.20  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.86/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.86/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.86/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.20  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.86/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.86/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.86/1.20  
% 1.86/1.21  tff(f_64, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.86/1.21  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.86/1.21  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.86/1.21  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.86/1.21  tff(f_49, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.86/1.21  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.86/1.21  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 1.86/1.21  tff(c_34, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.86/1.21  tff(c_70, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 1.86/1.21  tff(c_91, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), B_49) | r2_hidden('#skF_2'(A_48, B_49), A_48) | B_49=A_48)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.21  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.86/1.21  tff(c_63, plain, (![A_36, B_37]: (~r2_hidden(A_36, k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.21  tff(c_66, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_63])).
% 1.86/1.21  tff(c_99, plain, (![B_49]: (r2_hidden('#skF_1'(k1_xboole_0, B_49), B_49) | k1_xboole_0=B_49)), inference(resolution, [status(thm)], [c_91, c_66])).
% 1.86/1.21  tff(c_126, plain, (![C_57, A_58]: (r2_hidden(k4_tarski(C_57, '#skF_6'(A_58, k1_relat_1(A_58), C_57)), A_58) | ~r2_hidden(C_57, k1_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.86/1.21  tff(c_137, plain, (![C_62]: (~r2_hidden(C_62, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_126, c_66])).
% 1.86/1.21  tff(c_149, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_137])).
% 1.86/1.21  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_149])).
% 1.86/1.21  tff(c_170, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 1.86/1.21  tff(c_196, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), B_74) | r2_hidden('#skF_2'(A_73, B_74), A_73) | B_74=A_73)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.21  tff(c_204, plain, (![B_74]: (r2_hidden('#skF_1'(k1_xboole_0, B_74), B_74) | k1_xboole_0=B_74)), inference(resolution, [status(thm)], [c_196, c_66])).
% 1.86/1.21  tff(c_36, plain, (![B_34]: (k2_zfmisc_1(k1_xboole_0, B_34)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.86/1.21  tff(c_30, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.86/1.21  tff(c_40, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_30])).
% 1.86/1.21  tff(c_171, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 1.86/1.21  tff(c_216, plain, (![A_76, B_77]: (r2_hidden('#skF_7'(A_76, B_77), k1_relat_1(B_77)) | ~r2_hidden(A_76, k2_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.86/1.21  tff(c_219, plain, (![A_76]: (r2_hidden('#skF_7'(A_76, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_76, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_216])).
% 1.86/1.21  tff(c_221, plain, (![A_76]: (r2_hidden('#skF_7'(A_76, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_76, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_219])).
% 1.86/1.21  tff(c_223, plain, (![A_78]: (~r2_hidden(A_78, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_66, c_221])).
% 1.86/1.21  tff(c_227, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_204, c_223])).
% 1.86/1.21  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_227])).
% 1.86/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.21  
% 1.86/1.21  Inference rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Ref     : 0
% 1.86/1.21  #Sup     : 39
% 1.86/1.21  #Fact    : 0
% 1.86/1.21  #Define  : 0
% 1.86/1.21  #Split   : 1
% 1.86/1.21  #Chain   : 0
% 1.86/1.21  #Close   : 0
% 1.86/1.21  
% 1.86/1.21  Ordering : KBO
% 1.86/1.21  
% 1.86/1.21  Simplification rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Subsume      : 6
% 1.86/1.21  #Demod        : 3
% 1.86/1.21  #Tautology    : 18
% 1.86/1.21  #SimpNegUnit  : 3
% 1.86/1.21  #BackRed      : 0
% 1.86/1.21  
% 1.86/1.21  #Partial instantiations: 0
% 1.86/1.21  #Strategies tried      : 1
% 1.86/1.21  
% 1.86/1.21  Timing (in seconds)
% 1.86/1.21  ----------------------
% 1.86/1.21  Preprocessing        : 0.28
% 1.86/1.21  Parsing              : 0.15
% 1.86/1.21  CNF conversion       : 0.02
% 1.86/1.21  Main loop            : 0.18
% 1.86/1.21  Inferencing          : 0.08
% 1.86/1.21  Reduction            : 0.04
% 1.86/1.21  Demodulation         : 0.03
% 1.86/1.21  BG Simplification    : 0.01
% 1.86/1.22  Subsumption          : 0.03
% 1.86/1.22  Abstraction          : 0.01
% 1.86/1.22  MUC search           : 0.00
% 1.86/1.22  Cooper               : 0.00
% 1.86/1.22  Total                : 0.48
% 1.86/1.22  Index Insertion      : 0.00
% 1.86/1.22  Index Deletion       : 0.00
% 1.86/1.22  Index Matching       : 0.00
% 1.86/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
