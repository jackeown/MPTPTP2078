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
% DateTime   : Thu Dec  3 09:58:53 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   49 (  64 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  76 expanded)
%              Number of equality atoms :   16 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_3 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_32,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_79,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [C_55,A_56] :
      ( r2_hidden(k4_tarski(C_55,'#skF_6'(A_56,k1_relat_1(A_56),C_55)),A_56)
      | ~ r2_hidden(C_55,k1_relat_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_39,B_40] : ~ r2_hidden(A_39,k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_145,plain,(
    ! [C_57] : ~ r2_hidden(C_57,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_126,c_60])).

tff(c_157,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_157])).

tff(c_170,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_42] : ~ r2_hidden(A_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_74,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_relat_1(A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_74,c_16])).

tff(c_171,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_205,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_7'(A_65,B_66),k1_relat_1(B_66))
      | ~ r2_hidden(A_65,k2_relat_1(B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_211,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_7'(A_65,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_65,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_205])).

tff(c_214,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_7'(A_65,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_65,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_211])).

tff(c_216,plain,(
    ! [A_67] : ~ r2_hidden(A_67,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_214])).

tff(c_220,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:22:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_3 > #skF_7 > #skF_5 > #skF_4
% 1.87/1.17  
% 1.87/1.17  %Foreground sorts:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Background operators:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Foreground operators:
% 1.87/1.17  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.17  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.87/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.87/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.17  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.87/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.17  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.87/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.87/1.17  
% 1.87/1.18  tff(f_73, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.87/1.18  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.87/1.18  tff(f_60, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.87/1.18  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.87/1.18  tff(f_48, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.87/1.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.87/1.18  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.87/1.18  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 1.87/1.18  tff(c_32, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.87/1.18  tff(c_79, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 1.87/1.18  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.18  tff(c_126, plain, (![C_55, A_56]: (r2_hidden(k4_tarski(C_55, '#skF_6'(A_56, k1_relat_1(A_56), C_55)), A_56) | ~r2_hidden(C_55, k1_relat_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.18  tff(c_10, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.18  tff(c_57, plain, (![A_39, B_40]: (~r2_hidden(A_39, k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.87/1.18  tff(c_60, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_57])).
% 1.87/1.18  tff(c_145, plain, (![C_57]: (~r2_hidden(C_57, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_126, c_60])).
% 1.87/1.18  tff(c_157, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_145])).
% 1.87/1.18  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_157])).
% 1.87/1.18  tff(c_170, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.87/1.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.18  tff(c_69, plain, (![A_42]: (~r2_hidden(A_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_57])).
% 1.87/1.18  tff(c_74, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_69])).
% 1.87/1.18  tff(c_16, plain, (![A_11]: (v1_relat_1(A_11) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.18  tff(c_78, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_16])).
% 1.87/1.18  tff(c_171, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.87/1.18  tff(c_205, plain, (![A_65, B_66]: (r2_hidden('#skF_7'(A_65, B_66), k1_relat_1(B_66)) | ~r2_hidden(A_65, k2_relat_1(B_66)) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.87/1.18  tff(c_211, plain, (![A_65]: (r2_hidden('#skF_7'(A_65, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_65, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_205])).
% 1.87/1.18  tff(c_214, plain, (![A_65]: (r2_hidden('#skF_7'(A_65, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_65, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_211])).
% 1.87/1.18  tff(c_216, plain, (![A_67]: (~r2_hidden(A_67, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_60, c_214])).
% 1.87/1.18  tff(c_220, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_216])).
% 1.87/1.18  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_220])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 38
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 1
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 2
% 1.87/1.18  #Demod        : 2
% 1.87/1.18  #Tautology    : 18
% 1.87/1.18  #SimpNegUnit  : 3
% 1.87/1.18  #BackRed      : 0
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.97/1.18  Preprocessing        : 0.27
% 1.97/1.18  Parsing              : 0.14
% 1.97/1.18  CNF conversion       : 0.02
% 1.97/1.18  Main loop            : 0.15
% 1.97/1.18  Inferencing          : 0.06
% 1.97/1.18  Reduction            : 0.04
% 1.97/1.18  Demodulation         : 0.03
% 1.97/1.18  BG Simplification    : 0.01
% 1.97/1.18  Subsumption          : 0.03
% 1.97/1.18  Abstraction          : 0.01
% 1.97/1.18  MUC search           : 0.00
% 1.97/1.18  Cooper               : 0.00
% 1.97/1.18  Total                : 0.45
% 1.97/1.18  Index Insertion      : 0.00
% 1.97/1.18  Index Deletion       : 0.00
% 1.97/1.18  Index Matching       : 0.00
% 1.97/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
