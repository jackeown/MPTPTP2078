%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:19 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 134 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [C_27,A_12] :
      ( r2_hidden(k4_tarski(C_27,'#skF_7'(A_12,k1_relat_1(A_12),C_27)),A_12)
      | ~ r2_hidden(C_27,k1_relat_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_605,plain,(
    ! [C_114,A_115] :
      ( r2_hidden(k4_tarski(C_114,'#skF_7'(A_115,k1_relat_1(A_115),C_114)),A_115)
      | ~ r2_hidden(C_114,k1_relat_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_289,plain,(
    ! [D_74,B_75,A_76] :
      ( ~ r2_hidden(D_74,B_75)
      | ~ r2_hidden(D_74,k4_xboole_0(A_76,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_296,plain,(
    ! [D_74,A_11] :
      ( ~ r2_hidden(D_74,A_11)
      | ~ r2_hidden(D_74,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_289])).

tff(c_772,plain,(
    ! [C_130,A_131] :
      ( ~ r2_hidden(k4_tarski(C_130,'#skF_7'(A_131,k1_relat_1(A_131),C_130)),k1_xboole_0)
      | ~ r2_hidden(C_130,k1_relat_1(A_131)) ) ),
    inference(resolution,[status(thm)],[c_605,c_296])).

tff(c_803,plain,(
    ! [C_135] : ~ r2_hidden(C_135,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_26,c_772])).

tff(c_843,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_803])).

tff(c_784,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_26,c_772])).

tff(c_844,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_784])).

tff(c_44,plain,
    ( k11_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_59,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_9'))
    | k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_50])).

tff(c_42,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_202,plain,(
    ! [A_60,B_61,C_62] :
      ( r2_hidden(k4_tarski(A_60,B_61),C_62)
      | ~ r2_hidden(B_61,k11_relat_1(C_62,A_60))
      | ~ v1_relat_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k1_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(C_27,D_30),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_234,plain,(
    ! [A_66,C_67,B_68] :
      ( r2_hidden(A_66,k1_relat_1(C_67))
      | ~ r2_hidden(B_68,k11_relat_1(C_67,A_66))
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_202,c_28])).

tff(c_247,plain,(
    ! [A_69,C_70] :
      ( r2_hidden(A_69,k1_relat_1(C_70))
      | ~ v1_relat_1(C_70)
      | k11_relat_1(C_70,A_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_234])).

tff(c_264,plain,
    ( ~ v1_relat_1('#skF_9')
    | k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_247,c_59])).

tff(c_271,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_264])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_271])).

tff(c_275,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_274,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,(
    ! [B_32,C_33,A_31] :
      ( r2_hidden(B_32,k11_relat_1(C_33,A_31))
      | ~ r2_hidden(k4_tarski(A_31,B_32),C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2673,plain,(
    ! [A_219,C_220] :
      ( r2_hidden('#skF_7'(A_219,k1_relat_1(A_219),C_220),k11_relat_1(A_219,C_220))
      | ~ v1_relat_1(A_219)
      | ~ r2_hidden(C_220,k1_relat_1(A_219)) ) ),
    inference(resolution,[status(thm)],[c_605,c_40])).

tff(c_2693,plain,
    ( r2_hidden('#skF_7'('#skF_9',k1_relat_1('#skF_9'),'#skF_8'),k1_xboole_0)
    | ~ v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_2673])).

tff(c_2698,plain,(
    r2_hidden('#skF_7'('#skF_9',k1_relat_1('#skF_9'),'#skF_8'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_42,c_2693])).

tff(c_2700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_2698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:30:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.64  
% 3.93/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.65  %$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.93/1.65  
% 3.93/1.65  %Foreground sorts:
% 3.93/1.65  
% 3.93/1.65  
% 3.93/1.65  %Background operators:
% 3.93/1.65  
% 3.93/1.65  
% 3.93/1.65  %Foreground operators:
% 3.93/1.65  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.93/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.93/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.93/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.93/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.93/1.65  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.93/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.93/1.65  tff('#skF_9', type, '#skF_9': $i).
% 3.93/1.65  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.93/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.93/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.93/1.65  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.93/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.93/1.65  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.93/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.93/1.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.93/1.65  
% 3.93/1.66  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.93/1.66  tff(f_55, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.93/1.66  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.93/1.66  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.93/1.66  tff(f_69, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.93/1.66  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.93/1.66  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.93/1.66  tff(c_26, plain, (![C_27, A_12]: (r2_hidden(k4_tarski(C_27, '#skF_7'(A_12, k1_relat_1(A_12), C_27)), A_12) | ~r2_hidden(C_27, k1_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.93/1.66  tff(c_605, plain, (![C_114, A_115]: (r2_hidden(k4_tarski(C_114, '#skF_7'(A_115, k1_relat_1(A_115), C_114)), A_115) | ~r2_hidden(C_114, k1_relat_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.93/1.66  tff(c_24, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.93/1.66  tff(c_289, plain, (![D_74, B_75, A_76]: (~r2_hidden(D_74, B_75) | ~r2_hidden(D_74, k4_xboole_0(A_76, B_75)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.93/1.66  tff(c_296, plain, (![D_74, A_11]: (~r2_hidden(D_74, A_11) | ~r2_hidden(D_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_289])).
% 3.93/1.66  tff(c_772, plain, (![C_130, A_131]: (~r2_hidden(k4_tarski(C_130, '#skF_7'(A_131, k1_relat_1(A_131), C_130)), k1_xboole_0) | ~r2_hidden(C_130, k1_relat_1(A_131)))), inference(resolution, [status(thm)], [c_605, c_296])).
% 3.93/1.66  tff(c_803, plain, (![C_135]: (~r2_hidden(C_135, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_26, c_772])).
% 3.93/1.66  tff(c_843, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_803])).
% 3.93/1.66  tff(c_784, plain, (![C_27]: (~r2_hidden(C_27, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_26, c_772])).
% 3.93/1.66  tff(c_844, plain, (![C_27]: (~r2_hidden(C_27, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_784])).
% 3.93/1.66  tff(c_44, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | ~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.93/1.66  tff(c_59, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.93/1.66  tff(c_50, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9')) | k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.93/1.66  tff(c_78, plain, (k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_59, c_50])).
% 3.93/1.66  tff(c_42, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.93/1.66  tff(c_202, plain, (![A_60, B_61, C_62]: (r2_hidden(k4_tarski(A_60, B_61), C_62) | ~r2_hidden(B_61, k11_relat_1(C_62, A_60)) | ~v1_relat_1(C_62))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.93/1.66  tff(c_28, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k1_relat_1(A_12)) | ~r2_hidden(k4_tarski(C_27, D_30), A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.93/1.66  tff(c_234, plain, (![A_66, C_67, B_68]: (r2_hidden(A_66, k1_relat_1(C_67)) | ~r2_hidden(B_68, k11_relat_1(C_67, A_66)) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_202, c_28])).
% 3.93/1.66  tff(c_247, plain, (![A_69, C_70]: (r2_hidden(A_69, k1_relat_1(C_70)) | ~v1_relat_1(C_70) | k11_relat_1(C_70, A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_234])).
% 3.93/1.66  tff(c_264, plain, (~v1_relat_1('#skF_9') | k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_247, c_59])).
% 3.93/1.66  tff(c_271, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_264])).
% 3.93/1.66  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_271])).
% 3.93/1.66  tff(c_275, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_44])).
% 3.93/1.66  tff(c_274, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.93/1.66  tff(c_40, plain, (![B_32, C_33, A_31]: (r2_hidden(B_32, k11_relat_1(C_33, A_31)) | ~r2_hidden(k4_tarski(A_31, B_32), C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.93/1.66  tff(c_2673, plain, (![A_219, C_220]: (r2_hidden('#skF_7'(A_219, k1_relat_1(A_219), C_220), k11_relat_1(A_219, C_220)) | ~v1_relat_1(A_219) | ~r2_hidden(C_220, k1_relat_1(A_219)))), inference(resolution, [status(thm)], [c_605, c_40])).
% 3.93/1.66  tff(c_2693, plain, (r2_hidden('#skF_7'('#skF_9', k1_relat_1('#skF_9'), '#skF_8'), k1_xboole_0) | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_2673])).
% 3.93/1.66  tff(c_2698, plain, (r2_hidden('#skF_7'('#skF_9', k1_relat_1('#skF_9'), '#skF_8'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_275, c_42, c_2693])).
% 3.93/1.66  tff(c_2700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_844, c_2698])).
% 3.93/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.66  
% 3.93/1.66  Inference rules
% 3.93/1.66  ----------------------
% 3.93/1.66  #Ref     : 0
% 3.93/1.66  #Sup     : 596
% 3.93/1.66  #Fact    : 0
% 3.93/1.66  #Define  : 0
% 3.93/1.66  #Split   : 2
% 3.93/1.66  #Chain   : 0
% 3.93/1.66  #Close   : 0
% 3.93/1.66  
% 3.93/1.66  Ordering : KBO
% 3.93/1.66  
% 3.93/1.66  Simplification rules
% 3.93/1.66  ----------------------
% 3.93/1.66  #Subsume      : 155
% 3.93/1.66  #Demod        : 191
% 3.93/1.66  #Tautology    : 157
% 3.93/1.66  #SimpNegUnit  : 43
% 3.93/1.66  #BackRed      : 1
% 3.93/1.66  
% 3.93/1.66  #Partial instantiations: 0
% 3.93/1.66  #Strategies tried      : 1
% 3.93/1.66  
% 3.93/1.66  Timing (in seconds)
% 3.93/1.66  ----------------------
% 3.93/1.66  Preprocessing        : 0.26
% 3.93/1.66  Parsing              : 0.14
% 3.93/1.66  CNF conversion       : 0.02
% 3.93/1.66  Main loop            : 0.64
% 3.93/1.66  Inferencing          : 0.23
% 3.93/1.66  Reduction            : 0.17
% 3.93/1.66  Demodulation         : 0.11
% 3.93/1.66  BG Simplification    : 0.03
% 3.93/1.66  Subsumption          : 0.16
% 3.93/1.66  Abstraction          : 0.04
% 3.93/1.66  MUC search           : 0.00
% 3.93/1.66  Cooper               : 0.00
% 3.93/1.66  Total                : 0.93
% 3.93/1.66  Index Insertion      : 0.00
% 3.93/1.66  Index Deletion       : 0.00
% 3.93/1.66  Index Matching       : 0.00
% 3.93/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
