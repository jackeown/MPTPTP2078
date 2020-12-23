%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:21 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  89 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [C_39,B_40] : ~ r2_hidden(C_39,k4_xboole_0(B_40,k1_tarski(C_39))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_44,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_111,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_171,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(k4_tarski(A_59,B_60),C_61)
      | ~ r2_hidden(B_60,k11_relat_1(C_61,A_59))
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [C_29,A_14,D_32] :
      ( r2_hidden(C_29,k1_relat_1(A_14))
      | ~ r2_hidden(k4_tarski(C_29,D_32),A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_202,plain,(
    ! [A_65,C_66,B_67] :
      ( r2_hidden(A_65,k1_relat_1(C_66))
      | ~ r2_hidden(B_67,k11_relat_1(C_66,A_65))
      | ~ v1_relat_1(C_66) ) ),
    inference(resolution,[status(thm)],[c_171,c_22])).

tff(c_211,plain,(
    ! [A_68,C_69] :
      ( r2_hidden(A_68,k1_relat_1(C_69))
      | ~ v1_relat_1(C_69)
      | k11_relat_1(C_69,A_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_202])).

tff(c_38,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_38])).

tff(c_222,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_211,c_112])).

tff(c_227,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_222])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_227])).

tff(c_230,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_231,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_327,plain,(
    ! [C_88,A_89] :
      ( r2_hidden(k4_tarski(C_88,'#skF_5'(A_89,k1_relat_1(A_89),C_88)),A_89)
      | ~ r2_hidden(C_88,k1_relat_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [B_34,C_35,A_33] :
      ( r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1114,plain,(
    ! [A_140,C_141] :
      ( r2_hidden('#skF_5'(A_140,k1_relat_1(A_140),C_141),k11_relat_1(A_140,C_141))
      | ~ v1_relat_1(A_140)
      | ~ r2_hidden(C_141,k1_relat_1(A_140)) ) ),
    inference(resolution,[status(thm)],[c_327,c_34])).

tff(c_1134,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_1114])).

tff(c_1139,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_36,c_1134])).

tff(c_1141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.47  
% 2.77/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.47  %$ r2_hidden > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 2.77/1.47  
% 2.77/1.47  %Foreground sorts:
% 2.77/1.47  
% 2.77/1.47  
% 2.77/1.47  %Background operators:
% 2.77/1.47  
% 2.77/1.47  
% 2.77/1.47  %Foreground operators:
% 2.77/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.47  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.77/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.47  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.77/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.77/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.77/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.77/1.47  
% 2.77/1.48  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.77/1.48  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.77/1.48  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.77/1.48  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.77/1.48  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.77/1.48  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.77/1.48  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.48  tff(c_62, plain, (![C_39, B_40]: (~r2_hidden(C_39, k4_xboole_0(B_40, k1_tarski(C_39))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.77/1.48  tff(c_65, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_62])).
% 2.77/1.48  tff(c_44, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.77/1.48  tff(c_111, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 2.77/1.48  tff(c_36, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.77/1.48  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.48  tff(c_171, plain, (![A_59, B_60, C_61]: (r2_hidden(k4_tarski(A_59, B_60), C_61) | ~r2_hidden(B_60, k11_relat_1(C_61, A_59)) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.77/1.48  tff(c_22, plain, (![C_29, A_14, D_32]: (r2_hidden(C_29, k1_relat_1(A_14)) | ~r2_hidden(k4_tarski(C_29, D_32), A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.77/1.48  tff(c_202, plain, (![A_65, C_66, B_67]: (r2_hidden(A_65, k1_relat_1(C_66)) | ~r2_hidden(B_67, k11_relat_1(C_66, A_65)) | ~v1_relat_1(C_66))), inference(resolution, [status(thm)], [c_171, c_22])).
% 2.77/1.48  tff(c_211, plain, (![A_68, C_69]: (r2_hidden(A_68, k1_relat_1(C_69)) | ~v1_relat_1(C_69) | k11_relat_1(C_69, A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_202])).
% 2.77/1.48  tff(c_38, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.77/1.48  tff(c_112, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_111, c_38])).
% 2.77/1.48  tff(c_222, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_211, c_112])).
% 2.77/1.48  tff(c_227, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_222])).
% 2.77/1.48  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_227])).
% 2.77/1.48  tff(c_230, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_44])).
% 2.77/1.48  tff(c_231, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 2.77/1.48  tff(c_327, plain, (![C_88, A_89]: (r2_hidden(k4_tarski(C_88, '#skF_5'(A_89, k1_relat_1(A_89), C_88)), A_89) | ~r2_hidden(C_88, k1_relat_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.77/1.48  tff(c_34, plain, (![B_34, C_35, A_33]: (r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~r2_hidden(k4_tarski(A_33, B_34), C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.77/1.48  tff(c_1114, plain, (![A_140, C_141]: (r2_hidden('#skF_5'(A_140, k1_relat_1(A_140), C_141), k11_relat_1(A_140, C_141)) | ~v1_relat_1(A_140) | ~r2_hidden(C_141, k1_relat_1(A_140)))), inference(resolution, [status(thm)], [c_327, c_34])).
% 2.77/1.48  tff(c_1134, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_1114])).
% 2.77/1.48  tff(c_1139, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_230, c_36, c_1134])).
% 2.77/1.48  tff(c_1141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_1139])).
% 2.77/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.48  
% 2.77/1.48  Inference rules
% 2.77/1.48  ----------------------
% 2.77/1.48  #Ref     : 0
% 2.77/1.48  #Sup     : 237
% 2.77/1.48  #Fact    : 0
% 2.77/1.48  #Define  : 0
% 2.77/1.48  #Split   : 3
% 2.77/1.48  #Chain   : 0
% 2.77/1.48  #Close   : 0
% 2.77/1.48  
% 2.77/1.48  Ordering : KBO
% 2.77/1.48  
% 2.77/1.48  Simplification rules
% 2.77/1.48  ----------------------
% 2.77/1.48  #Subsume      : 50
% 2.77/1.48  #Demod        : 83
% 2.77/1.48  #Tautology    : 69
% 2.77/1.48  #SimpNegUnit  : 38
% 2.77/1.48  #BackRed      : 1
% 2.77/1.48  
% 2.77/1.48  #Partial instantiations: 0
% 2.77/1.48  #Strategies tried      : 1
% 2.77/1.48  
% 2.77/1.48  Timing (in seconds)
% 2.77/1.48  ----------------------
% 2.77/1.49  Preprocessing        : 0.30
% 2.77/1.49  Parsing              : 0.15
% 2.77/1.49  CNF conversion       : 0.02
% 2.77/1.49  Main loop            : 0.38
% 2.77/1.49  Inferencing          : 0.14
% 2.77/1.49  Reduction            : 0.11
% 2.77/1.49  Demodulation         : 0.07
% 2.77/1.49  BG Simplification    : 0.02
% 2.77/1.49  Subsumption          : 0.08
% 2.77/1.49  Abstraction          : 0.02
% 2.77/1.49  MUC search           : 0.00
% 2.77/1.49  Cooper               : 0.00
% 2.77/1.49  Total                : 0.71
% 2.77/1.49  Index Insertion      : 0.00
% 2.77/1.49  Index Deletion       : 0.00
% 2.77/1.49  Index Matching       : 0.00
% 2.77/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
