%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:23 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   57 (  71 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 106 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_113,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_114,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_188,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden(k4_tarski(A_54,B_55),C_56)
      | ~ r2_hidden(B_55,k11_relat_1(C_56,A_54))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    ! [A_24,C_26,B_25] :
      ( r2_hidden(A_24,k1_relat_1(C_26))
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_224,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(A_60,k1_relat_1(C_61))
      | ~ r2_hidden(B_62,k11_relat_1(C_61,A_60))
      | ~ v1_relat_1(C_61) ) ),
    inference(resolution,[status(thm)],[c_188,c_36])).

tff(c_233,plain,(
    ! [A_63,C_64] :
      ( r2_hidden(A_63,k1_relat_1(C_64))
      | ~ v1_relat_1(C_64)
      | k11_relat_1(C_64,A_63) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_224])).

tff(c_244,plain,
    ( ~ v1_relat_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_233,c_113])).

tff(c_249,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_244])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_249])).

tff(c_253,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_28,plain,(
    ! [A_20] :
      ( k10_relat_1(A_20,k2_relat_1(A_20)) = k1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [C_30,B_31] : ~ r2_hidden(C_30,k4_xboole_0(B_31,k1_tarski(C_30))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_64])).

tff(c_252,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_502,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden(k4_tarski(A_109,'#skF_2'(A_109,B_110,C_111)),C_111)
      | ~ r2_hidden(A_109,k10_relat_1(C_111,B_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [B_22,C_23,A_21] :
      ( r2_hidden(B_22,k11_relat_1(C_23,A_21))
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_863,plain,(
    ! [A_145,B_146,C_147] :
      ( r2_hidden('#skF_2'(A_145,B_146,C_147),k11_relat_1(C_147,A_145))
      | ~ r2_hidden(A_145,k10_relat_1(C_147,B_146))
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_502,c_32])).

tff(c_877,plain,(
    ! [B_146] :
      ( r2_hidden('#skF_2'('#skF_3',B_146,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_146))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_863])).

tff(c_883,plain,(
    ! [B_146] :
      ( r2_hidden('#skF_2'('#skF_3',B_146,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_146)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_877])).

tff(c_885,plain,(
    ! [B_148] : ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_148)) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_883])).

tff(c_899,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_885])).

tff(c_907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_253,c_899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.44  
% 2.67/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.44  %$ r2_hidden > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.67/1.44  
% 2.67/1.44  %Foreground sorts:
% 2.67/1.44  
% 2.67/1.44  
% 2.67/1.44  %Background operators:
% 2.67/1.44  
% 2.67/1.44  
% 2.67/1.44  %Foreground operators:
% 2.67/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.67/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.44  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.67/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.67/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.67/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.67/1.44  
% 2.95/1.45  tff(f_87, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.95/1.45  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.95/1.45  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.95/1.45  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.95/1.45  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.95/1.45  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.95/1.45  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.95/1.45  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.95/1.45  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.95/1.45  tff(c_40, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.95/1.45  tff(c_113, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.95/1.45  tff(c_46, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4')) | k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.95/1.45  tff(c_114, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_113, c_46])).
% 2.95/1.45  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.45  tff(c_188, plain, (![A_54, B_55, C_56]: (r2_hidden(k4_tarski(A_54, B_55), C_56) | ~r2_hidden(B_55, k11_relat_1(C_56, A_54)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.95/1.45  tff(c_36, plain, (![A_24, C_26, B_25]: (r2_hidden(A_24, k1_relat_1(C_26)) | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.45  tff(c_224, plain, (![A_60, C_61, B_62]: (r2_hidden(A_60, k1_relat_1(C_61)) | ~r2_hidden(B_62, k11_relat_1(C_61, A_60)) | ~v1_relat_1(C_61))), inference(resolution, [status(thm)], [c_188, c_36])).
% 2.95/1.45  tff(c_233, plain, (![A_63, C_64]: (r2_hidden(A_63, k1_relat_1(C_64)) | ~v1_relat_1(C_64) | k11_relat_1(C_64, A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_224])).
% 2.95/1.45  tff(c_244, plain, (~v1_relat_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_233, c_113])).
% 2.95/1.45  tff(c_249, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_244])).
% 2.95/1.45  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_249])).
% 2.95/1.45  tff(c_253, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 2.95/1.45  tff(c_28, plain, (![A_20]: (k10_relat_1(A_20, k2_relat_1(A_20))=k1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.45  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.95/1.45  tff(c_64, plain, (![C_30, B_31]: (~r2_hidden(C_30, k4_xboole_0(B_31, k1_tarski(C_30))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.95/1.45  tff(c_67, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_64])).
% 2.95/1.45  tff(c_252, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.95/1.45  tff(c_502, plain, (![A_109, B_110, C_111]: (r2_hidden(k4_tarski(A_109, '#skF_2'(A_109, B_110, C_111)), C_111) | ~r2_hidden(A_109, k10_relat_1(C_111, B_110)) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.95/1.45  tff(c_32, plain, (![B_22, C_23, A_21]: (r2_hidden(B_22, k11_relat_1(C_23, A_21)) | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.95/1.45  tff(c_863, plain, (![A_145, B_146, C_147]: (r2_hidden('#skF_2'(A_145, B_146, C_147), k11_relat_1(C_147, A_145)) | ~r2_hidden(A_145, k10_relat_1(C_147, B_146)) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_502, c_32])).
% 2.95/1.45  tff(c_877, plain, (![B_146]: (r2_hidden('#skF_2'('#skF_3', B_146, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_146)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_252, c_863])).
% 2.95/1.45  tff(c_883, plain, (![B_146]: (r2_hidden('#skF_2'('#skF_3', B_146, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_146)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_877])).
% 2.95/1.45  tff(c_885, plain, (![B_148]: (~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_148)))), inference(negUnitSimplification, [status(thm)], [c_67, c_883])).
% 2.95/1.45  tff(c_899, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_885])).
% 2.95/1.45  tff(c_907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_253, c_899])).
% 2.95/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.45  
% 2.95/1.45  Inference rules
% 2.95/1.45  ----------------------
% 2.95/1.45  #Ref     : 0
% 2.95/1.45  #Sup     : 186
% 2.95/1.45  #Fact    : 0
% 2.95/1.45  #Define  : 0
% 2.95/1.45  #Split   : 3
% 2.95/1.45  #Chain   : 0
% 2.95/1.45  #Close   : 0
% 2.95/1.45  
% 2.95/1.45  Ordering : KBO
% 2.95/1.45  
% 2.95/1.45  Simplification rules
% 2.95/1.45  ----------------------
% 2.95/1.45  #Subsume      : 40
% 2.95/1.45  #Demod        : 38
% 2.95/1.45  #Tautology    : 55
% 2.95/1.45  #SimpNegUnit  : 11
% 2.95/1.45  #BackRed      : 0
% 2.95/1.45  
% 2.95/1.45  #Partial instantiations: 0
% 2.95/1.45  #Strategies tried      : 1
% 2.95/1.45  
% 2.95/1.45  Timing (in seconds)
% 2.95/1.45  ----------------------
% 2.95/1.45  Preprocessing        : 0.29
% 2.95/1.45  Parsing              : 0.15
% 2.95/1.46  CNF conversion       : 0.02
% 2.95/1.46  Main loop            : 0.34
% 2.95/1.46  Inferencing          : 0.13
% 2.95/1.46  Reduction            : 0.09
% 2.95/1.46  Demodulation         : 0.06
% 2.95/1.46  BG Simplification    : 0.02
% 2.95/1.46  Subsumption          : 0.07
% 2.95/1.46  Abstraction          : 0.02
% 2.95/1.46  MUC search           : 0.00
% 2.95/1.46  Cooper               : 0.00
% 2.95/1.46  Total                : 0.66
% 2.95/1.46  Index Insertion      : 0.00
% 2.95/1.46  Index Deletion       : 0.00
% 2.95/1.46  Index Matching       : 0.00
% 2.95/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
