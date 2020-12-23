%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:23 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   53 (  67 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 106 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_36])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k4_tarski(A_40,B_41),C_42)
      | ~ r2_hidden(B_41,k11_relat_1(C_42,A_40))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(A_19,k1_relat_1(C_21))
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_146,plain,(
    ! [A_52,C_53,B_54] :
      ( r2_hidden(A_52,k1_relat_1(C_53))
      | ~ r2_hidden(B_54,k11_relat_1(C_53,A_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_75,c_26])).

tff(c_159,plain,(
    ! [A_55,C_56] :
      ( r2_hidden(A_55,k1_relat_1(C_56))
      | ~ v1_relat_1(C_56)
      | k11_relat_1(C_56,A_55) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_146])).

tff(c_174,plain,
    ( ~ v1_relat_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_159,c_48])).

tff(c_180,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_174])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_180])).

tff(c_184,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_18,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [A_57,C_58,B_59] :
      ( ~ r2_hidden(A_57,C_58)
      | ~ r1_xboole_0(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_194,plain,(
    ! [A_57] : ~ r2_hidden(A_57,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_183,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_364,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k4_tarski(A_96,'#skF_2'(A_96,B_97,C_98)),C_98)
      | ~ r2_hidden(A_96,k10_relat_1(C_98,B_97))
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [B_17,C_18,A_16] :
      ( r2_hidden(B_17,k11_relat_1(C_18,A_16))
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_549,plain,(
    ! [A_120,B_121,C_122] :
      ( r2_hidden('#skF_2'(A_120,B_121,C_122),k11_relat_1(C_122,A_120))
      | ~ r2_hidden(A_120,k10_relat_1(C_122,B_121))
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_364,c_22])).

tff(c_563,plain,(
    ! [B_121] :
      ( r2_hidden('#skF_2'('#skF_3',B_121,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_121))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_549])).

tff(c_569,plain,(
    ! [B_121] :
      ( r2_hidden('#skF_2'('#skF_3',B_121,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_121)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_563])).

tff(c_599,plain,(
    ! [B_125] : ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_125)) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_569])).

tff(c_613,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_599])).

tff(c_621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_184,c_613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:13:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.42  
% 2.54/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.42  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.54/1.42  
% 2.54/1.42  %Foreground sorts:
% 2.54/1.42  
% 2.54/1.42  
% 2.54/1.42  %Background operators:
% 2.54/1.42  
% 2.54/1.42  
% 2.54/1.42  %Foreground operators:
% 2.54/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.42  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.54/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.54/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.42  
% 2.79/1.43  tff(f_79, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.79/1.43  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.79/1.43  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.79/1.43  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.79/1.43  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.79/1.43  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.79/1.43  tff(f_42, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.79/1.43  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.79/1.43  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.79/1.43  tff(c_30, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.79/1.43  tff(c_48, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.79/1.43  tff(c_36, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4')) | k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.79/1.43  tff(c_49, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_36])).
% 2.79/1.43  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.43  tff(c_75, plain, (![A_40, B_41, C_42]: (r2_hidden(k4_tarski(A_40, B_41), C_42) | ~r2_hidden(B_41, k11_relat_1(C_42, A_40)) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.79/1.43  tff(c_26, plain, (![A_19, C_21, B_20]: (r2_hidden(A_19, k1_relat_1(C_21)) | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.43  tff(c_146, plain, (![A_52, C_53, B_54]: (r2_hidden(A_52, k1_relat_1(C_53)) | ~r2_hidden(B_54, k11_relat_1(C_53, A_52)) | ~v1_relat_1(C_53))), inference(resolution, [status(thm)], [c_75, c_26])).
% 2.79/1.43  tff(c_159, plain, (![A_55, C_56]: (r2_hidden(A_55, k1_relat_1(C_56)) | ~v1_relat_1(C_56) | k11_relat_1(C_56, A_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_146])).
% 2.79/1.43  tff(c_174, plain, (~v1_relat_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_159, c_48])).
% 2.79/1.43  tff(c_180, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_174])).
% 2.79/1.43  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_180])).
% 2.79/1.43  tff(c_184, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_30])).
% 2.79/1.43  tff(c_18, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.43  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.43  tff(c_189, plain, (![A_57, C_58, B_59]: (~r2_hidden(A_57, C_58) | ~r1_xboole_0(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.43  tff(c_194, plain, (![A_57]: (~r2_hidden(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_189])).
% 2.79/1.43  tff(c_183, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.79/1.43  tff(c_364, plain, (![A_96, B_97, C_98]: (r2_hidden(k4_tarski(A_96, '#skF_2'(A_96, B_97, C_98)), C_98) | ~r2_hidden(A_96, k10_relat_1(C_98, B_97)) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.79/1.43  tff(c_22, plain, (![B_17, C_18, A_16]: (r2_hidden(B_17, k11_relat_1(C_18, A_16)) | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.79/1.43  tff(c_549, plain, (![A_120, B_121, C_122]: (r2_hidden('#skF_2'(A_120, B_121, C_122), k11_relat_1(C_122, A_120)) | ~r2_hidden(A_120, k10_relat_1(C_122, B_121)) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_364, c_22])).
% 2.79/1.43  tff(c_563, plain, (![B_121]: (r2_hidden('#skF_2'('#skF_3', B_121, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_121)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_549])).
% 2.79/1.43  tff(c_569, plain, (![B_121]: (r2_hidden('#skF_2'('#skF_3', B_121, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_121)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_563])).
% 2.79/1.43  tff(c_599, plain, (![B_125]: (~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_125)))), inference(negUnitSimplification, [status(thm)], [c_194, c_569])).
% 2.79/1.43  tff(c_613, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_599])).
% 2.79/1.43  tff(c_621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_184, c_613])).
% 2.79/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  Inference rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Ref     : 0
% 2.79/1.43  #Sup     : 122
% 2.79/1.43  #Fact    : 0
% 2.79/1.43  #Define  : 0
% 2.79/1.43  #Split   : 3
% 2.79/1.43  #Chain   : 0
% 2.79/1.43  #Close   : 0
% 2.79/1.43  
% 2.79/1.43  Ordering : KBO
% 2.79/1.43  
% 2.79/1.43  Simplification rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Subsume      : 24
% 2.79/1.43  #Demod        : 28
% 2.79/1.43  #Tautology    : 24
% 2.79/1.43  #SimpNegUnit  : 3
% 2.79/1.43  #BackRed      : 0
% 2.79/1.43  
% 2.79/1.43  #Partial instantiations: 0
% 2.79/1.43  #Strategies tried      : 1
% 2.79/1.43  
% 2.79/1.43  Timing (in seconds)
% 2.79/1.43  ----------------------
% 2.79/1.44  Preprocessing        : 0.32
% 2.79/1.44  Parsing              : 0.16
% 2.79/1.44  CNF conversion       : 0.02
% 2.79/1.44  Main loop            : 0.35
% 2.79/1.44  Inferencing          : 0.14
% 2.79/1.44  Reduction            : 0.09
% 2.79/1.44  Demodulation         : 0.05
% 2.79/1.44  BG Simplification    : 0.02
% 2.79/1.44  Subsumption          : 0.07
% 2.79/1.44  Abstraction          : 0.03
% 2.79/1.44  MUC search           : 0.00
% 2.79/1.44  Cooper               : 0.00
% 2.79/1.44  Total                : 0.71
% 2.79/1.44  Index Insertion      : 0.00
% 2.79/1.44  Index Deletion       : 0.00
% 2.79/1.44  Index Matching       : 0.00
% 2.79/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
