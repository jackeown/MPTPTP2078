%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:23 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   52 (  66 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 106 expanded)
%              Number of equality atoms :   12 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(f_77,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_59,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden(k4_tarski(A_34,B_35),C_36)
      | ~ r2_hidden(B_35,k11_relat_1(C_36,A_34))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(A_16,k1_relat_1(C_18))
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_136,plain,(
    ! [A_49,C_50,B_51] :
      ( r2_hidden(A_49,k1_relat_1(C_50))
      | ~ r2_hidden(B_51,k11_relat_1(C_50,A_49))
      | ~ v1_relat_1(C_50) ) ),
    inference(resolution,[status(thm)],[c_64,c_24])).

tff(c_149,plain,(
    ! [A_52,C_53] :
      ( r2_hidden(A_52,k1_relat_1(C_53))
      | ~ v1_relat_1(C_53)
      | k11_relat_1(C_53,A_52) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_136])).

tff(c_28,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_28])).

tff(c_164,plain,
    ( ~ v1_relat_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149,c_60])).

tff(c_170,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_164])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_170])).

tff(c_173,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_16,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    ! [A_21,B_22] :
      ( ~ r2_hidden(A_21,B_22)
      | ~ r1_xboole_0(k1_tarski(A_21),B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    ! [A_21] : ~ r2_hidden(A_21,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_37])).

tff(c_174,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_364,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_hidden(k4_tarski(A_95,'#skF_2'(A_95,B_96,C_97)),C_97)
      | ~ r2_hidden(A_95,k10_relat_1(C_97,B_96))
      | ~ v1_relat_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [B_14,C_15,A_13] :
      ( r2_hidden(B_14,k11_relat_1(C_15,A_13))
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_517,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden('#skF_2'(A_112,B_113,C_114),k11_relat_1(C_114,A_112))
      | ~ r2_hidden(A_112,k10_relat_1(C_114,B_113))
      | ~ v1_relat_1(C_114) ) ),
    inference(resolution,[status(thm)],[c_364,c_20])).

tff(c_531,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_2'('#skF_3',B_113,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_113))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_517])).

tff(c_537,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_2'('#skF_3',B_113,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_113)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_531])).

tff(c_539,plain,(
    ! [B_115] : ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_115)) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_537])).

tff(c_549,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_539])).

tff(c_554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_173,c_549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.32  
% 2.10/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.32  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.10/1.32  
% 2.10/1.32  %Foreground sorts:
% 2.10/1.32  
% 2.10/1.32  
% 2.10/1.32  %Background operators:
% 2.10/1.32  
% 2.10/1.32  
% 2.10/1.32  %Foreground operators:
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.32  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.10/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.10/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.32  
% 2.10/1.33  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.10/1.33  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.10/1.33  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.10/1.33  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.10/1.33  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.10/1.33  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.10/1.33  tff(f_40, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.10/1.33  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.10/1.33  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.10/1.33  tff(c_34, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4')) | k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.10/1.33  tff(c_59, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.10/1.33  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.33  tff(c_64, plain, (![A_34, B_35, C_36]: (r2_hidden(k4_tarski(A_34, B_35), C_36) | ~r2_hidden(B_35, k11_relat_1(C_36, A_34)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.33  tff(c_24, plain, (![A_16, C_18, B_17]: (r2_hidden(A_16, k1_relat_1(C_18)) | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.10/1.33  tff(c_136, plain, (![A_49, C_50, B_51]: (r2_hidden(A_49, k1_relat_1(C_50)) | ~r2_hidden(B_51, k11_relat_1(C_50, A_49)) | ~v1_relat_1(C_50))), inference(resolution, [status(thm)], [c_64, c_24])).
% 2.10/1.33  tff(c_149, plain, (![A_52, C_53]: (r2_hidden(A_52, k1_relat_1(C_53)) | ~v1_relat_1(C_53) | k11_relat_1(C_53, A_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_136])).
% 2.10/1.33  tff(c_28, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.10/1.33  tff(c_60, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_59, c_28])).
% 2.10/1.33  tff(c_164, plain, (~v1_relat_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_149, c_60])).
% 2.10/1.33  tff(c_170, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_164])).
% 2.10/1.33  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_170])).
% 2.10/1.33  tff(c_173, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_34])).
% 2.10/1.33  tff(c_16, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.33  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.33  tff(c_37, plain, (![A_21, B_22]: (~r2_hidden(A_21, B_22) | ~r1_xboole_0(k1_tarski(A_21), B_22))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.10/1.33  tff(c_42, plain, (![A_21]: (~r2_hidden(A_21, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_37])).
% 2.10/1.33  tff(c_174, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.10/1.33  tff(c_364, plain, (![A_95, B_96, C_97]: (r2_hidden(k4_tarski(A_95, '#skF_2'(A_95, B_96, C_97)), C_97) | ~r2_hidden(A_95, k10_relat_1(C_97, B_96)) | ~v1_relat_1(C_97))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.33  tff(c_20, plain, (![B_14, C_15, A_13]: (r2_hidden(B_14, k11_relat_1(C_15, A_13)) | ~r2_hidden(k4_tarski(A_13, B_14), C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.33  tff(c_517, plain, (![A_112, B_113, C_114]: (r2_hidden('#skF_2'(A_112, B_113, C_114), k11_relat_1(C_114, A_112)) | ~r2_hidden(A_112, k10_relat_1(C_114, B_113)) | ~v1_relat_1(C_114))), inference(resolution, [status(thm)], [c_364, c_20])).
% 2.10/1.33  tff(c_531, plain, (![B_113]: (r2_hidden('#skF_2'('#skF_3', B_113, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_113)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_174, c_517])).
% 2.10/1.33  tff(c_537, plain, (![B_113]: (r2_hidden('#skF_2'('#skF_3', B_113, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_113)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_531])).
% 2.10/1.33  tff(c_539, plain, (![B_115]: (~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_115)))), inference(negUnitSimplification, [status(thm)], [c_42, c_537])).
% 2.10/1.33  tff(c_549, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16, c_539])).
% 2.10/1.33  tff(c_554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_173, c_549])).
% 2.10/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.33  
% 2.10/1.33  Inference rules
% 2.10/1.33  ----------------------
% 2.10/1.33  #Ref     : 0
% 2.10/1.33  #Sup     : 109
% 2.10/1.33  #Fact    : 0
% 2.10/1.33  #Define  : 0
% 2.10/1.33  #Split   : 3
% 2.10/1.33  #Chain   : 0
% 2.10/1.33  #Close   : 0
% 2.10/1.33  
% 2.10/1.33  Ordering : KBO
% 2.10/1.33  
% 2.10/1.33  Simplification rules
% 2.10/1.33  ----------------------
% 2.10/1.33  #Subsume      : 22
% 2.10/1.33  #Demod        : 27
% 2.10/1.33  #Tautology    : 19
% 2.10/1.33  #SimpNegUnit  : 3
% 2.10/1.33  #BackRed      : 0
% 2.10/1.33  
% 2.10/1.33  #Partial instantiations: 0
% 2.10/1.33  #Strategies tried      : 1
% 2.10/1.33  
% 2.10/1.33  Timing (in seconds)
% 2.10/1.33  ----------------------
% 2.56/1.33  Preprocessing        : 0.28
% 2.56/1.33  Parsing              : 0.16
% 2.56/1.33  CNF conversion       : 0.02
% 2.56/1.33  Main loop            : 0.30
% 2.56/1.33  Inferencing          : 0.13
% 2.56/1.33  Reduction            : 0.07
% 2.56/1.33  Demodulation         : 0.04
% 2.56/1.33  BG Simplification    : 0.02
% 2.56/1.33  Subsumption          : 0.07
% 2.56/1.33  Abstraction          : 0.01
% 2.56/1.33  MUC search           : 0.00
% 2.56/1.33  Cooper               : 0.00
% 2.56/1.33  Total                : 0.61
% 2.56/1.33  Index Insertion      : 0.00
% 2.56/1.33  Index Deletion       : 0.00
% 2.56/1.33  Index Matching       : 0.00
% 2.56/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
