%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:01 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 104 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 188 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_92,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_25] :
      ( v1_relat_1(A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_51])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k5_relat_1(A_14,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_160,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_55,B_56)),k1_relat_1(A_55))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_171,plain,(
    ! [B_56] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_56)),k1_xboole_0)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_160])).

tff(c_244,plain,(
    ! [B_61] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_61)),k1_xboole_0)
      | ~ v1_relat_1(B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_171])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49),B_50)
      | ~ r1_tarski(A_49,B_50)
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ! [B_50,A_49] :
      ( ~ v1_xboole_0(B_50)
      | ~ r1_tarski(A_49,B_50)
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_247,plain,(
    ! [B_61] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_61)))
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_244,c_133])).

tff(c_260,plain,(
    ! [B_62] :
      ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_62)))
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_247])).

tff(c_26,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(k1_relat_1(A_16))
      | ~ v1_relat_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_365,plain,(
    ! [B_73] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_73))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_73))
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_260,c_26])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_784,plain,(
    ! [B_91] :
      ( k5_relat_1(k1_xboole_0,B_91) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_91))
      | ~ v1_relat_1(B_91) ) ),
    inference(resolution,[status(thm)],[c_365,c_14])).

tff(c_791,plain,(
    ! [B_15] :
      ( k5_relat_1(k1_xboole_0,B_15) = k1_xboole_0
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_784])).

tff(c_797,plain,(
    ! [B_92] :
      ( k5_relat_1(k1_xboole_0,B_92) = k1_xboole_0
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_791])).

tff(c_812,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_797])).

tff(c_821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_812])).

tff(c_822,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_976,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_121,B_122)),k2_relat_1(B_122))
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_990,plain,(
    ! [A_121] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_121,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_976])).

tff(c_1050,plain,(
    ! [A_124] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_124,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_990])).

tff(c_888,plain,(
    ! [C_110,B_111,A_112] :
      ( r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_895,plain,(
    ! [A_113,B_114] :
      ( r2_hidden('#skF_1'(A_113),B_114)
      | ~ r1_tarski(A_113,B_114)
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_4,c_888])).

tff(c_902,plain,(
    ! [B_114,A_113] :
      ( ~ v1_xboole_0(B_114)
      | ~ r1_tarski(A_113,B_114)
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_895,c_2])).

tff(c_1053,plain,(
    ! [A_124] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k2_relat_1(k5_relat_1(A_124,k1_xboole_0)))
      | ~ v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_1050,c_902])).

tff(c_1066,plain,(
    ! [A_125] :
      ( v1_xboole_0(k2_relat_1(k5_relat_1(A_125,k1_xboole_0)))
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1053])).

tff(c_28,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k2_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1369,plain,(
    ! [A_150] :
      ( ~ v1_relat_1(k5_relat_1(A_150,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_150,k1_xboole_0))
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_1066,c_28])).

tff(c_1400,plain,(
    ! [A_152] :
      ( k5_relat_1(A_152,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_152,k1_xboole_0))
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_1369,c_14])).

tff(c_1404,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_1400])).

tff(c_1509,plain,(
    ! [A_154] :
      ( k5_relat_1(A_154,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1404])).

tff(c_1524,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1509])).

tff(c_1533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_822,c_1524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.56  
% 3.25/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.56  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 3.25/1.56  
% 3.25/1.56  %Foreground sorts:
% 3.25/1.56  
% 3.25/1.56  
% 3.25/1.56  %Background operators:
% 3.25/1.56  
% 3.25/1.56  
% 3.25/1.56  %Foreground operators:
% 3.25/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.25/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.25/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.56  
% 3.43/1.58  tff(f_99, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.43/1.58  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.43/1.58  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.43/1.58  tff(f_59, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.43/1.58  tff(f_92, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.43/1.58  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.43/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.43/1.58  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.43/1.58  tff(f_67, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.43/1.58  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.43/1.58  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.43/1.58  tff(f_75, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.43/1.58  tff(c_38, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.43/1.58  tff(c_63, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 3.43/1.58  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.43/1.58  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.43/1.58  tff(c_51, plain, (![A_25]: (v1_relat_1(A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.43/1.58  tff(c_55, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_51])).
% 3.43/1.58  tff(c_24, plain, (![A_14, B_15]: (v1_relat_1(k5_relat_1(A_14, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.43/1.58  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.43/1.58  tff(c_160, plain, (![A_55, B_56]: (r1_tarski(k1_relat_1(k5_relat_1(A_55, B_56)), k1_relat_1(A_55)) | ~v1_relat_1(B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.43/1.58  tff(c_171, plain, (![B_56]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_56)), k1_xboole_0) | ~v1_relat_1(B_56) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_160])).
% 3.43/1.58  tff(c_244, plain, (![B_61]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_61)), k1_xboole_0) | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_171])).
% 3.43/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.58  tff(c_105, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.43/1.58  tff(c_126, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49), B_50) | ~r1_tarski(A_49, B_50) | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_4, c_105])).
% 3.43/1.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.58  tff(c_133, plain, (![B_50, A_49]: (~v1_xboole_0(B_50) | ~r1_tarski(A_49, B_50) | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_126, c_2])).
% 3.43/1.58  tff(c_247, plain, (![B_61]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_61))) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_244, c_133])).
% 3.43/1.58  tff(c_260, plain, (![B_62]: (v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_62))) | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_247])).
% 3.43/1.58  tff(c_26, plain, (![A_16]: (~v1_xboole_0(k1_relat_1(A_16)) | ~v1_relat_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.43/1.58  tff(c_365, plain, (![B_73]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_73)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_73)) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_260, c_26])).
% 3.43/1.58  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.43/1.58  tff(c_784, plain, (![B_91]: (k5_relat_1(k1_xboole_0, B_91)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_91)) | ~v1_relat_1(B_91))), inference(resolution, [status(thm)], [c_365, c_14])).
% 3.43/1.58  tff(c_791, plain, (![B_15]: (k5_relat_1(k1_xboole_0, B_15)=k1_xboole_0 | ~v1_relat_1(B_15) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_784])).
% 3.43/1.58  tff(c_797, plain, (![B_92]: (k5_relat_1(k1_xboole_0, B_92)=k1_xboole_0 | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_791])).
% 3.43/1.58  tff(c_812, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_797])).
% 3.43/1.58  tff(c_821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_812])).
% 3.43/1.58  tff(c_822, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.43/1.58  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.43/1.58  tff(c_976, plain, (![A_121, B_122]: (r1_tarski(k2_relat_1(k5_relat_1(A_121, B_122)), k2_relat_1(B_122)) | ~v1_relat_1(B_122) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.43/1.58  tff(c_990, plain, (![A_121]: (r1_tarski(k2_relat_1(k5_relat_1(A_121, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_34, c_976])).
% 3.43/1.58  tff(c_1050, plain, (![A_124]: (r1_tarski(k2_relat_1(k5_relat_1(A_124, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_990])).
% 3.43/1.58  tff(c_888, plain, (![C_110, B_111, A_112]: (r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.43/1.58  tff(c_895, plain, (![A_113, B_114]: (r2_hidden('#skF_1'(A_113), B_114) | ~r1_tarski(A_113, B_114) | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_4, c_888])).
% 3.43/1.58  tff(c_902, plain, (![B_114, A_113]: (~v1_xboole_0(B_114) | ~r1_tarski(A_113, B_114) | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_895, c_2])).
% 3.43/1.58  tff(c_1053, plain, (![A_124]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_relat_1(k5_relat_1(A_124, k1_xboole_0))) | ~v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_1050, c_902])).
% 3.43/1.58  tff(c_1066, plain, (![A_125]: (v1_xboole_0(k2_relat_1(k5_relat_1(A_125, k1_xboole_0))) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1053])).
% 3.43/1.58  tff(c_28, plain, (![A_17]: (~v1_xboole_0(k2_relat_1(A_17)) | ~v1_relat_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.58  tff(c_1369, plain, (![A_150]: (~v1_relat_1(k5_relat_1(A_150, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_150, k1_xboole_0)) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_1066, c_28])).
% 3.43/1.58  tff(c_1400, plain, (![A_152]: (k5_relat_1(A_152, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_152, k1_xboole_0)) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_1369, c_14])).
% 3.43/1.58  tff(c_1404, plain, (![A_14]: (k5_relat_1(A_14, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_24, c_1400])).
% 3.43/1.58  tff(c_1509, plain, (![A_154]: (k5_relat_1(A_154, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1404])).
% 3.43/1.58  tff(c_1524, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_1509])).
% 3.43/1.58  tff(c_1533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_822, c_1524])).
% 3.43/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.58  
% 3.43/1.58  Inference rules
% 3.43/1.58  ----------------------
% 3.43/1.58  #Ref     : 0
% 3.43/1.58  #Sup     : 337
% 3.43/1.58  #Fact    : 0
% 3.43/1.58  #Define  : 0
% 3.43/1.58  #Split   : 4
% 3.43/1.58  #Chain   : 0
% 3.43/1.58  #Close   : 0
% 3.43/1.58  
% 3.43/1.58  Ordering : KBO
% 3.43/1.58  
% 3.43/1.58  Simplification rules
% 3.43/1.58  ----------------------
% 3.43/1.58  #Subsume      : 58
% 3.43/1.58  #Demod        : 310
% 3.43/1.58  #Tautology    : 138
% 3.43/1.58  #SimpNegUnit  : 2
% 3.43/1.58  #BackRed      : 0
% 3.43/1.58  
% 3.43/1.58  #Partial instantiations: 0
% 3.43/1.58  #Strategies tried      : 1
% 3.43/1.58  
% 3.43/1.58  Timing (in seconds)
% 3.43/1.58  ----------------------
% 3.43/1.58  Preprocessing        : 0.28
% 3.43/1.58  Parsing              : 0.16
% 3.43/1.58  CNF conversion       : 0.02
% 3.43/1.58  Main loop            : 0.51
% 3.43/1.58  Inferencing          : 0.20
% 3.43/1.58  Reduction            : 0.14
% 3.43/1.58  Demodulation         : 0.10
% 3.43/1.59  BG Simplification    : 0.02
% 3.43/1.59  Subsumption          : 0.11
% 3.43/1.59  Abstraction          : 0.03
% 3.43/1.59  MUC search           : 0.00
% 3.43/1.59  Cooper               : 0.00
% 3.43/1.59  Total                : 0.83
% 3.43/1.59  Index Insertion      : 0.00
% 3.43/1.59  Index Deletion       : 0.00
% 3.43/1.59  Index Matching       : 0.00
% 3.43/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
