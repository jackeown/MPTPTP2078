%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:18 EST 2020

% Result     : Theorem 9.23s
% Output     : CNFRefutation 9.58s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 370 expanded)
%              Number of leaves         :   26 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          :  131 ( 881 expanded)
%              Number of equality atoms :   17 ( 115 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k8_relat_1(A_30,B_31),B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_95,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,C_57)
      | ~ r1_tarski(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,'#skF_9')
      | ~ r1_tarski(A_59,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_95])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_121,plain,(
    ! [A_61] :
      ( k3_xboole_0(A_61,'#skF_9') = A_61
      | ~ r1_tarski(A_61,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_105,c_22])).

tff(c_125,plain,(
    ! [A_30] :
      ( k3_xboole_0(k8_relat_1(A_30,'#skF_8'),'#skF_9') = k8_relat_1(A_30,'#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_30,c_121])).

tff(c_128,plain,(
    ! [A_30] : k3_xboole_0(k8_relat_1(A_30,'#skF_8'),'#skF_9') = k8_relat_1(A_30,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_125])).

tff(c_28,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    ! [D_48,B_49,A_50] :
      ( r2_hidden(D_48,B_49)
      | ~ r2_hidden(D_48,k3_xboole_0(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_210,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_73,B_74)),B_74)
      | v1_relat_1(k3_xboole_0(A_73,B_74)) ) ),
    inference(resolution,[status(thm)],[c_28,c_69])).

tff(c_225,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(k8_relat_1(A_30,'#skF_8')),'#skF_9')
      | v1_relat_1(k3_xboole_0(k8_relat_1(A_30,'#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_210])).

tff(c_235,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(k8_relat_1(A_30,'#skF_8')),'#skF_9')
      | v1_relat_1(k8_relat_1(A_30,'#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_225])).

tff(c_420,plain,(
    ! [A_97,B_98] :
      ( k4_tarski('#skF_4'(A_97,B_98),'#skF_5'(A_97,B_98)) = B_98
      | ~ r2_hidden(B_98,A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [C_25,D_26,A_12] :
      ( k4_tarski(C_25,D_26) != '#skF_3'(A_12)
      | v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_424,plain,(
    ! [B_98,A_12,A_97] :
      ( B_98 != '#skF_3'(A_12)
      | v1_relat_1(A_12)
      | ~ r2_hidden(B_98,A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_26])).

tff(c_435,plain,(
    ! [A_102,A_103] :
      ( v1_relat_1(A_102)
      | ~ r2_hidden('#skF_3'(A_102),A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_424])).

tff(c_441,plain,(
    ! [A_30] :
      ( ~ v1_relat_1('#skF_9')
      | v1_relat_1(k8_relat_1(A_30,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_235,c_435])).

tff(c_466,plain,(
    ! [A_30] : v1_relat_1(k8_relat_1(A_30,'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_441])).

tff(c_32,plain,(
    ! [B_33,A_32,C_34] :
      ( k8_relat_1(B_33,k8_relat_1(A_32,C_34)) = k8_relat_1(A_32,C_34)
      | ~ r1_tarski(A_32,B_33)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_312,plain,(
    ! [A_82,B_83,A_84] :
      ( r1_tarski(A_82,B_83)
      | ~ r1_tarski(A_82,k8_relat_1(A_84,B_83))
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_30,c_95])).

tff(c_716,plain,(
    ! [A_131,A_132,B_133] :
      ( r1_tarski(k8_relat_1(A_131,k8_relat_1(A_132,B_133)),B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(k8_relat_1(A_132,B_133)) ) ),
    inference(resolution,[status(thm)],[c_30,c_312])).

tff(c_112,plain,(
    ! [A_59] :
      ( k3_xboole_0(A_59,'#skF_9') = A_59
      | ~ r1_tarski(A_59,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_105,c_22])).

tff(c_738,plain,(
    ! [A_131,A_132] :
      ( k3_xboole_0(k8_relat_1(A_131,k8_relat_1(A_132,'#skF_8')),'#skF_9') = k8_relat_1(A_131,k8_relat_1(A_132,'#skF_8'))
      | ~ v1_relat_1('#skF_8')
      | ~ v1_relat_1(k8_relat_1(A_132,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_716,c_112])).

tff(c_767,plain,(
    ! [A_134,A_135] : k3_xboole_0(k8_relat_1(A_134,k8_relat_1(A_135,'#skF_8')),'#skF_9') = k8_relat_1(A_134,k8_relat_1(A_135,'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_44,c_738])).

tff(c_798,plain,(
    ! [B_33,A_32] :
      ( k8_relat_1(B_33,k8_relat_1(A_32,'#skF_8')) = k3_xboole_0(k8_relat_1(A_32,'#skF_8'),'#skF_9')
      | ~ r1_tarski(A_32,B_33)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_767])).

tff(c_844,plain,(
    ! [B_141,A_142] :
      ( k8_relat_1(B_141,k8_relat_1(A_142,'#skF_8')) = k8_relat_1(A_142,'#skF_8')
      | ~ r1_tarski(A_142,B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_128,c_798])).

tff(c_320,plain,(
    ! [A_30,A_84,B_83] :
      ( r1_tarski(k8_relat_1(A_30,k8_relat_1(A_84,B_83)),B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(k8_relat_1(A_84,B_83)) ) ),
    inference(resolution,[status(thm)],[c_30,c_312])).

tff(c_860,plain,(
    ! [A_142,B_141] :
      ( r1_tarski(k8_relat_1(A_142,'#skF_8'),'#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_relat_1(k8_relat_1(A_142,'#skF_8'))
      | ~ r1_tarski(A_142,B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_320])).

tff(c_1015,plain,(
    ! [A_146,B_147] :
      ( r1_tarski(k8_relat_1(A_146,'#skF_8'),'#skF_8')
      | ~ r1_tarski(A_146,B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_44,c_860])).

tff(c_1045,plain,(
    r1_tarski(k8_relat_1('#skF_6','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_1015])).

tff(c_901,plain,(
    ! [A_142,B_141] :
      ( r1_tarski(k8_relat_1(A_142,'#skF_8'),k8_relat_1(A_142,'#skF_8'))
      | ~ v1_relat_1(k8_relat_1(A_142,'#skF_8'))
      | ~ r1_tarski(A_142,B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_30])).

tff(c_1844,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(k8_relat_1(A_175,'#skF_8'),k8_relat_1(A_175,'#skF_8'))
      | ~ r1_tarski(A_175,B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_901])).

tff(c_1913,plain,(
    r1_tarski(k8_relat_1('#skF_6','#skF_8'),k8_relat_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_38,c_1844])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [A_7,A_59] :
      ( r1_tarski(A_7,'#skF_9')
      | ~ r1_tarski(A_7,A_59)
      | ~ r1_tarski(A_59,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_105,c_20])).

tff(c_1958,plain,
    ( r1_tarski(k8_relat_1('#skF_6','#skF_8'),'#skF_9')
    | ~ r1_tarski(k8_relat_1('#skF_6','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1913,c_111])).

tff(c_1976,plain,(
    r1_tarski(k8_relat_1('#skF_6','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_1958])).

tff(c_528,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(k8_relat_1(A_110,B_111),k8_relat_1(A_110,C_112))
      | ~ r1_tarski(B_111,C_112)
      | ~ v1_relat_1(C_112)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_11504,plain,(
    ! [A_380,C_381,B_382,C_383] :
      ( r1_tarski(k8_relat_1(A_380,C_381),k8_relat_1(B_382,C_383))
      | ~ r1_tarski(k8_relat_1(A_380,C_381),C_383)
      | ~ v1_relat_1(C_383)
      | ~ v1_relat_1(k8_relat_1(A_380,C_381))
      | ~ r1_tarski(A_380,B_382)
      | ~ v1_relat_1(C_381) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_528])).

tff(c_36,plain,(
    ~ r1_tarski(k8_relat_1('#skF_6','#skF_8'),k8_relat_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_11642,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_6','#skF_8'),'#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_8'))
    | ~ r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_11504,c_36])).

tff(c_11761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_466,c_42,c_1976,c_11642])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:50:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.23/3.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.23/3.16  
% 9.23/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.23/3.16  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 9.23/3.16  
% 9.23/3.16  %Foreground sorts:
% 9.23/3.16  
% 9.23/3.16  
% 9.23/3.16  %Background operators:
% 9.23/3.16  
% 9.23/3.16  
% 9.23/3.16  %Foreground operators:
% 9.23/3.16  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 9.23/3.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.23/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.23/3.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.23/3.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.23/3.16  tff('#skF_7', type, '#skF_7': $i).
% 9.23/3.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.23/3.16  tff('#skF_6', type, '#skF_6': $i).
% 9.23/3.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.23/3.16  tff('#skF_9', type, '#skF_9': $i).
% 9.23/3.16  tff('#skF_8', type, '#skF_8': $i).
% 9.23/3.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.23/3.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.23/3.16  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.23/3.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.23/3.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.23/3.16  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.23/3.16  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.23/3.16  
% 9.58/3.18  tff(f_85, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 9.58/3.18  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 9.58/3.18  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.58/3.18  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.58/3.18  tff(f_54, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 9.58/3.18  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.58/3.18  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 9.58/3.18  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 9.58/3.18  tff(c_44, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.58/3.18  tff(c_38, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.58/3.18  tff(c_42, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.58/3.18  tff(c_30, plain, (![A_30, B_31]: (r1_tarski(k8_relat_1(A_30, B_31), B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.58/3.18  tff(c_40, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.58/3.18  tff(c_95, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, C_57) | ~r1_tarski(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.58/3.18  tff(c_105, plain, (![A_59]: (r1_tarski(A_59, '#skF_9') | ~r1_tarski(A_59, '#skF_8'))), inference(resolution, [status(thm)], [c_40, c_95])).
% 9.58/3.18  tff(c_22, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.58/3.18  tff(c_121, plain, (![A_61]: (k3_xboole_0(A_61, '#skF_9')=A_61 | ~r1_tarski(A_61, '#skF_8'))), inference(resolution, [status(thm)], [c_105, c_22])).
% 9.58/3.18  tff(c_125, plain, (![A_30]: (k3_xboole_0(k8_relat_1(A_30, '#skF_8'), '#skF_9')=k8_relat_1(A_30, '#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_30, c_121])).
% 9.58/3.18  tff(c_128, plain, (![A_30]: (k3_xboole_0(k8_relat_1(A_30, '#skF_8'), '#skF_9')=k8_relat_1(A_30, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_125])).
% 9.58/3.18  tff(c_28, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.58/3.18  tff(c_69, plain, (![D_48, B_49, A_50]: (r2_hidden(D_48, B_49) | ~r2_hidden(D_48, k3_xboole_0(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.58/3.18  tff(c_210, plain, (![A_73, B_74]: (r2_hidden('#skF_3'(k3_xboole_0(A_73, B_74)), B_74) | v1_relat_1(k3_xboole_0(A_73, B_74)))), inference(resolution, [status(thm)], [c_28, c_69])).
% 9.58/3.18  tff(c_225, plain, (![A_30]: (r2_hidden('#skF_3'(k8_relat_1(A_30, '#skF_8')), '#skF_9') | v1_relat_1(k3_xboole_0(k8_relat_1(A_30, '#skF_8'), '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_128, c_210])).
% 9.58/3.18  tff(c_235, plain, (![A_30]: (r2_hidden('#skF_3'(k8_relat_1(A_30, '#skF_8')), '#skF_9') | v1_relat_1(k8_relat_1(A_30, '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_225])).
% 9.58/3.18  tff(c_420, plain, (![A_97, B_98]: (k4_tarski('#skF_4'(A_97, B_98), '#skF_5'(A_97, B_98))=B_98 | ~r2_hidden(B_98, A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.58/3.18  tff(c_26, plain, (![C_25, D_26, A_12]: (k4_tarski(C_25, D_26)!='#skF_3'(A_12) | v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.58/3.18  tff(c_424, plain, (![B_98, A_12, A_97]: (B_98!='#skF_3'(A_12) | v1_relat_1(A_12) | ~r2_hidden(B_98, A_97) | ~v1_relat_1(A_97))), inference(superposition, [status(thm), theory('equality')], [c_420, c_26])).
% 9.58/3.18  tff(c_435, plain, (![A_102, A_103]: (v1_relat_1(A_102) | ~r2_hidden('#skF_3'(A_102), A_103) | ~v1_relat_1(A_103))), inference(reflexivity, [status(thm), theory('equality')], [c_424])).
% 9.58/3.18  tff(c_441, plain, (![A_30]: (~v1_relat_1('#skF_9') | v1_relat_1(k8_relat_1(A_30, '#skF_8')))), inference(resolution, [status(thm)], [c_235, c_435])).
% 9.58/3.18  tff(c_466, plain, (![A_30]: (v1_relat_1(k8_relat_1(A_30, '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_441])).
% 9.58/3.18  tff(c_32, plain, (![B_33, A_32, C_34]: (k8_relat_1(B_33, k8_relat_1(A_32, C_34))=k8_relat_1(A_32, C_34) | ~r1_tarski(A_32, B_33) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.58/3.18  tff(c_312, plain, (![A_82, B_83, A_84]: (r1_tarski(A_82, B_83) | ~r1_tarski(A_82, k8_relat_1(A_84, B_83)) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_30, c_95])).
% 9.58/3.18  tff(c_716, plain, (![A_131, A_132, B_133]: (r1_tarski(k8_relat_1(A_131, k8_relat_1(A_132, B_133)), B_133) | ~v1_relat_1(B_133) | ~v1_relat_1(k8_relat_1(A_132, B_133)))), inference(resolution, [status(thm)], [c_30, c_312])).
% 9.58/3.18  tff(c_112, plain, (![A_59]: (k3_xboole_0(A_59, '#skF_9')=A_59 | ~r1_tarski(A_59, '#skF_8'))), inference(resolution, [status(thm)], [c_105, c_22])).
% 9.58/3.18  tff(c_738, plain, (![A_131, A_132]: (k3_xboole_0(k8_relat_1(A_131, k8_relat_1(A_132, '#skF_8')), '#skF_9')=k8_relat_1(A_131, k8_relat_1(A_132, '#skF_8')) | ~v1_relat_1('#skF_8') | ~v1_relat_1(k8_relat_1(A_132, '#skF_8')))), inference(resolution, [status(thm)], [c_716, c_112])).
% 9.58/3.18  tff(c_767, plain, (![A_134, A_135]: (k3_xboole_0(k8_relat_1(A_134, k8_relat_1(A_135, '#skF_8')), '#skF_9')=k8_relat_1(A_134, k8_relat_1(A_135, '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_44, c_738])).
% 9.58/3.18  tff(c_798, plain, (![B_33, A_32]: (k8_relat_1(B_33, k8_relat_1(A_32, '#skF_8'))=k3_xboole_0(k8_relat_1(A_32, '#skF_8'), '#skF_9') | ~r1_tarski(A_32, B_33) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_767])).
% 9.58/3.18  tff(c_844, plain, (![B_141, A_142]: (k8_relat_1(B_141, k8_relat_1(A_142, '#skF_8'))=k8_relat_1(A_142, '#skF_8') | ~r1_tarski(A_142, B_141))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_128, c_798])).
% 9.58/3.18  tff(c_320, plain, (![A_30, A_84, B_83]: (r1_tarski(k8_relat_1(A_30, k8_relat_1(A_84, B_83)), B_83) | ~v1_relat_1(B_83) | ~v1_relat_1(k8_relat_1(A_84, B_83)))), inference(resolution, [status(thm)], [c_30, c_312])).
% 9.58/3.18  tff(c_860, plain, (![A_142, B_141]: (r1_tarski(k8_relat_1(A_142, '#skF_8'), '#skF_8') | ~v1_relat_1('#skF_8') | ~v1_relat_1(k8_relat_1(A_142, '#skF_8')) | ~r1_tarski(A_142, B_141))), inference(superposition, [status(thm), theory('equality')], [c_844, c_320])).
% 9.58/3.18  tff(c_1015, plain, (![A_146, B_147]: (r1_tarski(k8_relat_1(A_146, '#skF_8'), '#skF_8') | ~r1_tarski(A_146, B_147))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_44, c_860])).
% 9.58/3.18  tff(c_1045, plain, (r1_tarski(k8_relat_1('#skF_6', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_38, c_1015])).
% 9.58/3.18  tff(c_901, plain, (![A_142, B_141]: (r1_tarski(k8_relat_1(A_142, '#skF_8'), k8_relat_1(A_142, '#skF_8')) | ~v1_relat_1(k8_relat_1(A_142, '#skF_8')) | ~r1_tarski(A_142, B_141))), inference(superposition, [status(thm), theory('equality')], [c_844, c_30])).
% 9.58/3.18  tff(c_1844, plain, (![A_175, B_176]: (r1_tarski(k8_relat_1(A_175, '#skF_8'), k8_relat_1(A_175, '#skF_8')) | ~r1_tarski(A_175, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_901])).
% 9.58/3.18  tff(c_1913, plain, (r1_tarski(k8_relat_1('#skF_6', '#skF_8'), k8_relat_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_38, c_1844])).
% 9.58/3.18  tff(c_20, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.58/3.18  tff(c_111, plain, (![A_7, A_59]: (r1_tarski(A_7, '#skF_9') | ~r1_tarski(A_7, A_59) | ~r1_tarski(A_59, '#skF_8'))), inference(resolution, [status(thm)], [c_105, c_20])).
% 9.58/3.18  tff(c_1958, plain, (r1_tarski(k8_relat_1('#skF_6', '#skF_8'), '#skF_9') | ~r1_tarski(k8_relat_1('#skF_6', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_1913, c_111])).
% 9.58/3.18  tff(c_1976, plain, (r1_tarski(k8_relat_1('#skF_6', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_1958])).
% 9.58/3.18  tff(c_528, plain, (![A_110, B_111, C_112]: (r1_tarski(k8_relat_1(A_110, B_111), k8_relat_1(A_110, C_112)) | ~r1_tarski(B_111, C_112) | ~v1_relat_1(C_112) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.58/3.18  tff(c_11504, plain, (![A_380, C_381, B_382, C_383]: (r1_tarski(k8_relat_1(A_380, C_381), k8_relat_1(B_382, C_383)) | ~r1_tarski(k8_relat_1(A_380, C_381), C_383) | ~v1_relat_1(C_383) | ~v1_relat_1(k8_relat_1(A_380, C_381)) | ~r1_tarski(A_380, B_382) | ~v1_relat_1(C_381))), inference(superposition, [status(thm), theory('equality')], [c_32, c_528])).
% 9.58/3.18  tff(c_36, plain, (~r1_tarski(k8_relat_1('#skF_6', '#skF_8'), k8_relat_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.58/3.18  tff(c_11642, plain, (~r1_tarski(k8_relat_1('#skF_6', '#skF_8'), '#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1(k8_relat_1('#skF_6', '#skF_8')) | ~r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_11504, c_36])).
% 9.58/3.18  tff(c_11761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_466, c_42, c_1976, c_11642])).
% 9.58/3.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/3.18  
% 9.58/3.18  Inference rules
% 9.58/3.18  ----------------------
% 9.58/3.18  #Ref     : 1
% 9.58/3.18  #Sup     : 2665
% 9.58/3.18  #Fact    : 0
% 9.58/3.18  #Define  : 0
% 9.58/3.18  #Split   : 11
% 9.58/3.18  #Chain   : 0
% 9.58/3.18  #Close   : 0
% 9.58/3.18  
% 9.58/3.18  Ordering : KBO
% 9.58/3.18  
% 9.58/3.18  Simplification rules
% 9.58/3.18  ----------------------
% 9.58/3.18  #Subsume      : 509
% 9.58/3.18  #Demod        : 1575
% 9.58/3.18  #Tautology    : 679
% 9.58/3.18  #SimpNegUnit  : 0
% 9.58/3.18  #BackRed      : 0
% 9.58/3.18  
% 9.58/3.18  #Partial instantiations: 0
% 9.58/3.18  #Strategies tried      : 1
% 9.58/3.18  
% 9.58/3.18  Timing (in seconds)
% 9.58/3.18  ----------------------
% 9.58/3.18  Preprocessing        : 0.30
% 9.58/3.18  Parsing              : 0.16
% 9.58/3.18  CNF conversion       : 0.03
% 9.58/3.18  Main loop            : 2.11
% 9.58/3.18  Inferencing          : 0.55
% 9.58/3.18  Reduction            : 0.74
% 9.58/3.18  Demodulation         : 0.57
% 9.58/3.18  BG Simplification    : 0.07
% 9.58/3.18  Subsumption          : 0.61
% 9.58/3.18  Abstraction          : 0.09
% 9.58/3.18  MUC search           : 0.00
% 9.58/3.18  Cooper               : 0.00
% 9.58/3.18  Total                : 2.45
% 9.58/3.18  Index Insertion      : 0.00
% 9.58/3.18  Index Deletion       : 0.00
% 9.58/3.18  Index Matching       : 0.00
% 9.58/3.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
