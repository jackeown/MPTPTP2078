%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:55 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 131 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 245 expanded)
%              Number of equality atoms :   57 ( 131 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_91,plain,(
    ! [A_50] :
      ( k1_relat_1(A_50) = k1_xboole_0
      | k2_relat_1(A_50) != k1_xboole_0
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_95,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_91])).

tff(c_96,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),A_26)
      | k1_xboole_0 = A_26
      | k1_tarski(B_27) = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_113,plain,(
    ! [A_58,B_59] :
      ( k9_relat_1(A_58,k1_tarski(B_59)) = k11_relat_1(A_58,B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_134,plain,(
    ! [A_63] :
      ( k9_relat_1(A_63,k1_relat_1('#skF_3')) = k11_relat_1(A_63,'#skF_2')
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_113])).

tff(c_28,plain,(
    ! [A_32] :
      ( k9_relat_1(A_32,k1_relat_1(A_32)) = k2_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_141,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_28])).

tff(c_151,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_141])).

tff(c_30,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_223,plain,(
    ! [C_88,A_89,B_90] :
      ( k1_funct_1(C_88,A_89) = B_90
      | ~ r2_hidden(k4_tarski(A_89,B_90),C_88)
      | ~ v1_funct_1(C_88)
      | ~ v1_relat_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_261,plain,(
    ! [C_105,A_106,B_107] :
      ( k1_funct_1(C_105,A_106) = B_107
      | ~ v1_funct_1(C_105)
      | ~ r2_hidden(B_107,k11_relat_1(C_105,A_106))
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_30,c_223])).

tff(c_272,plain,(
    ! [B_107] :
      ( k1_funct_1('#skF_3','#skF_2') = B_107
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_107,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_261])).

tff(c_277,plain,(
    ! [B_108] :
      ( k1_funct_1('#skF_3','#skF_2') = B_108
      | ~ r2_hidden(B_108,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_272])).

tff(c_285,plain,(
    ! [B_27] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_27) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_27) ) ),
    inference(resolution,[status(thm)],[c_24,c_277])).

tff(c_290,plain,(
    ! [B_109] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_109) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_109) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_285])).

tff(c_22,plain,(
    ! [A_26,B_27] :
      ( '#skF_1'(A_26,B_27) != B_27
      | k1_xboole_0 = A_26
      | k1_tarski(B_27) = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_298,plain,(
    ! [B_109] :
      ( k1_funct_1('#skF_3','#skF_2') != B_109
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_109)
      | k2_relat_1('#skF_3') = k1_tarski(B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_22])).

tff(c_306,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_298])).

tff(c_48,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_48])).

tff(c_311,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_310,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_316,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_28])).

tff(c_320,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_316])).

tff(c_331,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_320])).

tff(c_312,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_50])).

tff(c_354,plain,(
    ! [A_117,B_118] :
      ( k9_relat_1(A_117,k1_tarski(B_118)) = k11_relat_1(A_117,B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_366,plain,(
    ! [A_119] :
      ( k9_relat_1(A_119,k1_xboole_0) = k11_relat_1(A_119,'#skF_2')
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_354])).

tff(c_369,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k11_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_366])).

tff(c_371,plain,(
    k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_369])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_47,C_48,B_49] :
      ( r2_hidden(A_47,C_48)
      | ~ r1_tarski(k2_tarski(A_47,B_49),C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_343,plain,(
    ! [A_111,C_112] :
      ( r2_hidden(A_111,C_112)
      | ~ r1_tarski(k1_tarski(A_111),C_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_346,plain,(
    ! [C_112] :
      ( r2_hidden('#skF_2',C_112)
      | ~ r1_tarski(k1_xboole_0,C_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_343])).

tff(c_348,plain,(
    ! [C_112] : r2_hidden('#skF_2',C_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_346])).

tff(c_387,plain,(
    ! [B_127,A_128] :
      ( k11_relat_1(B_127,A_128) != k1_xboole_0
      | ~ r2_hidden(A_128,k1_relat_1(B_127))
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_403,plain,(
    ! [B_129] :
      ( k11_relat_1(B_129,'#skF_2') != k1_xboole_0
      | ~ v1_relat_1(B_129) ) ),
    inference(resolution,[status(thm)],[c_348,c_387])).

tff(c_406,plain,(
    k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_403])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.62  
% 2.49/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.62  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.62  
% 2.49/1.62  %Foreground sorts:
% 2.49/1.62  
% 2.49/1.62  
% 2.49/1.62  %Background operators:
% 2.49/1.62  
% 2.49/1.62  
% 2.49/1.62  %Foreground operators:
% 2.49/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.49/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.62  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.49/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.62  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.49/1.62  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.62  
% 2.49/1.63  tff(f_106, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.49/1.63  tff(f_87, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.49/1.63  tff(f_59, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.49/1.63  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.49/1.63  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.49/1.63  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.49/1.63  tff(f_97, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.49/1.63  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.49/1.63  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.49/1.63  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.49/1.63  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.49/1.63  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.49/1.63  tff(c_91, plain, (![A_50]: (k1_relat_1(A_50)=k1_xboole_0 | k2_relat_1(A_50)!=k1_xboole_0 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.49/1.63  tff(c_95, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_91])).
% 2.49/1.63  tff(c_96, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_95])).
% 2.49/1.63  tff(c_24, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), A_26) | k1_xboole_0=A_26 | k1_tarski(B_27)=A_26)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.49/1.63  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.49/1.63  tff(c_50, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.49/1.63  tff(c_113, plain, (![A_58, B_59]: (k9_relat_1(A_58, k1_tarski(B_59))=k11_relat_1(A_58, B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.49/1.63  tff(c_134, plain, (![A_63]: (k9_relat_1(A_63, k1_relat_1('#skF_3'))=k11_relat_1(A_63, '#skF_2') | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_50, c_113])).
% 2.49/1.63  tff(c_28, plain, (![A_32]: (k9_relat_1(A_32, k1_relat_1(A_32))=k2_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.63  tff(c_141, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_134, c_28])).
% 2.49/1.63  tff(c_151, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_141])).
% 2.49/1.63  tff(c_30, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski(A_33, B_34), C_35) | ~r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.63  tff(c_223, plain, (![C_88, A_89, B_90]: (k1_funct_1(C_88, A_89)=B_90 | ~r2_hidden(k4_tarski(A_89, B_90), C_88) | ~v1_funct_1(C_88) | ~v1_relat_1(C_88))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.49/1.63  tff(c_261, plain, (![C_105, A_106, B_107]: (k1_funct_1(C_105, A_106)=B_107 | ~v1_funct_1(C_105) | ~r2_hidden(B_107, k11_relat_1(C_105, A_106)) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_30, c_223])).
% 2.49/1.63  tff(c_272, plain, (![B_107]: (k1_funct_1('#skF_3', '#skF_2')=B_107 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_107, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_261])).
% 2.49/1.63  tff(c_277, plain, (![B_108]: (k1_funct_1('#skF_3', '#skF_2')=B_108 | ~r2_hidden(B_108, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_272])).
% 2.49/1.63  tff(c_285, plain, (![B_27]: ('#skF_1'(k2_relat_1('#skF_3'), B_27)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_27))), inference(resolution, [status(thm)], [c_24, c_277])).
% 2.49/1.63  tff(c_290, plain, (![B_109]: ('#skF_1'(k2_relat_1('#skF_3'), B_109)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_109))), inference(negUnitSimplification, [status(thm)], [c_96, c_285])).
% 2.49/1.63  tff(c_22, plain, (![A_26, B_27]: ('#skF_1'(A_26, B_27)!=B_27 | k1_xboole_0=A_26 | k1_tarski(B_27)=A_26)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.49/1.63  tff(c_298, plain, (![B_109]: (k1_funct_1('#skF_3', '#skF_2')!=B_109 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_109) | k2_relat_1('#skF_3')=k1_tarski(B_109))), inference(superposition, [status(thm), theory('equality')], [c_290, c_22])).
% 2.49/1.63  tff(c_306, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_96, c_298])).
% 2.49/1.63  tff(c_48, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.49/1.63  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_306, c_48])).
% 2.49/1.63  tff(c_311, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_95])).
% 2.49/1.63  tff(c_310, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_95])).
% 2.49/1.63  tff(c_316, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_310, c_28])).
% 2.49/1.63  tff(c_320, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_316])).
% 2.49/1.63  tff(c_331, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_311, c_320])).
% 2.49/1.63  tff(c_312, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_310, c_50])).
% 2.49/1.63  tff(c_354, plain, (![A_117, B_118]: (k9_relat_1(A_117, k1_tarski(B_118))=k11_relat_1(A_117, B_118) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.49/1.63  tff(c_366, plain, (![A_119]: (k9_relat_1(A_119, k1_xboole_0)=k11_relat_1(A_119, '#skF_2') | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_312, c_354])).
% 2.49/1.63  tff(c_369, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k11_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_366])).
% 2.49/1.63  tff(c_371, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_331, c_369])).
% 2.49/1.63  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.63  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.63  tff(c_87, plain, (![A_47, C_48, B_49]: (r2_hidden(A_47, C_48) | ~r1_tarski(k2_tarski(A_47, B_49), C_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.49/1.63  tff(c_343, plain, (![A_111, C_112]: (r2_hidden(A_111, C_112) | ~r1_tarski(k1_tarski(A_111), C_112))), inference(superposition, [status(thm), theory('equality')], [c_4, c_87])).
% 2.49/1.63  tff(c_346, plain, (![C_112]: (r2_hidden('#skF_2', C_112) | ~r1_tarski(k1_xboole_0, C_112))), inference(superposition, [status(thm), theory('equality')], [c_312, c_343])).
% 2.49/1.63  tff(c_348, plain, (![C_112]: (r2_hidden('#skF_2', C_112))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_346])).
% 2.49/1.63  tff(c_387, plain, (![B_127, A_128]: (k11_relat_1(B_127, A_128)!=k1_xboole_0 | ~r2_hidden(A_128, k1_relat_1(B_127)) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.49/1.63  tff(c_403, plain, (![B_129]: (k11_relat_1(B_129, '#skF_2')!=k1_xboole_0 | ~v1_relat_1(B_129))), inference(resolution, [status(thm)], [c_348, c_387])).
% 2.49/1.63  tff(c_406, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_403])).
% 2.49/1.63  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_371, c_406])).
% 2.49/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.63  
% 2.49/1.63  Inference rules
% 2.49/1.63  ----------------------
% 2.49/1.63  #Ref     : 0
% 2.49/1.63  #Sup     : 78
% 2.49/1.63  #Fact    : 0
% 2.49/1.63  #Define  : 0
% 2.49/1.63  #Split   : 1
% 2.49/1.63  #Chain   : 0
% 2.49/1.63  #Close   : 0
% 2.49/1.63  
% 2.49/1.63  Ordering : KBO
% 2.49/1.63  
% 2.49/1.63  Simplification rules
% 2.49/1.63  ----------------------
% 2.49/1.63  #Subsume      : 2
% 2.49/1.63  #Demod        : 18
% 2.49/1.63  #Tautology    : 46
% 2.49/1.63  #SimpNegUnit  : 4
% 2.49/1.63  #BackRed      : 3
% 2.49/1.63  
% 2.49/1.63  #Partial instantiations: 0
% 2.49/1.63  #Strategies tried      : 1
% 2.49/1.63  
% 2.49/1.63  Timing (in seconds)
% 2.49/1.63  ----------------------
% 2.49/1.64  Preprocessing        : 0.48
% 2.49/1.64  Parsing              : 0.27
% 2.49/1.64  CNF conversion       : 0.03
% 2.49/1.64  Main loop            : 0.25
% 2.49/1.64  Inferencing          : 0.10
% 2.49/1.64  Reduction            : 0.07
% 2.49/1.64  Demodulation         : 0.04
% 2.49/1.64  BG Simplification    : 0.02
% 2.49/1.64  Subsumption          : 0.04
% 2.49/1.64  Abstraction          : 0.01
% 2.81/1.64  MUC search           : 0.00
% 2.81/1.64  Cooper               : 0.00
% 2.81/1.64  Total                : 0.76
% 2.81/1.64  Index Insertion      : 0.00
% 2.81/1.64  Index Deletion       : 0.00
% 2.81/1.64  Index Matching       : 0.00
% 2.81/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
