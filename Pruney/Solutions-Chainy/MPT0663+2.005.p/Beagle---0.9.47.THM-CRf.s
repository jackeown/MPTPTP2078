%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:12 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 185 expanded)
%              Number of leaves         :   34 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  128 ( 345 expanded)
%              Number of equality atoms :   38 ( 106 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_89,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [B_60,A_61] : k1_setfam_1(k2_tarski(B_60,A_61)) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_16,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,A_61) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_16])).

tff(c_48,plain,(
    r2_hidden('#skF_2',k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_162,plain,(
    r2_hidden('#skF_2',k3_xboole_0('#skF_3',k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_48])).

tff(c_30,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_38] : v1_funct_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_43] :
      ( k1_relat_1(k6_relat_1(A_43)) = A_43
      | ~ v1_funct_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54,plain,(
    ! [A_43] :
      ( k1_relat_1(k6_relat_1(A_43)) = A_43
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42])).

tff(c_58,plain,(
    ! [A_43] : k1_relat_1(k6_relat_1(A_43)) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_54])).

tff(c_215,plain,(
    ! [A_68,B_69] :
      ( k5_relat_1(k6_relat_1(A_68),B_69) = k7_relat_1(B_69,A_68)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [B_49,A_48] : k5_relat_1(k6_relat_1(B_49),k6_relat_1(A_48)) = k6_relat_1(k3_xboole_0(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_222,plain,(
    ! [A_48,A_68] :
      ( k7_relat_1(k6_relat_1(A_48),A_68) = k6_relat_1(k3_xboole_0(A_48,A_68))
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_44])).

tff(c_231,plain,(
    ! [A_48,A_68] : k7_relat_1(k6_relat_1(A_48),A_68) = k6_relat_1(k3_xboole_0(A_48,A_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_222])).

tff(c_280,plain,(
    ! [A_85,C_86,B_87] :
      ( r2_hidden(A_85,k1_relat_1(C_86))
      | ~ r2_hidden(A_85,k1_relat_1(k7_relat_1(C_86,B_87)))
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_283,plain,(
    ! [A_85,A_48,A_68] :
      ( r2_hidden(A_85,k1_relat_1(k6_relat_1(A_48)))
      | ~ r2_hidden(A_85,k1_relat_1(k6_relat_1(k3_xboole_0(A_48,A_68))))
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_280])).

tff(c_286,plain,(
    ! [A_88,A_89,A_90] :
      ( r2_hidden(A_88,A_89)
      | ~ r2_hidden(A_88,k3_xboole_0(A_89,A_90)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_58,c_58,c_283])).

tff(c_296,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_286])).

tff(c_263,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden(A_79,B_80)
      | ~ r2_hidden(A_79,k1_relat_1(k7_relat_1(C_81,B_80)))
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_266,plain,(
    ! [A_79,A_68,A_48] :
      ( r2_hidden(A_79,A_68)
      | ~ r2_hidden(A_79,k1_relat_1(k6_relat_1(k3_xboole_0(A_48,A_68))))
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_263])).

tff(c_269,plain,(
    ! [A_82,A_83,A_84] :
      ( r2_hidden(A_82,A_83)
      | ~ r2_hidden(A_82,k3_xboole_0(A_84,A_83)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_58,c_266])).

tff(c_279,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_162,c_269])).

tff(c_40,plain,(
    ! [A_43,C_47] :
      ( k1_funct_1(k6_relat_1(A_43),C_47) = C_47
      | ~ r2_hidden(C_47,A_43)
      | ~ v1_funct_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    ! [A_43,C_47] :
      ( k1_funct_1(k6_relat_1(A_43),C_47) = C_47
      | ~ r2_hidden(C_47,A_43)
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_60,plain,(
    ! [A_43,C_47] :
      ( k1_funct_1(k6_relat_1(A_43),C_47) = C_47
      | ~ r2_hidden(C_47,A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_56])).

tff(c_387,plain,(
    ! [B_117,C_118,A_119] :
      ( k1_funct_1(k5_relat_1(B_117,C_118),A_119) = k1_funct_1(C_118,k1_funct_1(B_117,A_119))
      | ~ r2_hidden(A_119,k1_relat_1(B_117))
      | ~ v1_funct_1(C_118)
      | ~ v1_relat_1(C_118)
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_395,plain,(
    ! [A_43,C_118,A_119] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_43),C_118),A_119) = k1_funct_1(C_118,k1_funct_1(k6_relat_1(A_43),A_119))
      | ~ r2_hidden(A_119,A_43)
      | ~ v1_funct_1(C_118)
      | ~ v1_relat_1(C_118)
      | ~ v1_funct_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_387])).

tff(c_412,plain,(
    ! [A_121,C_122,A_123] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_121),C_122),A_123) = k1_funct_1(C_122,k1_funct_1(k6_relat_1(A_121),A_123))
      | ~ r2_hidden(A_123,A_121)
      | ~ v1_funct_1(C_122)
      | ~ v1_relat_1(C_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_395])).

tff(c_428,plain,(
    ! [A_48,B_49,A_123] :
      ( k1_funct_1(k6_relat_1(A_48),k1_funct_1(k6_relat_1(B_49),A_123)) = k1_funct_1(k6_relat_1(k3_xboole_0(A_48,B_49)),A_123)
      | ~ r2_hidden(A_123,B_49)
      | ~ v1_funct_1(k6_relat_1(A_48))
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_412])).

tff(c_433,plain,(
    ! [A_124,B_125,A_126] :
      ( k1_funct_1(k6_relat_1(A_124),k1_funct_1(k6_relat_1(B_125),A_126)) = k1_funct_1(k6_relat_1(k3_xboole_0(A_124,B_125)),A_126)
      | ~ r2_hidden(A_126,B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_428])).

tff(c_458,plain,(
    ! [A_127,A_128,C_129] :
      ( k1_funct_1(k6_relat_1(k3_xboole_0(A_127,A_128)),C_129) = k1_funct_1(k6_relat_1(A_127),C_129)
      | ~ r2_hidden(C_129,A_128)
      | ~ r2_hidden(C_129,A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_433])).

tff(c_497,plain,(
    ! [A_130,C_131,A_132] :
      ( k1_funct_1(k6_relat_1(A_130),C_131) = C_131
      | ~ r2_hidden(C_131,k3_xboole_0(A_130,A_132))
      | ~ r2_hidden(C_131,A_132)
      | ~ r2_hidden(C_131,A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_60])).

tff(c_503,plain,
    ( k1_funct_1(k6_relat_1('#skF_3'),'#skF_2') = '#skF_2'
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_162,c_497])).

tff(c_513,plain,(
    k1_funct_1(k6_relat_1('#skF_3'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_503])).

tff(c_28,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = k7_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1619,plain,(
    ! [B_166,A_167,A_168] :
      ( k1_funct_1(B_166,k1_funct_1(k6_relat_1(A_167),A_168)) = k1_funct_1(k7_relat_1(B_166,A_167),A_168)
      | ~ r2_hidden(A_168,A_167)
      | ~ v1_funct_1(B_166)
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_412])).

tff(c_1746,plain,(
    ! [B_166] :
      ( k1_funct_1(k7_relat_1(B_166,'#skF_3'),'#skF_2') = k1_funct_1(B_166,'#skF_2')
      | ~ r2_hidden('#skF_2','#skF_3')
      | ~ v1_funct_1(B_166)
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_1619])).

tff(c_1819,plain,(
    ! [B_169] :
      ( k1_funct_1(k7_relat_1(B_169,'#skF_3'),'#skF_2') = k1_funct_1(B_169,'#skF_2')
      | ~ v1_funct_1(B_169)
      | ~ v1_relat_1(B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_1746])).

tff(c_46,plain,(
    k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1825,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1819,c_46])).

tff(c_1837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:43:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.67  
% 3.91/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.67  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.91/1.67  
% 3.91/1.67  %Foreground sorts:
% 3.91/1.67  
% 3.91/1.67  
% 3.91/1.67  %Background operators:
% 3.91/1.67  
% 3.91/1.67  
% 3.91/1.67  %Foreground operators:
% 3.91/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.91/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.91/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.91/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.91/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.91/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.91/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.91/1.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.91/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.91/1.67  
% 4.04/1.68  tff(f_98, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 4.04/1.68  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.04/1.68  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.04/1.68  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.04/1.68  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 4.04/1.68  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.04/1.68  tff(f_89, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 4.04/1.68  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 4.04/1.68  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 4.04/1.68  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.04/1.68  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.04/1.68  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/1.68  tff(c_124, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.04/1.68  tff(c_139, plain, (![B_60, A_61]: (k1_setfam_1(k2_tarski(B_60, A_61))=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 4.04/1.68  tff(c_16, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.04/1.68  tff(c_145, plain, (![B_60, A_61]: (k3_xboole_0(B_60, A_61)=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_139, c_16])).
% 4.04/1.68  tff(c_48, plain, (r2_hidden('#skF_2', k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.04/1.68  tff(c_162, plain, (r2_hidden('#skF_2', k3_xboole_0('#skF_3', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_48])).
% 4.04/1.68  tff(c_30, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.04/1.68  tff(c_32, plain, (![A_38]: (v1_funct_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.04/1.68  tff(c_42, plain, (![A_43]: (k1_relat_1(k6_relat_1(A_43))=A_43 | ~v1_funct_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.04/1.68  tff(c_54, plain, (![A_43]: (k1_relat_1(k6_relat_1(A_43))=A_43 | ~v1_relat_1(k6_relat_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42])).
% 4.04/1.68  tff(c_58, plain, (![A_43]: (k1_relat_1(k6_relat_1(A_43))=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_54])).
% 4.04/1.68  tff(c_215, plain, (![A_68, B_69]: (k5_relat_1(k6_relat_1(A_68), B_69)=k7_relat_1(B_69, A_68) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.04/1.68  tff(c_44, plain, (![B_49, A_48]: (k5_relat_1(k6_relat_1(B_49), k6_relat_1(A_48))=k6_relat_1(k3_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.04/1.68  tff(c_222, plain, (![A_48, A_68]: (k7_relat_1(k6_relat_1(A_48), A_68)=k6_relat_1(k3_xboole_0(A_48, A_68)) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_215, c_44])).
% 4.04/1.68  tff(c_231, plain, (![A_48, A_68]: (k7_relat_1(k6_relat_1(A_48), A_68)=k6_relat_1(k3_xboole_0(A_48, A_68)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_222])).
% 4.04/1.68  tff(c_280, plain, (![A_85, C_86, B_87]: (r2_hidden(A_85, k1_relat_1(C_86)) | ~r2_hidden(A_85, k1_relat_1(k7_relat_1(C_86, B_87))) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.04/1.68  tff(c_283, plain, (![A_85, A_48, A_68]: (r2_hidden(A_85, k1_relat_1(k6_relat_1(A_48))) | ~r2_hidden(A_85, k1_relat_1(k6_relat_1(k3_xboole_0(A_48, A_68)))) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_231, c_280])).
% 4.04/1.68  tff(c_286, plain, (![A_88, A_89, A_90]: (r2_hidden(A_88, A_89) | ~r2_hidden(A_88, k3_xboole_0(A_89, A_90)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_58, c_58, c_283])).
% 4.04/1.68  tff(c_296, plain, (r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_162, c_286])).
% 4.04/1.68  tff(c_263, plain, (![A_79, B_80, C_81]: (r2_hidden(A_79, B_80) | ~r2_hidden(A_79, k1_relat_1(k7_relat_1(C_81, B_80))) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.04/1.68  tff(c_266, plain, (![A_79, A_68, A_48]: (r2_hidden(A_79, A_68) | ~r2_hidden(A_79, k1_relat_1(k6_relat_1(k3_xboole_0(A_48, A_68)))) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_231, c_263])).
% 4.04/1.68  tff(c_269, plain, (![A_82, A_83, A_84]: (r2_hidden(A_82, A_83) | ~r2_hidden(A_82, k3_xboole_0(A_84, A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_58, c_266])).
% 4.04/1.68  tff(c_279, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_162, c_269])).
% 4.04/1.68  tff(c_40, plain, (![A_43, C_47]: (k1_funct_1(k6_relat_1(A_43), C_47)=C_47 | ~r2_hidden(C_47, A_43) | ~v1_funct_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.04/1.68  tff(c_56, plain, (![A_43, C_47]: (k1_funct_1(k6_relat_1(A_43), C_47)=C_47 | ~r2_hidden(C_47, A_43) | ~v1_relat_1(k6_relat_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 4.04/1.68  tff(c_60, plain, (![A_43, C_47]: (k1_funct_1(k6_relat_1(A_43), C_47)=C_47 | ~r2_hidden(C_47, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_56])).
% 4.04/1.68  tff(c_387, plain, (![B_117, C_118, A_119]: (k1_funct_1(k5_relat_1(B_117, C_118), A_119)=k1_funct_1(C_118, k1_funct_1(B_117, A_119)) | ~r2_hidden(A_119, k1_relat_1(B_117)) | ~v1_funct_1(C_118) | ~v1_relat_1(C_118) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.04/1.68  tff(c_395, plain, (![A_43, C_118, A_119]: (k1_funct_1(k5_relat_1(k6_relat_1(A_43), C_118), A_119)=k1_funct_1(C_118, k1_funct_1(k6_relat_1(A_43), A_119)) | ~r2_hidden(A_119, A_43) | ~v1_funct_1(C_118) | ~v1_relat_1(C_118) | ~v1_funct_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_387])).
% 4.04/1.68  tff(c_412, plain, (![A_121, C_122, A_123]: (k1_funct_1(k5_relat_1(k6_relat_1(A_121), C_122), A_123)=k1_funct_1(C_122, k1_funct_1(k6_relat_1(A_121), A_123)) | ~r2_hidden(A_123, A_121) | ~v1_funct_1(C_122) | ~v1_relat_1(C_122))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_395])).
% 4.04/1.68  tff(c_428, plain, (![A_48, B_49, A_123]: (k1_funct_1(k6_relat_1(A_48), k1_funct_1(k6_relat_1(B_49), A_123))=k1_funct_1(k6_relat_1(k3_xboole_0(A_48, B_49)), A_123) | ~r2_hidden(A_123, B_49) | ~v1_funct_1(k6_relat_1(A_48)) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_412])).
% 4.04/1.68  tff(c_433, plain, (![A_124, B_125, A_126]: (k1_funct_1(k6_relat_1(A_124), k1_funct_1(k6_relat_1(B_125), A_126))=k1_funct_1(k6_relat_1(k3_xboole_0(A_124, B_125)), A_126) | ~r2_hidden(A_126, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_428])).
% 4.04/1.68  tff(c_458, plain, (![A_127, A_128, C_129]: (k1_funct_1(k6_relat_1(k3_xboole_0(A_127, A_128)), C_129)=k1_funct_1(k6_relat_1(A_127), C_129) | ~r2_hidden(C_129, A_128) | ~r2_hidden(C_129, A_128))), inference(superposition, [status(thm), theory('equality')], [c_60, c_433])).
% 4.04/1.68  tff(c_497, plain, (![A_130, C_131, A_132]: (k1_funct_1(k6_relat_1(A_130), C_131)=C_131 | ~r2_hidden(C_131, k3_xboole_0(A_130, A_132)) | ~r2_hidden(C_131, A_132) | ~r2_hidden(C_131, A_132))), inference(superposition, [status(thm), theory('equality')], [c_458, c_60])).
% 4.04/1.68  tff(c_503, plain, (k1_funct_1(k6_relat_1('#skF_3'), '#skF_2')='#skF_2' | ~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_162, c_497])).
% 4.04/1.68  tff(c_513, plain, (k1_funct_1(k6_relat_1('#skF_3'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_503])).
% 4.04/1.68  tff(c_28, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=k7_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.04/1.68  tff(c_1619, plain, (![B_166, A_167, A_168]: (k1_funct_1(B_166, k1_funct_1(k6_relat_1(A_167), A_168))=k1_funct_1(k7_relat_1(B_166, A_167), A_168) | ~r2_hidden(A_168, A_167) | ~v1_funct_1(B_166) | ~v1_relat_1(B_166) | ~v1_relat_1(B_166))), inference(superposition, [status(thm), theory('equality')], [c_28, c_412])).
% 4.04/1.68  tff(c_1746, plain, (![B_166]: (k1_funct_1(k7_relat_1(B_166, '#skF_3'), '#skF_2')=k1_funct_1(B_166, '#skF_2') | ~r2_hidden('#skF_2', '#skF_3') | ~v1_funct_1(B_166) | ~v1_relat_1(B_166) | ~v1_relat_1(B_166))), inference(superposition, [status(thm), theory('equality')], [c_513, c_1619])).
% 4.04/1.68  tff(c_1819, plain, (![B_169]: (k1_funct_1(k7_relat_1(B_169, '#skF_3'), '#skF_2')=k1_funct_1(B_169, '#skF_2') | ~v1_funct_1(B_169) | ~v1_relat_1(B_169))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_1746])).
% 4.04/1.68  tff(c_46, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.04/1.68  tff(c_1825, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1819, c_46])).
% 4.04/1.68  tff(c_1837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1825])).
% 4.04/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.68  
% 4.04/1.68  Inference rules
% 4.04/1.68  ----------------------
% 4.04/1.68  #Ref     : 0
% 4.04/1.68  #Sup     : 405
% 4.04/1.68  #Fact    : 0
% 4.04/1.68  #Define  : 0
% 4.04/1.68  #Split   : 0
% 4.04/1.68  #Chain   : 0
% 4.04/1.68  #Close   : 0
% 4.04/1.68  
% 4.04/1.68  Ordering : KBO
% 4.04/1.68  
% 4.04/1.68  Simplification rules
% 4.04/1.68  ----------------------
% 4.04/1.68  #Subsume      : 50
% 4.04/1.68  #Demod        : 407
% 4.04/1.68  #Tautology    : 192
% 4.04/1.68  #SimpNegUnit  : 0
% 4.04/1.68  #BackRed      : 1
% 4.04/1.68  
% 4.04/1.68  #Partial instantiations: 0
% 4.04/1.68  #Strategies tried      : 1
% 4.04/1.68  
% 4.04/1.68  Timing (in seconds)
% 4.04/1.68  ----------------------
% 4.04/1.69  Preprocessing        : 0.33
% 4.04/1.69  Parsing              : 0.17
% 4.04/1.69  CNF conversion       : 0.02
% 4.04/1.69  Main loop            : 0.58
% 4.04/1.69  Inferencing          : 0.19
% 4.04/1.69  Reduction            : 0.22
% 4.04/1.69  Demodulation         : 0.18
% 4.04/1.69  BG Simplification    : 0.03
% 4.04/1.69  Subsumption          : 0.10
% 4.04/1.69  Abstraction          : 0.04
% 4.04/1.69  MUC search           : 0.00
% 4.04/1.69  Cooper               : 0.00
% 4.04/1.69  Total                : 0.94
% 4.04/1.69  Index Insertion      : 0.00
% 4.04/1.69  Index Deletion       : 0.00
% 4.04/1.69  Index Matching       : 0.00
% 4.04/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
