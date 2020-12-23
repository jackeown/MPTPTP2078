%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:25 EST 2020

% Result     : Theorem 20.81s
% Output     : CNFRefutation 20.81s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 426 expanded)
%              Number of leaves         :   23 ( 151 expanded)
%              Depth                    :   16
%              Number of atoms          :  199 ( 796 expanded)
%              Number of equality atoms :   80 ( 332 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_40,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_158,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_153,c_52])).

tff(c_161,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_38,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_253,plain,(
    k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_565,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r2_hidden('#skF_1'(A_69,B_70,C_71),C_71)
      | r2_hidden('#skF_2'(A_69,B_70,C_71),C_71)
      | k4_xboole_0(A_69,B_70) = C_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_574,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_565])).

tff(c_863,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden('#skF_1'(A_102,B_103,C_104),A_102)
      | r2_hidden('#skF_2'(A_102,B_103,C_104),B_103)
      | ~ r2_hidden('#skF_2'(A_102,B_103,C_104),A_102)
      | k4_xboole_0(A_102,B_103) = C_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3322,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_2'(A_166,B_167,A_166),B_167)
      | ~ r2_hidden('#skF_2'(A_166,B_167,A_166),A_166)
      | k4_xboole_0(A_166,B_167) = A_166 ) ),
    inference(resolution,[status(thm)],[c_863,c_10])).

tff(c_3341,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),B_4)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_574,c_3322])).

tff(c_32,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_370,plain,(
    ! [D_55,A_56,B_57] :
      ( r2_hidden(D_55,k4_xboole_0(A_56,B_57))
      | r2_hidden(D_55,B_57)
      | ~ r2_hidden(D_55,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3004,plain,(
    ! [D_158,A_159,B_160] :
      ( r2_hidden(D_158,k3_xboole_0(A_159,B_160))
      | r2_hidden(D_158,k4_xboole_0(A_159,B_160))
      | ~ r2_hidden(D_158,A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_370])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9208,plain,(
    ! [D_274,B_275,A_276] :
      ( ~ r2_hidden(D_274,B_275)
      | r2_hidden(D_274,k3_xboole_0(A_276,B_275))
      | ~ r2_hidden(D_274,A_276) ) ),
    inference(resolution,[status(thm)],[c_3004,c_6])).

tff(c_680,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r2_hidden('#skF_1'(A_78,B_79,C_80),B_79)
      | r2_hidden('#skF_2'(A_78,B_79,C_80),C_80)
      | k4_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1280,plain,(
    ! [A_115,C_116] :
      ( r2_hidden('#skF_2'(A_115,A_115,C_116),C_116)
      | k4_xboole_0(A_115,A_115) = C_116 ) ),
    inference(resolution,[status(thm)],[c_20,c_680])).

tff(c_28,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_270,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k4_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_779,plain,(
    ! [D_93,A_94,B_95] :
      ( r2_hidden(D_93,A_94)
      | ~ r2_hidden(D_93,k3_xboole_0(A_94,B_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_8])).

tff(c_811,plain,(
    ! [D_93,A_13] :
      ( r2_hidden(D_93,A_13)
      | ~ r2_hidden(D_93,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_779])).

tff(c_1301,plain,(
    ! [A_115,A_13] :
      ( r2_hidden('#skF_2'(A_115,A_115,k1_xboole_0),A_13)
      | k4_xboole_0(A_115,A_115) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1280,c_811])).

tff(c_5789,plain,(
    ! [A_218,A_219] :
      ( r2_hidden('#skF_2'(A_218,A_218,k1_xboole_0),A_219)
      | k4_xboole_0(A_218,A_218) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1280,c_811])).

tff(c_62,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    ! [A_30] : k3_xboole_0(k1_xboole_0,A_30) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_28])).

tff(c_1539,plain,(
    ! [A_123,B_124] : k4_xboole_0(A_123,k3_xboole_0(A_123,B_124)) = k3_xboole_0(A_123,k4_xboole_0(A_123,B_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_32])).

tff(c_1646,plain,(
    ! [A_30] : k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,A_30)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1539])).

tff(c_1666,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1646])).

tff(c_1731,plain,(
    ! [D_8] :
      ( ~ r2_hidden(D_8,k1_xboole_0)
      | ~ r2_hidden(D_8,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1666,c_6])).

tff(c_6051,plain,(
    ! [A_225] :
      ( ~ r2_hidden('#skF_2'(A_225,A_225,k1_xboole_0),k1_xboole_0)
      | k4_xboole_0(A_225,A_225) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5789,c_1731])).

tff(c_6100,plain,(
    ! [A_226] : k4_xboole_0(A_226,A_226) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1301,c_6051])).

tff(c_6288,plain,(
    ! [A_226] : k4_xboole_0(A_226,k1_xboole_0) = k3_xboole_0(A_226,A_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_6100,c_32])).

tff(c_42,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_142,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_142,c_26])).

tff(c_162,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_179,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_162])).

tff(c_1640,plain,(
    k3_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_5')) = k4_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_1539])).

tff(c_808,plain,(
    ! [D_93,B_2,A_1] :
      ( r2_hidden(D_93,B_2)
      | ~ r2_hidden(D_93,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_779])).

tff(c_2029,plain,(
    ! [D_93] :
      ( r2_hidden(D_93,k4_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(D_93,k4_xboole_0('#skF_6',k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1640,c_808])).

tff(c_8639,plain,(
    ! [D_269] :
      ( r2_hidden(D_269,k4_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(D_269,k3_xboole_0('#skF_6','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6288,c_2029])).

tff(c_8704,plain,(
    ! [D_269] :
      ( ~ r2_hidden(D_269,'#skF_5')
      | ~ r2_hidden(D_269,k3_xboole_0('#skF_6','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_8639,c_6])).

tff(c_9452,plain,(
    ! [D_280] :
      ( ~ r2_hidden(D_280,'#skF_5')
      | ~ r2_hidden(D_280,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_9208,c_8704])).

tff(c_13398,plain,(
    ! [B_349] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_349,'#skF_5'),'#skF_6')
      | k4_xboole_0('#skF_5',B_349) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_574,c_9452])).

tff(c_13404,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3341,c_13398])).

tff(c_13410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_253,c_13404])).

tff(c_13411,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ! [B_19,A_18] : r1_xboole_0(B_19,k4_xboole_0(A_18,B_19)) ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_181,plain,(
    ! [B_19,A_18] : k3_xboole_0(B_19,k4_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_162])).

tff(c_13416,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13411,c_181])).

tff(c_13435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_13416])).

tff(c_13436,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_13447,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13436,c_34])).

tff(c_13451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_13447])).

tff(c_13453,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_36,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_13566,plain,(
    k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13453,c_36])).

tff(c_13982,plain,(
    ! [A_390,B_391,C_392] :
      ( ~ r2_hidden('#skF_1'(A_390,B_391,C_392),C_392)
      | r2_hidden('#skF_2'(A_390,B_391,C_392),C_392)
      | k4_xboole_0(A_390,B_391) = C_392 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13991,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_13982])).

tff(c_14287,plain,(
    ! [A_418,B_419,C_420] :
      ( r2_hidden('#skF_1'(A_418,B_419,C_420),A_418)
      | r2_hidden('#skF_2'(A_418,B_419,C_420),B_419)
      | ~ r2_hidden('#skF_2'(A_418,B_419,C_420),A_418)
      | k4_xboole_0(A_418,B_419) = C_420 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16616,plain,(
    ! [A_481,B_482] :
      ( r2_hidden('#skF_2'(A_481,B_482,A_481),B_482)
      | ~ r2_hidden('#skF_2'(A_481,B_482,A_481),A_481)
      | k4_xboole_0(A_481,B_482) = A_481 ) ),
    inference(resolution,[status(thm)],[c_14287,c_10])).

tff(c_16634,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),B_4)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_13991,c_16616])).

tff(c_18191,plain,(
    ! [A_518,B_519] :
      ( r2_hidden('#skF_2'(A_518,B_519,A_518),B_519)
      | k4_xboole_0(A_518,B_519) = A_518 ) ),
    inference(resolution,[status(thm)],[c_13991,c_16616])).

tff(c_13776,plain,(
    ! [D_373,A_374,B_375] :
      ( r2_hidden(D_373,A_374)
      | ~ r2_hidden(D_373,k4_xboole_0(A_374,B_375)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14328,plain,(
    ! [D_421,A_422,B_423] :
      ( r2_hidden(D_421,A_422)
      | ~ r2_hidden(D_421,k3_xboole_0(A_422,B_423)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_13776])).

tff(c_14374,plain,(
    ! [D_421,A_13] :
      ( r2_hidden(D_421,A_13)
      | ~ r2_hidden(D_421,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14328])).

tff(c_18235,plain,(
    ! [A_518,A_13] :
      ( r2_hidden('#skF_2'(A_518,k1_xboole_0,A_518),A_13)
      | k4_xboole_0(A_518,k1_xboole_0) = A_518 ) ),
    inference(resolution,[status(thm)],[c_18191,c_14374])).

tff(c_20185,plain,(
    ! [A_552,A_553] :
      ( r2_hidden('#skF_2'(A_552,k1_xboole_0,A_552),A_553)
      | k4_xboole_0(A_552,k1_xboole_0) = A_552 ) ),
    inference(resolution,[status(thm)],[c_18191,c_14374])).

tff(c_13454,plain,(
    ! [B_350,A_351] : k3_xboole_0(B_350,A_351) = k3_xboole_0(A_351,B_350) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_13470,plain,(
    ! [A_351] : k3_xboole_0(k1_xboole_0,A_351) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13454,c_28])).

tff(c_13674,plain,(
    ! [A_366,B_367] : k4_xboole_0(A_366,k4_xboole_0(A_366,B_367)) = k3_xboole_0(A_366,B_367) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_15105,plain,(
    ! [A_450,B_451] : k4_xboole_0(A_450,k3_xboole_0(A_450,B_451)) = k3_xboole_0(A_450,k4_xboole_0(A_450,B_451)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13674,c_32])).

tff(c_15218,plain,(
    ! [A_351] : k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,A_351)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13470,c_15105])).

tff(c_15237,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13470,c_15218])).

tff(c_13686,plain,(
    ! [D_8,A_366,B_367] :
      ( ~ r2_hidden(D_8,k4_xboole_0(A_366,B_367))
      | ~ r2_hidden(D_8,k3_xboole_0(A_366,B_367)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13674,c_6])).

tff(c_15253,plain,(
    ! [D_8] :
      ( ~ r2_hidden(D_8,k1_xboole_0)
      | ~ r2_hidden(D_8,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15237,c_13686])).

tff(c_15315,plain,(
    ! [D_8] :
      ( ~ r2_hidden(D_8,k1_xboole_0)
      | ~ r2_hidden(D_8,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_15253])).

tff(c_63867,plain,(
    ! [A_1027] :
      ( ~ r2_hidden('#skF_2'(A_1027,k1_xboole_0,A_1027),k1_xboole_0)
      | k4_xboole_0(A_1027,k1_xboole_0) = A_1027 ) ),
    inference(resolution,[status(thm)],[c_20185,c_15315])).

tff(c_63893,plain,(
    ! [A_518] : k4_xboole_0(A_518,k1_xboole_0) = A_518 ),
    inference(resolution,[status(thm)],[c_18235,c_63867])).

tff(c_15227,plain,(
    ! [A_13] : k3_xboole_0(A_13,k4_xboole_0(A_13,k1_xboole_0)) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_15105])).

tff(c_63915,plain,(
    ! [A_13] : k3_xboole_0(A_13,A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63893,c_63893,c_15227])).

tff(c_14061,plain,(
    ! [A_395,B_396,C_397] :
      ( ~ r2_hidden('#skF_1'(A_395,B_396,C_397),B_396)
      | r2_hidden('#skF_2'(A_395,B_396,C_397),C_397)
      | k4_xboole_0(A_395,B_396) = C_397 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_15544,plain,(
    ! [A_455,C_456] :
      ( r2_hidden('#skF_2'(A_455,A_455,C_456),C_456)
      | k4_xboole_0(A_455,A_455) = C_456 ) ),
    inference(resolution,[status(thm)],[c_20,c_14061])).

tff(c_15574,plain,(
    ! [A_455,A_13] :
      ( r2_hidden('#skF_2'(A_455,A_455,k1_xboole_0),A_13)
      | k4_xboole_0(A_455,A_455) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_15544,c_14374])).

tff(c_19235,plain,(
    ! [A_532,A_533] :
      ( r2_hidden('#skF_2'(A_532,A_532,k1_xboole_0),A_533)
      | k4_xboole_0(A_532,A_532) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_15544,c_14374])).

tff(c_20598,plain,(
    ! [A_559] :
      ( ~ r2_hidden('#skF_2'(A_559,A_559,k1_xboole_0),k1_xboole_0)
      | k4_xboole_0(A_559,A_559) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_19235,c_15315])).

tff(c_20649,plain,(
    ! [A_560] : k4_xboole_0(A_560,A_560) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15574,c_20598])).

tff(c_20853,plain,(
    ! [A_560] : k4_xboole_0(A_560,k1_xboole_0) = k3_xboole_0(A_560,A_560) ),
    inference(superposition,[status(thm),theory(equality)],[c_20649,c_32])).

tff(c_13452,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_13567,plain,(
    ! [A_359,B_360] :
      ( k3_xboole_0(A_359,B_360) = k1_xboole_0
      | ~ r1_xboole_0(A_359,B_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13594,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13452,c_13567])).

tff(c_13625,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13594])).

tff(c_15206,plain,(
    k3_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_5')) = k4_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13625,c_15105])).

tff(c_21125,plain,(
    k3_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_5')) = k3_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20853,c_15206])).

tff(c_64183,plain,(
    k3_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63915,c_21125])).

tff(c_14371,plain,(
    ! [D_421,B_2,A_1] :
      ( r2_hidden(D_421,B_2)
      | ~ r2_hidden(D_421,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14328])).

tff(c_65592,plain,(
    ! [D_1042] :
      ( r2_hidden(D_1042,k4_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(D_1042,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64183,c_14371])).

tff(c_65767,plain,(
    ! [D_1046] :
      ( ~ r2_hidden(D_1046,'#skF_5')
      | ~ r2_hidden(D_1046,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_65592,c_6])).

tff(c_75663,plain,(
    ! [B_1138] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_1138,'#skF_5'),'#skF_6')
      | k4_xboole_0('#skF_5',B_1138) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_13991,c_65767])).

tff(c_75669,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16634,c_75663])).

tff(c_75675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13566,c_13566,c_75669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.81/11.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.81/11.32  
% 20.81/11.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.81/11.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 20.81/11.32  
% 20.81/11.32  %Foreground sorts:
% 20.81/11.32  
% 20.81/11.32  
% 20.81/11.32  %Background operators:
% 20.81/11.32  
% 20.81/11.32  
% 20.81/11.32  %Foreground operators:
% 20.81/11.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 20.81/11.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.81/11.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.81/11.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.81/11.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.81/11.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.81/11.32  tff('#skF_5', type, '#skF_5': $i).
% 20.81/11.32  tff('#skF_6', type, '#skF_6': $i).
% 20.81/11.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 20.81/11.32  tff('#skF_3', type, '#skF_3': $i).
% 20.81/11.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.81/11.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.81/11.32  tff('#skF_4', type, '#skF_4': $i).
% 20.81/11.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.81/11.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.81/11.32  
% 20.81/11.34  tff(f_58, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 20.81/11.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 20.81/11.34  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 20.81/11.34  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 20.81/11.34  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 20.81/11.34  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 20.81/11.34  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 20.81/11.34  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 20.81/11.34  tff(c_40, plain, (~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.81/11.34  tff(c_52, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 20.81/11.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.81/11.34  tff(c_153, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k3_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.81/11.34  tff(c_158, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_153, c_52])).
% 20.81/11.34  tff(c_161, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_158])).
% 20.81/11.34  tff(c_38, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.81/11.34  tff(c_253, plain, (k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(splitLeft, [status(thm)], [c_38])).
% 20.81/11.34  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_565, plain, (![A_69, B_70, C_71]: (~r2_hidden('#skF_1'(A_69, B_70, C_71), C_71) | r2_hidden('#skF_2'(A_69, B_70, C_71), C_71) | k4_xboole_0(A_69, B_70)=C_71)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_574, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_565])).
% 20.81/11.34  tff(c_863, plain, (![A_102, B_103, C_104]: (r2_hidden('#skF_1'(A_102, B_103, C_104), A_102) | r2_hidden('#skF_2'(A_102, B_103, C_104), B_103) | ~r2_hidden('#skF_2'(A_102, B_103, C_104), A_102) | k4_xboole_0(A_102, B_103)=C_104)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_3322, plain, (![A_166, B_167]: (r2_hidden('#skF_2'(A_166, B_167, A_166), B_167) | ~r2_hidden('#skF_2'(A_166, B_167, A_166), A_166) | k4_xboole_0(A_166, B_167)=A_166)), inference(resolution, [status(thm)], [c_863, c_10])).
% 20.81/11.34  tff(c_3341, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), B_4) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_574, c_3322])).
% 20.81/11.34  tff(c_32, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.81/11.34  tff(c_370, plain, (![D_55, A_56, B_57]: (r2_hidden(D_55, k4_xboole_0(A_56, B_57)) | r2_hidden(D_55, B_57) | ~r2_hidden(D_55, A_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_3004, plain, (![D_158, A_159, B_160]: (r2_hidden(D_158, k3_xboole_0(A_159, B_160)) | r2_hidden(D_158, k4_xboole_0(A_159, B_160)) | ~r2_hidden(D_158, A_159))), inference(superposition, [status(thm), theory('equality')], [c_32, c_370])).
% 20.81/11.34  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_9208, plain, (![D_274, B_275, A_276]: (~r2_hidden(D_274, B_275) | r2_hidden(D_274, k3_xboole_0(A_276, B_275)) | ~r2_hidden(D_274, A_276))), inference(resolution, [status(thm)], [c_3004, c_6])).
% 20.81/11.34  tff(c_680, plain, (![A_78, B_79, C_80]: (~r2_hidden('#skF_1'(A_78, B_79, C_80), B_79) | r2_hidden('#skF_2'(A_78, B_79, C_80), C_80) | k4_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_1280, plain, (![A_115, C_116]: (r2_hidden('#skF_2'(A_115, A_115, C_116), C_116) | k4_xboole_0(A_115, A_115)=C_116)), inference(resolution, [status(thm)], [c_20, c_680])).
% 20.81/11.34  tff(c_28, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.81/11.34  tff(c_270, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k4_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.81/11.34  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_779, plain, (![D_93, A_94, B_95]: (r2_hidden(D_93, A_94) | ~r2_hidden(D_93, k3_xboole_0(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_8])).
% 20.81/11.34  tff(c_811, plain, (![D_93, A_13]: (r2_hidden(D_93, A_13) | ~r2_hidden(D_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_779])).
% 20.81/11.34  tff(c_1301, plain, (![A_115, A_13]: (r2_hidden('#skF_2'(A_115, A_115, k1_xboole_0), A_13) | k4_xboole_0(A_115, A_115)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1280, c_811])).
% 20.81/11.34  tff(c_5789, plain, (![A_218, A_219]: (r2_hidden('#skF_2'(A_218, A_218, k1_xboole_0), A_219) | k4_xboole_0(A_218, A_218)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1280, c_811])).
% 20.81/11.34  tff(c_62, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.81/11.34  tff(c_78, plain, (![A_30]: (k3_xboole_0(k1_xboole_0, A_30)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_28])).
% 20.81/11.34  tff(c_1539, plain, (![A_123, B_124]: (k4_xboole_0(A_123, k3_xboole_0(A_123, B_124))=k3_xboole_0(A_123, k4_xboole_0(A_123, B_124)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_32])).
% 20.81/11.34  tff(c_1646, plain, (![A_30]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, A_30))=k4_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1539])).
% 20.81/11.34  tff(c_1666, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1646])).
% 20.81/11.34  tff(c_1731, plain, (![D_8]: (~r2_hidden(D_8, k1_xboole_0) | ~r2_hidden(D_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1666, c_6])).
% 20.81/11.34  tff(c_6051, plain, (![A_225]: (~r2_hidden('#skF_2'(A_225, A_225, k1_xboole_0), k1_xboole_0) | k4_xboole_0(A_225, A_225)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5789, c_1731])).
% 20.81/11.34  tff(c_6100, plain, (![A_226]: (k4_xboole_0(A_226, A_226)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1301, c_6051])).
% 20.81/11.34  tff(c_6288, plain, (![A_226]: (k4_xboole_0(A_226, k1_xboole_0)=k3_xboole_0(A_226, A_226))), inference(superposition, [status(thm), theory('equality')], [c_6100, c_32])).
% 20.81/11.34  tff(c_42, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.81/11.34  tff(c_142, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_42])).
% 20.81/11.34  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.81/11.34  tff(c_145, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_142, c_26])).
% 20.81/11.34  tff(c_162, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.81/11.34  tff(c_179, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_145, c_162])).
% 20.81/11.34  tff(c_1640, plain, (k3_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_5'))=k4_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_179, c_1539])).
% 20.81/11.34  tff(c_808, plain, (![D_93, B_2, A_1]: (r2_hidden(D_93, B_2) | ~r2_hidden(D_93, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_779])).
% 20.81/11.34  tff(c_2029, plain, (![D_93]: (r2_hidden(D_93, k4_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(D_93, k4_xboole_0('#skF_6', k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1640, c_808])).
% 20.81/11.34  tff(c_8639, plain, (![D_269]: (r2_hidden(D_269, k4_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(D_269, k3_xboole_0('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6288, c_2029])).
% 20.81/11.34  tff(c_8704, plain, (![D_269]: (~r2_hidden(D_269, '#skF_5') | ~r2_hidden(D_269, k3_xboole_0('#skF_6', '#skF_6')))), inference(resolution, [status(thm)], [c_8639, c_6])).
% 20.81/11.34  tff(c_9452, plain, (![D_280]: (~r2_hidden(D_280, '#skF_5') | ~r2_hidden(D_280, '#skF_6'))), inference(resolution, [status(thm)], [c_9208, c_8704])).
% 20.81/11.34  tff(c_13398, plain, (![B_349]: (~r2_hidden('#skF_2'('#skF_5', B_349, '#skF_5'), '#skF_6') | k4_xboole_0('#skF_5', B_349)='#skF_5')), inference(resolution, [status(thm)], [c_574, c_9452])).
% 20.81/11.34  tff(c_13404, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_3341, c_13398])).
% 20.81/11.34  tff(c_13410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_253, c_13404])).
% 20.81/11.34  tff(c_13411, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 20.81/11.34  tff(c_34, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.81/11.34  tff(c_53, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.81/11.34  tff(c_56, plain, (![B_19, A_18]: (r1_xboole_0(B_19, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_34, c_53])).
% 20.81/11.34  tff(c_181, plain, (![B_19, A_18]: (k3_xboole_0(B_19, k4_xboole_0(A_18, B_19))=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_162])).
% 20.81/11.34  tff(c_13416, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13411, c_181])).
% 20.81/11.34  tff(c_13435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_13416])).
% 20.81/11.34  tff(c_13436, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 20.81/11.34  tff(c_13447, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13436, c_34])).
% 20.81/11.34  tff(c_13451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_13447])).
% 20.81/11.34  tff(c_13453, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 20.81/11.34  tff(c_36, plain, (~r1_xboole_0('#skF_3', '#skF_4') | k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.81/11.34  tff(c_13566, plain, (k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13453, c_36])).
% 20.81/11.34  tff(c_13982, plain, (![A_390, B_391, C_392]: (~r2_hidden('#skF_1'(A_390, B_391, C_392), C_392) | r2_hidden('#skF_2'(A_390, B_391, C_392), C_392) | k4_xboole_0(A_390, B_391)=C_392)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_13991, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_13982])).
% 20.81/11.34  tff(c_14287, plain, (![A_418, B_419, C_420]: (r2_hidden('#skF_1'(A_418, B_419, C_420), A_418) | r2_hidden('#skF_2'(A_418, B_419, C_420), B_419) | ~r2_hidden('#skF_2'(A_418, B_419, C_420), A_418) | k4_xboole_0(A_418, B_419)=C_420)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_16616, plain, (![A_481, B_482]: (r2_hidden('#skF_2'(A_481, B_482, A_481), B_482) | ~r2_hidden('#skF_2'(A_481, B_482, A_481), A_481) | k4_xboole_0(A_481, B_482)=A_481)), inference(resolution, [status(thm)], [c_14287, c_10])).
% 20.81/11.34  tff(c_16634, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), B_4) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_13991, c_16616])).
% 20.81/11.34  tff(c_18191, plain, (![A_518, B_519]: (r2_hidden('#skF_2'(A_518, B_519, A_518), B_519) | k4_xboole_0(A_518, B_519)=A_518)), inference(resolution, [status(thm)], [c_13991, c_16616])).
% 20.81/11.34  tff(c_13776, plain, (![D_373, A_374, B_375]: (r2_hidden(D_373, A_374) | ~r2_hidden(D_373, k4_xboole_0(A_374, B_375)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_14328, plain, (![D_421, A_422, B_423]: (r2_hidden(D_421, A_422) | ~r2_hidden(D_421, k3_xboole_0(A_422, B_423)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_13776])).
% 20.81/11.34  tff(c_14374, plain, (![D_421, A_13]: (r2_hidden(D_421, A_13) | ~r2_hidden(D_421, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_14328])).
% 20.81/11.34  tff(c_18235, plain, (![A_518, A_13]: (r2_hidden('#skF_2'(A_518, k1_xboole_0, A_518), A_13) | k4_xboole_0(A_518, k1_xboole_0)=A_518)), inference(resolution, [status(thm)], [c_18191, c_14374])).
% 20.81/11.34  tff(c_20185, plain, (![A_552, A_553]: (r2_hidden('#skF_2'(A_552, k1_xboole_0, A_552), A_553) | k4_xboole_0(A_552, k1_xboole_0)=A_552)), inference(resolution, [status(thm)], [c_18191, c_14374])).
% 20.81/11.34  tff(c_13454, plain, (![B_350, A_351]: (k3_xboole_0(B_350, A_351)=k3_xboole_0(A_351, B_350))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.81/11.34  tff(c_13470, plain, (![A_351]: (k3_xboole_0(k1_xboole_0, A_351)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13454, c_28])).
% 20.81/11.34  tff(c_13674, plain, (![A_366, B_367]: (k4_xboole_0(A_366, k4_xboole_0(A_366, B_367))=k3_xboole_0(A_366, B_367))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.81/11.34  tff(c_15105, plain, (![A_450, B_451]: (k4_xboole_0(A_450, k3_xboole_0(A_450, B_451))=k3_xboole_0(A_450, k4_xboole_0(A_450, B_451)))), inference(superposition, [status(thm), theory('equality')], [c_13674, c_32])).
% 20.81/11.34  tff(c_15218, plain, (![A_351]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, A_351))=k4_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13470, c_15105])).
% 20.81/11.34  tff(c_15237, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13470, c_15218])).
% 20.81/11.34  tff(c_13686, plain, (![D_8, A_366, B_367]: (~r2_hidden(D_8, k4_xboole_0(A_366, B_367)) | ~r2_hidden(D_8, k3_xboole_0(A_366, B_367)))), inference(superposition, [status(thm), theory('equality')], [c_13674, c_6])).
% 20.81/11.34  tff(c_15253, plain, (![D_8]: (~r2_hidden(D_8, k1_xboole_0) | ~r2_hidden(D_8, k3_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_15237, c_13686])).
% 20.81/11.34  tff(c_15315, plain, (![D_8]: (~r2_hidden(D_8, k1_xboole_0) | ~r2_hidden(D_8, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_15253])).
% 20.81/11.34  tff(c_63867, plain, (![A_1027]: (~r2_hidden('#skF_2'(A_1027, k1_xboole_0, A_1027), k1_xboole_0) | k4_xboole_0(A_1027, k1_xboole_0)=A_1027)), inference(resolution, [status(thm)], [c_20185, c_15315])).
% 20.81/11.34  tff(c_63893, plain, (![A_518]: (k4_xboole_0(A_518, k1_xboole_0)=A_518)), inference(resolution, [status(thm)], [c_18235, c_63867])).
% 20.81/11.34  tff(c_15227, plain, (![A_13]: (k3_xboole_0(A_13, k4_xboole_0(A_13, k1_xboole_0))=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_15105])).
% 20.81/11.34  tff(c_63915, plain, (![A_13]: (k3_xboole_0(A_13, A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_63893, c_63893, c_15227])).
% 20.81/11.34  tff(c_14061, plain, (![A_395, B_396, C_397]: (~r2_hidden('#skF_1'(A_395, B_396, C_397), B_396) | r2_hidden('#skF_2'(A_395, B_396, C_397), C_397) | k4_xboole_0(A_395, B_396)=C_397)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/11.34  tff(c_15544, plain, (![A_455, C_456]: (r2_hidden('#skF_2'(A_455, A_455, C_456), C_456) | k4_xboole_0(A_455, A_455)=C_456)), inference(resolution, [status(thm)], [c_20, c_14061])).
% 20.81/11.34  tff(c_15574, plain, (![A_455, A_13]: (r2_hidden('#skF_2'(A_455, A_455, k1_xboole_0), A_13) | k4_xboole_0(A_455, A_455)=k1_xboole_0)), inference(resolution, [status(thm)], [c_15544, c_14374])).
% 20.81/11.34  tff(c_19235, plain, (![A_532, A_533]: (r2_hidden('#skF_2'(A_532, A_532, k1_xboole_0), A_533) | k4_xboole_0(A_532, A_532)=k1_xboole_0)), inference(resolution, [status(thm)], [c_15544, c_14374])).
% 20.81/11.34  tff(c_20598, plain, (![A_559]: (~r2_hidden('#skF_2'(A_559, A_559, k1_xboole_0), k1_xboole_0) | k4_xboole_0(A_559, A_559)=k1_xboole_0)), inference(resolution, [status(thm)], [c_19235, c_15315])).
% 20.81/11.34  tff(c_20649, plain, (![A_560]: (k4_xboole_0(A_560, A_560)=k1_xboole_0)), inference(resolution, [status(thm)], [c_15574, c_20598])).
% 20.81/11.34  tff(c_20853, plain, (![A_560]: (k4_xboole_0(A_560, k1_xboole_0)=k3_xboole_0(A_560, A_560))), inference(superposition, [status(thm), theory('equality')], [c_20649, c_32])).
% 20.81/11.34  tff(c_13452, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 20.81/11.34  tff(c_13567, plain, (![A_359, B_360]: (k3_xboole_0(A_359, B_360)=k1_xboole_0 | ~r1_xboole_0(A_359, B_360))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.81/11.34  tff(c_13594, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_13452, c_13567])).
% 20.81/11.34  tff(c_13625, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_13594])).
% 20.81/11.34  tff(c_15206, plain, (k3_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_5'))=k4_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13625, c_15105])).
% 20.81/11.34  tff(c_21125, plain, (k3_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_5'))=k3_xboole_0('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20853, c_15206])).
% 20.81/11.34  tff(c_64183, plain, (k3_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_63915, c_21125])).
% 20.81/11.34  tff(c_14371, plain, (![D_421, B_2, A_1]: (r2_hidden(D_421, B_2) | ~r2_hidden(D_421, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14328])).
% 20.81/11.34  tff(c_65592, plain, (![D_1042]: (r2_hidden(D_1042, k4_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(D_1042, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_64183, c_14371])).
% 20.81/11.34  tff(c_65767, plain, (![D_1046]: (~r2_hidden(D_1046, '#skF_5') | ~r2_hidden(D_1046, '#skF_6'))), inference(resolution, [status(thm)], [c_65592, c_6])).
% 20.81/11.34  tff(c_75663, plain, (![B_1138]: (~r2_hidden('#skF_2'('#skF_5', B_1138, '#skF_5'), '#skF_6') | k4_xboole_0('#skF_5', B_1138)='#skF_5')), inference(resolution, [status(thm)], [c_13991, c_65767])).
% 20.81/11.34  tff(c_75669, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_16634, c_75663])).
% 20.81/11.34  tff(c_75675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13566, c_13566, c_75669])).
% 20.81/11.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.81/11.34  
% 20.81/11.34  Inference rules
% 20.81/11.34  ----------------------
% 20.81/11.34  #Ref     : 0
% 20.81/11.34  #Sup     : 18770
% 20.81/11.34  #Fact    : 0
% 20.81/11.34  #Define  : 0
% 20.81/11.34  #Split   : 15
% 20.81/11.34  #Chain   : 0
% 20.81/11.34  #Close   : 0
% 20.81/11.34  
% 20.81/11.34  Ordering : KBO
% 20.81/11.34  
% 20.81/11.34  Simplification rules
% 20.81/11.34  ----------------------
% 20.81/11.34  #Subsume      : 3507
% 20.81/11.34  #Demod        : 34114
% 20.81/11.34  #Tautology    : 9324
% 20.81/11.34  #SimpNegUnit  : 19
% 20.81/11.34  #BackRed      : 286
% 20.81/11.34  
% 20.81/11.34  #Partial instantiations: 0
% 20.81/11.34  #Strategies tried      : 1
% 20.81/11.34  
% 20.81/11.34  Timing (in seconds)
% 20.81/11.34  ----------------------
% 20.81/11.34  Preprocessing        : 0.27
% 20.81/11.34  Parsing              : 0.14
% 20.81/11.34  CNF conversion       : 0.02
% 20.81/11.35  Main loop            : 10.22
% 20.81/11.35  Inferencing          : 1.62
% 20.81/11.35  Reduction            : 5.58
% 20.81/11.35  Demodulation         : 4.95
% 20.81/11.35  BG Simplification    : 0.19
% 20.81/11.35  Subsumption          : 2.21
% 20.81/11.35  Abstraction          : 0.34
% 20.81/11.35  MUC search           : 0.00
% 20.81/11.35  Cooper               : 0.00
% 20.81/11.35  Total                : 10.55
% 20.81/11.35  Index Insertion      : 0.00
% 20.81/11.35  Index Deletion       : 0.00
% 20.81/11.35  Index Matching       : 0.00
% 20.81/11.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
