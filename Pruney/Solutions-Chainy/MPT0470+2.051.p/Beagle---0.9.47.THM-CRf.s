%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:08 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 115 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 190 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_103,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_78,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_33] :
      ( v1_relat_1(A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k5_relat_1(A_20,B_21))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_191,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_65,B_66)),k1_relat_1(A_65))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_194,plain,(
    ! [B_66] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_66)),k1_xboole_0)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_191])).

tff(c_232,plain,(
    ! [B_74] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_74)),k1_xboole_0)
      | ~ v1_relat_1(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_194])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_xboole_0(A_56,k4_xboole_0(C_57,B_58))
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_170,plain,(
    ! [A_61,A_62] :
      ( r1_xboole_0(A_61,A_62)
      | ~ r1_tarski(A_61,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_136])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_116,plain,(
    ! [A_46,B_47] :
      ( ~ r1_xboole_0(A_46,B_47)
      | v1_xboole_0(k3_xboole_0(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_4,c_106])).

tff(c_125,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_116])).

tff(c_187,plain,(
    ! [A_62] :
      ( v1_xboole_0(A_62)
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_170,c_125])).

tff(c_250,plain,(
    ! [B_77] :
      ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_77)))
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_232,c_187])).

tff(c_26,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(k1_relat_1(A_22))
      | ~ v1_relat_1(A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_860,plain,(
    ! [B_121] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_121))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_121))
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_250,c_26])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_869,plain,(
    ! [B_122] :
      ( k5_relat_1(k1_xboole_0,B_122) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_122))
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_860,c_10])).

tff(c_873,plain,(
    ! [B_21] :
      ( k5_relat_1(k1_xboole_0,B_21) = k1_xboole_0
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_869])).

tff(c_885,plain,(
    ! [B_124] :
      ( k5_relat_1(k1_xboole_0,B_124) = k1_xboole_0
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_873])).

tff(c_903,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_885])).

tff(c_912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_903])).

tff(c_913,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1203,plain,(
    ! [A_171,B_172] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_171,B_172)),k2_relat_1(B_172))
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1209,plain,(
    ! [A_171] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_171,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1203])).

tff(c_1275,plain,(
    ! [A_175] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_175,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1209])).

tff(c_946,plain,(
    ! [A_132,C_133,B_134] :
      ( r1_xboole_0(A_132,k4_xboole_0(C_133,B_134))
      | ~ r1_tarski(A_132,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_949,plain,(
    ! [A_132,A_13] :
      ( r1_xboole_0(A_132,A_13)
      | ~ r1_tarski(A_132,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_946])).

tff(c_950,plain,(
    ! [A_135,B_136,C_137] :
      ( ~ r1_xboole_0(A_135,B_136)
      | ~ r2_hidden(C_137,k3_xboole_0(A_135,B_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_960,plain,(
    ! [A_140,C_141] :
      ( ~ r1_xboole_0(A_140,A_140)
      | ~ r2_hidden(C_141,A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_950])).

tff(c_969,plain,(
    ! [C_142,A_143] :
      ( ~ r2_hidden(C_142,A_143)
      | ~ r1_tarski(A_143,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_949,c_960])).

tff(c_973,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,k1_xboole_0)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_969])).

tff(c_1287,plain,(
    ! [A_176] :
      ( v1_xboole_0(k2_relat_1(k5_relat_1(A_176,k1_xboole_0)))
      | ~ v1_relat_1(A_176) ) ),
    inference(resolution,[status(thm)],[c_1275,c_973])).

tff(c_28,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(k2_relat_1(A_23))
      | ~ v1_relat_1(A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1730,plain,(
    ! [A_211] :
      ( ~ v1_relat_1(k5_relat_1(A_211,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_211,k1_xboole_0))
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_1287,c_28])).

tff(c_1753,plain,(
    ! [A_213] :
      ( k5_relat_1(A_213,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_213,k1_xboole_0))
      | ~ v1_relat_1(A_213) ) ),
    inference(resolution,[status(thm)],[c_1730,c_10])).

tff(c_1757,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_24,c_1753])).

tff(c_1774,plain,(
    ! [A_215] :
      ( k5_relat_1(A_215,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1757])).

tff(c_1792,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1774])).

tff(c_1801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_913,c_1792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:20:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.80  
% 3.58/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 3.58/1.81  
% 3.58/1.81  %Foreground sorts:
% 3.58/1.81  
% 3.58/1.81  
% 3.58/1.81  %Background operators:
% 3.58/1.81  
% 3.58/1.81  
% 3.58/1.81  %Foreground operators:
% 3.58/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.58/1.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.58/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.58/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.58/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.58/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.58/1.81  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.58/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.58/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.58/1.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.58/1.81  
% 3.86/1.82  tff(f_110, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.86/1.82  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.86/1.82  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.86/1.82  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.86/1.82  tff(f_103, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.86/1.82  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.86/1.82  tff(f_54, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.86/1.82  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.86/1.82  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.86/1.82  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.86/1.82  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.86/1.82  tff(f_78, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.86/1.82  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.86/1.82  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.86/1.82  tff(f_86, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.86/1.82  tff(c_38, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.86/1.82  tff(c_78, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 3.86/1.82  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.86/1.82  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.82  tff(c_73, plain, (![A_33]: (v1_relat_1(A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.86/1.82  tff(c_77, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_73])).
% 3.86/1.82  tff(c_24, plain, (![A_20, B_21]: (v1_relat_1(k5_relat_1(A_20, B_21)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.86/1.82  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.86/1.82  tff(c_191, plain, (![A_65, B_66]: (r1_tarski(k1_relat_1(k5_relat_1(A_65, B_66)), k1_relat_1(A_65)) | ~v1_relat_1(B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.86/1.82  tff(c_194, plain, (![B_66]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_66)), k1_xboole_0) | ~v1_relat_1(B_66) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_191])).
% 3.86/1.82  tff(c_232, plain, (![B_74]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_74)), k1_xboole_0) | ~v1_relat_1(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_194])).
% 3.86/1.82  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.86/1.82  tff(c_136, plain, (![A_56, C_57, B_58]: (r1_xboole_0(A_56, k4_xboole_0(C_57, B_58)) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.86/1.82  tff(c_170, plain, (![A_61, A_62]: (r1_xboole_0(A_61, A_62) | ~r1_tarski(A_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_136])).
% 3.86/1.82  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.86/1.82  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.82  tff(c_106, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.86/1.82  tff(c_116, plain, (![A_46, B_47]: (~r1_xboole_0(A_46, B_47) | v1_xboole_0(k3_xboole_0(A_46, B_47)))), inference(resolution, [status(thm)], [c_4, c_106])).
% 3.86/1.82  tff(c_125, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | v1_xboole_0(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_116])).
% 3.86/1.82  tff(c_187, plain, (![A_62]: (v1_xboole_0(A_62) | ~r1_tarski(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_170, c_125])).
% 3.86/1.82  tff(c_250, plain, (![B_77]: (v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_77))) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_232, c_187])).
% 3.86/1.82  tff(c_26, plain, (![A_22]: (~v1_xboole_0(k1_relat_1(A_22)) | ~v1_relat_1(A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.86/1.82  tff(c_860, plain, (![B_121]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_121)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_121)) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_250, c_26])).
% 3.86/1.82  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.86/1.82  tff(c_869, plain, (![B_122]: (k5_relat_1(k1_xboole_0, B_122)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_122)) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_860, c_10])).
% 3.86/1.82  tff(c_873, plain, (![B_21]: (k5_relat_1(k1_xboole_0, B_21)=k1_xboole_0 | ~v1_relat_1(B_21) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_869])).
% 3.86/1.82  tff(c_885, plain, (![B_124]: (k5_relat_1(k1_xboole_0, B_124)=k1_xboole_0 | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_873])).
% 3.86/1.82  tff(c_903, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_885])).
% 3.86/1.82  tff(c_912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_903])).
% 3.86/1.82  tff(c_913, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.86/1.82  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.86/1.82  tff(c_1203, plain, (![A_171, B_172]: (r1_tarski(k2_relat_1(k5_relat_1(A_171, B_172)), k2_relat_1(B_172)) | ~v1_relat_1(B_172) | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.86/1.82  tff(c_1209, plain, (![A_171]: (r1_tarski(k2_relat_1(k5_relat_1(A_171, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_171))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1203])).
% 3.86/1.82  tff(c_1275, plain, (![A_175]: (r1_tarski(k2_relat_1(k5_relat_1(A_175, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_175))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1209])).
% 3.86/1.82  tff(c_946, plain, (![A_132, C_133, B_134]: (r1_xboole_0(A_132, k4_xboole_0(C_133, B_134)) | ~r1_tarski(A_132, B_134))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.86/1.82  tff(c_949, plain, (![A_132, A_13]: (r1_xboole_0(A_132, A_13) | ~r1_tarski(A_132, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_946])).
% 3.86/1.82  tff(c_950, plain, (![A_135, B_136, C_137]: (~r1_xboole_0(A_135, B_136) | ~r2_hidden(C_137, k3_xboole_0(A_135, B_136)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.86/1.82  tff(c_960, plain, (![A_140, C_141]: (~r1_xboole_0(A_140, A_140) | ~r2_hidden(C_141, A_140))), inference(superposition, [status(thm), theory('equality')], [c_8, c_950])).
% 3.86/1.82  tff(c_969, plain, (![C_142, A_143]: (~r2_hidden(C_142, A_143) | ~r1_tarski(A_143, k1_xboole_0))), inference(resolution, [status(thm)], [c_949, c_960])).
% 3.86/1.82  tff(c_973, plain, (![A_1]: (~r1_tarski(A_1, k1_xboole_0) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_969])).
% 3.86/1.82  tff(c_1287, plain, (![A_176]: (v1_xboole_0(k2_relat_1(k5_relat_1(A_176, k1_xboole_0))) | ~v1_relat_1(A_176))), inference(resolution, [status(thm)], [c_1275, c_973])).
% 3.86/1.82  tff(c_28, plain, (![A_23]: (~v1_xboole_0(k2_relat_1(A_23)) | ~v1_relat_1(A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.86/1.82  tff(c_1730, plain, (![A_211]: (~v1_relat_1(k5_relat_1(A_211, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_211, k1_xboole_0)) | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_1287, c_28])).
% 3.86/1.82  tff(c_1753, plain, (![A_213]: (k5_relat_1(A_213, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_213, k1_xboole_0)) | ~v1_relat_1(A_213))), inference(resolution, [status(thm)], [c_1730, c_10])).
% 3.86/1.82  tff(c_1757, plain, (![A_20]: (k5_relat_1(A_20, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_24, c_1753])).
% 3.86/1.82  tff(c_1774, plain, (![A_215]: (k5_relat_1(A_215, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_215))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1757])).
% 3.86/1.82  tff(c_1792, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_1774])).
% 3.86/1.82  tff(c_1801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_913, c_1792])).
% 3.86/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.82  
% 3.86/1.82  Inference rules
% 3.86/1.82  ----------------------
% 3.86/1.82  #Ref     : 0
% 3.86/1.82  #Sup     : 386
% 3.86/1.82  #Fact    : 0
% 3.86/1.82  #Define  : 0
% 3.86/1.82  #Split   : 2
% 3.86/1.82  #Chain   : 0
% 3.86/1.82  #Close   : 0
% 3.86/1.82  
% 3.86/1.82  Ordering : KBO
% 3.86/1.82  
% 3.86/1.82  Simplification rules
% 3.86/1.82  ----------------------
% 3.86/1.82  #Subsume      : 111
% 3.86/1.82  #Demod        : 189
% 3.86/1.82  #Tautology    : 161
% 3.86/1.82  #SimpNegUnit  : 18
% 3.86/1.82  #BackRed      : 6
% 3.86/1.82  
% 3.86/1.82  #Partial instantiations: 0
% 3.86/1.82  #Strategies tried      : 1
% 3.86/1.82  
% 3.86/1.82  Timing (in seconds)
% 3.86/1.82  ----------------------
% 3.86/1.83  Preprocessing        : 0.36
% 3.86/1.83  Parsing              : 0.21
% 3.86/1.83  CNF conversion       : 0.02
% 3.86/1.83  Main loop            : 0.64
% 3.86/1.83  Inferencing          : 0.26
% 3.86/1.83  Reduction            : 0.18
% 3.86/1.83  Demodulation         : 0.12
% 3.86/1.83  BG Simplification    : 0.03
% 3.86/1.83  Subsumption          : 0.13
% 3.86/1.83  Abstraction          : 0.02
% 3.86/1.83  MUC search           : 0.00
% 3.86/1.83  Cooper               : 0.00
% 3.86/1.83  Total                : 1.04
% 3.86/1.83  Index Insertion      : 0.00
% 3.86/1.83  Index Deletion       : 0.00
% 3.86/1.83  Index Matching       : 0.00
% 3.86/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
