%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:08 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 126 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  149 ( 224 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_123,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_40,plain,
    ( k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_68,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_32] :
      ( v1_relat_1(A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k5_relat_1(A_21,B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_88,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_2'(A_43,B_44),B_44)
      | r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [B_44,A_43] :
      ( ~ v1_xboole_0(B_44)
      | r1_xboole_0(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_20,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_4'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_94,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_130,plain,(
    ! [A_56,B_57] :
      ( ~ r1_xboole_0(A_56,B_57)
      | k3_xboole_0(A_56,B_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_94])).

tff(c_167,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = k1_xboole_0
      | ~ v1_xboole_0(B_65) ) ),
    inference(resolution,[status(thm)],[c_92,c_130])).

tff(c_173,plain,(
    ! [A_64] : k3_xboole_0(A_64,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_167])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_270,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_74,B_75)),k1_relat_1(A_74))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_276,plain,(
    ! [B_75] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_75)),k1_xboole_0)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_270])).

tff(c_337,plain,(
    ! [B_86] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_86)),k1_xboole_0)
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_276])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_340,plain,(
    ! [B_86] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_86)),k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,B_86))
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_337,c_22])).

tff(c_343,plain,(
    ! [B_87] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_87)) = k1_xboole_0
      | ~ v1_relat_1(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_340])).

tff(c_28,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(k1_relat_1(A_23))
      | ~ v1_relat_1(A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_358,plain,(
    ! [B_87] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_87))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_28])).

tff(c_610,plain,(
    ! [B_98] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_98))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_358])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_640,plain,(
    ! [B_100] :
      ( k5_relat_1(k1_xboole_0,B_100) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_100))
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_610,c_8])).

tff(c_644,plain,(
    ! [B_22] :
      ( k5_relat_1(k1_xboole_0,B_22) = k1_xboole_0
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_640])).

tff(c_656,plain,(
    ! [B_102] :
      ( k5_relat_1(k1_xboole_0,B_102) = k1_xboole_0
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_644])).

tff(c_668,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_656])).

tff(c_675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_668])).

tff(c_676,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_700,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_2'(A_108,B_109),B_109)
      | r1_xboole_0(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_704,plain,(
    ! [B_109,A_108] :
      ( ~ v1_xboole_0(B_109)
      | r1_xboole_0(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_700,c_2])).

tff(c_712,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r1_xboole_0(A_114,B_115)
      | ~ r2_hidden(C_116,k3_xboole_0(A_114,B_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_737,plain,(
    ! [A_119,B_120] :
      ( ~ r1_xboole_0(A_119,B_120)
      | k3_xboole_0(A_119,B_120) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_712])).

tff(c_742,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,B_122) = k1_xboole_0
      | ~ v1_xboole_0(B_122) ) ),
    inference(resolution,[status(thm)],[c_704,c_737])).

tff(c_748,plain,(
    ! [A_121] : k3_xboole_0(A_121,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_742])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1001,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_153,B_154)),k2_relat_1(B_154))
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1010,plain,(
    ! [A_153] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_153,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1001])).

tff(c_1021,plain,(
    ! [A_155] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_155,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1010])).

tff(c_1024,plain,(
    ! [A_155] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_155,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_155,k1_xboole_0))
      | ~ v1_relat_1(A_155) ) ),
    inference(resolution,[status(thm)],[c_1021,c_22])).

tff(c_1027,plain,(
    ! [A_156] :
      ( k2_relat_1(k5_relat_1(A_156,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_1024])).

tff(c_30,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k2_relat_1(A_24))
      | ~ v1_relat_1(A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1042,plain,(
    ! [A_156] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_156,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_156,k1_xboole_0))
      | ~ v1_relat_1(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_30])).

tff(c_1250,plain,(
    ! [A_165] :
      ( ~ v1_relat_1(k5_relat_1(A_165,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_165,k1_xboole_0))
      | ~ v1_relat_1(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1042])).

tff(c_1340,plain,(
    ! [A_169] :
      ( k5_relat_1(A_169,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_169,k1_xboole_0))
      | ~ v1_relat_1(A_169) ) ),
    inference(resolution,[status(thm)],[c_1250,c_8])).

tff(c_1344,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_1340])).

tff(c_1348,plain,(
    ! [A_170] :
      ( k5_relat_1(A_170,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1344])).

tff(c_1360,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_1348])).

tff(c_1367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_676,c_1360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.46  
% 3.04/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_2
% 3.04/1.46  
% 3.04/1.46  %Foreground sorts:
% 3.04/1.46  
% 3.04/1.46  
% 3.04/1.46  %Background operators:
% 3.04/1.46  
% 3.04/1.46  
% 3.04/1.46  %Foreground operators:
% 3.04/1.46  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.04/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.04/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.04/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.04/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.04/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.46  
% 3.20/1.48  tff(f_130, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.20/1.48  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.20/1.48  tff(f_84, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.20/1.48  tff(f_90, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.20/1.48  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.20/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.20/1.48  tff(f_76, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.20/1.48  tff(f_68, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.20/1.48  tff(f_123, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.20/1.48  tff(f_113, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.20/1.48  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.20/1.48  tff(f_98, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.20/1.48  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.20/1.48  tff(f_120, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.20/1.48  tff(f_106, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.20/1.48  tff(c_40, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.48  tff(c_68, plain, (k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.20/1.48  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.48  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.48  tff(c_57, plain, (![A_32]: (v1_relat_1(A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.48  tff(c_61, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_57])).
% 3.20/1.48  tff(c_26, plain, (![A_21, B_22]: (v1_relat_1(k5_relat_1(A_21, B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.48  tff(c_88, plain, (![A_43, B_44]: (r2_hidden('#skF_2'(A_43, B_44), B_44) | r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.48  tff(c_92, plain, (![B_44, A_43]: (~v1_xboole_0(B_44) | r1_xboole_0(A_43, B_44))), inference(resolution, [status(thm)], [c_88, c_2])).
% 3.20/1.48  tff(c_20, plain, (![A_16]: (r2_hidden('#skF_4'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.20/1.48  tff(c_94, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.48  tff(c_130, plain, (![A_56, B_57]: (~r1_xboole_0(A_56, B_57) | k3_xboole_0(A_56, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_94])).
% 3.20/1.48  tff(c_167, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=k1_xboole_0 | ~v1_xboole_0(B_65))), inference(resolution, [status(thm)], [c_92, c_130])).
% 3.20/1.48  tff(c_173, plain, (![A_64]: (k3_xboole_0(A_64, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_167])).
% 3.20/1.48  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.20/1.48  tff(c_270, plain, (![A_74, B_75]: (r1_tarski(k1_relat_1(k5_relat_1(A_74, B_75)), k1_relat_1(A_74)) | ~v1_relat_1(B_75) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.20/1.48  tff(c_276, plain, (![B_75]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_75)), k1_xboole_0) | ~v1_relat_1(B_75) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_270])).
% 3.20/1.48  tff(c_337, plain, (![B_86]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_86)), k1_xboole_0) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_276])).
% 3.20/1.48  tff(c_22, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.48  tff(c_340, plain, (![B_86]: (k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_86)), k1_xboole_0)=k1_relat_1(k5_relat_1(k1_xboole_0, B_86)) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_337, c_22])).
% 3.20/1.48  tff(c_343, plain, (![B_87]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_87))=k1_xboole_0 | ~v1_relat_1(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_340])).
% 3.20/1.48  tff(c_28, plain, (![A_23]: (~v1_xboole_0(k1_relat_1(A_23)) | ~v1_relat_1(A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.48  tff(c_358, plain, (![B_87]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_87)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_87)) | ~v1_relat_1(B_87))), inference(superposition, [status(thm), theory('equality')], [c_343, c_28])).
% 3.20/1.48  tff(c_610, plain, (![B_98]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_98)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_98)) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_358])).
% 3.20/1.48  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.20/1.48  tff(c_640, plain, (![B_100]: (k5_relat_1(k1_xboole_0, B_100)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_100)) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_610, c_8])).
% 3.20/1.48  tff(c_644, plain, (![B_22]: (k5_relat_1(k1_xboole_0, B_22)=k1_xboole_0 | ~v1_relat_1(B_22) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_640])).
% 3.20/1.48  tff(c_656, plain, (![B_102]: (k5_relat_1(k1_xboole_0, B_102)=k1_xboole_0 | ~v1_relat_1(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_644])).
% 3.20/1.48  tff(c_668, plain, (k5_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_656])).
% 3.20/1.48  tff(c_675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_668])).
% 3.20/1.48  tff(c_676, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.20/1.48  tff(c_700, plain, (![A_108, B_109]: (r2_hidden('#skF_2'(A_108, B_109), B_109) | r1_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.48  tff(c_704, plain, (![B_109, A_108]: (~v1_xboole_0(B_109) | r1_xboole_0(A_108, B_109))), inference(resolution, [status(thm)], [c_700, c_2])).
% 3.20/1.48  tff(c_712, plain, (![A_114, B_115, C_116]: (~r1_xboole_0(A_114, B_115) | ~r2_hidden(C_116, k3_xboole_0(A_114, B_115)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.48  tff(c_737, plain, (![A_119, B_120]: (~r1_xboole_0(A_119, B_120) | k3_xboole_0(A_119, B_120)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_712])).
% 3.20/1.48  tff(c_742, plain, (![A_121, B_122]: (k3_xboole_0(A_121, B_122)=k1_xboole_0 | ~v1_xboole_0(B_122))), inference(resolution, [status(thm)], [c_704, c_737])).
% 3.20/1.48  tff(c_748, plain, (![A_121]: (k3_xboole_0(A_121, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_742])).
% 3.20/1.48  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.20/1.48  tff(c_1001, plain, (![A_153, B_154]: (r1_tarski(k2_relat_1(k5_relat_1(A_153, B_154)), k2_relat_1(B_154)) | ~v1_relat_1(B_154) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.20/1.48  tff(c_1010, plain, (![A_153]: (r1_tarski(k2_relat_1(k5_relat_1(A_153, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_153))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1001])).
% 3.20/1.48  tff(c_1021, plain, (![A_155]: (r1_tarski(k2_relat_1(k5_relat_1(A_155, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_155))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_1010])).
% 3.20/1.48  tff(c_1024, plain, (![A_155]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_155, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_155, k1_xboole_0)) | ~v1_relat_1(A_155))), inference(resolution, [status(thm)], [c_1021, c_22])).
% 3.20/1.48  tff(c_1027, plain, (![A_156]: (k2_relat_1(k5_relat_1(A_156, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_156))), inference(demodulation, [status(thm), theory('equality')], [c_748, c_1024])).
% 3.20/1.48  tff(c_30, plain, (![A_24]: (~v1_xboole_0(k2_relat_1(A_24)) | ~v1_relat_1(A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.20/1.48  tff(c_1042, plain, (![A_156]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_156, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_156, k1_xboole_0)) | ~v1_relat_1(A_156))), inference(superposition, [status(thm), theory('equality')], [c_1027, c_30])).
% 3.20/1.48  tff(c_1250, plain, (![A_165]: (~v1_relat_1(k5_relat_1(A_165, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_165, k1_xboole_0)) | ~v1_relat_1(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1042])).
% 3.20/1.48  tff(c_1340, plain, (![A_169]: (k5_relat_1(A_169, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_169, k1_xboole_0)) | ~v1_relat_1(A_169))), inference(resolution, [status(thm)], [c_1250, c_8])).
% 3.20/1.48  tff(c_1344, plain, (![A_21]: (k5_relat_1(A_21, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_21))), inference(resolution, [status(thm)], [c_26, c_1340])).
% 3.20/1.48  tff(c_1348, plain, (![A_170]: (k5_relat_1(A_170, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_1344])).
% 3.20/1.48  tff(c_1360, plain, (k5_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_1348])).
% 3.20/1.48  tff(c_1367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_676, c_1360])).
% 3.20/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  Inference rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Ref     : 0
% 3.20/1.48  #Sup     : 301
% 3.20/1.48  #Fact    : 0
% 3.20/1.48  #Define  : 0
% 3.20/1.48  #Split   : 4
% 3.20/1.48  #Chain   : 0
% 3.20/1.48  #Close   : 0
% 3.20/1.48  
% 3.20/1.48  Ordering : KBO
% 3.20/1.48  
% 3.20/1.48  Simplification rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Subsume      : 51
% 3.20/1.48  #Demod        : 190
% 3.20/1.48  #Tautology    : 151
% 3.20/1.48  #SimpNegUnit  : 15
% 3.20/1.48  #BackRed      : 4
% 3.20/1.48  
% 3.20/1.48  #Partial instantiations: 0
% 3.20/1.48  #Strategies tried      : 1
% 3.20/1.48  
% 3.20/1.48  Timing (in seconds)
% 3.20/1.48  ----------------------
% 3.20/1.48  Preprocessing        : 0.30
% 3.20/1.48  Parsing              : 0.17
% 3.20/1.48  CNF conversion       : 0.02
% 3.20/1.48  Main loop            : 0.41
% 3.20/1.48  Inferencing          : 0.17
% 3.20/1.48  Reduction            : 0.11
% 3.20/1.48  Demodulation         : 0.08
% 3.20/1.48  BG Simplification    : 0.02
% 3.20/1.48  Subsumption          : 0.07
% 3.20/1.48  Abstraction          : 0.02
% 3.20/1.48  MUC search           : 0.00
% 3.20/1.48  Cooper               : 0.00
% 3.20/1.48  Total                : 0.75
% 3.20/1.48  Index Insertion      : 0.00
% 3.20/1.48  Index Deletion       : 0.00
% 3.20/1.48  Index Matching       : 0.00
% 3.20/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
