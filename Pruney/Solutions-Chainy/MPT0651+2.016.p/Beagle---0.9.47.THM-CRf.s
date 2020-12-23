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
% DateTime   : Thu Dec  3 10:03:50 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 158 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 362 expanded)
%              Number of equality atoms :   45 ( 129 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_36,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_65,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,(
    ! [A_28] :
      ( k5_relat_1(A_28,k6_relat_1(k2_relat_1(A_28))) = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_97,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_relat_1(A_13),k6_relat_1(A_13)) = k6_relat_1(A_13)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_85])).

tff(c_101,plain,(
    ! [A_13] : k5_relat_1(k6_relat_1(A_13),k6_relat_1(A_13)) = k6_relat_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_97])).

tff(c_196,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_33,B_34)),k2_relat_1(B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_205,plain,(
    ! [A_13] :
      ( r1_tarski(k2_relat_1(k6_relat_1(A_13)),k2_relat_1(k6_relat_1(A_13)))
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_196])).

tff(c_220,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_18,c_18,c_205])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_137,plain,(
    ! [A_32] :
      ( k4_relat_1(A_32) = k2_funct_1(A_32)
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_143,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_137])).

tff(c_149,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_143])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_2])).

tff(c_167,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_159])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_153,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_10])).

tff(c_163,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_153])).

tff(c_343,plain,(
    ! [A_44,B_45] :
      ( k1_relat_1(k5_relat_1(A_44,B_45)) = k1_relat_1(A_44)
      | ~ r1_tarski(k2_relat_1(A_44),k1_relat_1(B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_362,plain,(
    ! [A_44] :
      ( k1_relat_1(k5_relat_1(A_44,k2_funct_1('#skF_1'))) = k1_relat_1(A_44)
      | ~ r1_tarski(k2_relat_1(A_44),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_343])).

tff(c_1145,plain,(
    ! [A_71] :
      ( k1_relat_1(k5_relat_1(A_71,k2_funct_1('#skF_1'))) = k1_relat_1(A_71)
      | ~ r1_tarski(k2_relat_1(A_71),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_362])).

tff(c_1178,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_220,c_1145])).

tff(c_1200,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1178])).

tff(c_1202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1200])).

tff(c_1203,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1284,plain,(
    ! [A_79] :
      ( k4_relat_1(A_79) = k2_funct_1(A_79)
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1290,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1284])).

tff(c_1296,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1290])).

tff(c_1306,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_2])).

tff(c_1314,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1306])).

tff(c_1442,plain,(
    ! [B_89,A_90] :
      ( k9_relat_1(B_89,k2_relat_1(A_90)) = k2_relat_1(k5_relat_1(A_90,B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1303,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_8])).

tff(c_1312,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1303])).

tff(c_1300,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_10])).

tff(c_1310,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1300])).

tff(c_4,plain,(
    ! [A_2] :
      ( k9_relat_1(A_2,k1_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1319,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_4])).

tff(c_1323,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_1319])).

tff(c_1360,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_1323])).

tff(c_1448,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_1360])).

tff(c_1477,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1314,c_1448])).

tff(c_1479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1203,c_1477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:45:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.54  
% 3.36/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.54  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.36/1.54  
% 3.36/1.54  %Foreground sorts:
% 3.36/1.54  
% 3.36/1.54  
% 3.36/1.54  %Background operators:
% 3.36/1.54  
% 3.36/1.54  
% 3.36/1.54  %Foreground operators:
% 3.36/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.36/1.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.36/1.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.36/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.36/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.54  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.36/1.54  
% 3.36/1.56  tff(f_111, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 3.36/1.56  tff(f_90, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.36/1.56  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.36/1.56  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.36/1.56  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.36/1.56  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.36/1.56  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.36/1.56  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.36/1.56  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.36/1.56  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.36/1.56  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.36/1.56  tff(c_36, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.36/1.56  tff(c_65, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.36/1.56  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.36/1.56  tff(c_28, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.36/1.56  tff(c_18, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.36/1.56  tff(c_85, plain, (![A_28]: (k5_relat_1(A_28, k6_relat_1(k2_relat_1(A_28)))=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.36/1.56  tff(c_97, plain, (![A_13]: (k5_relat_1(k6_relat_1(A_13), k6_relat_1(A_13))=k6_relat_1(A_13) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_85])).
% 3.36/1.56  tff(c_101, plain, (![A_13]: (k5_relat_1(k6_relat_1(A_13), k6_relat_1(A_13))=k6_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_97])).
% 3.36/1.56  tff(c_196, plain, (![A_33, B_34]: (r1_tarski(k2_relat_1(k5_relat_1(A_33, B_34)), k2_relat_1(B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.56  tff(c_205, plain, (![A_13]: (r1_tarski(k2_relat_1(k6_relat_1(A_13)), k2_relat_1(k6_relat_1(A_13))) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_196])).
% 3.36/1.56  tff(c_220, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_18, c_18, c_205])).
% 3.36/1.56  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.36/1.56  tff(c_38, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.36/1.56  tff(c_137, plain, (![A_32]: (k4_relat_1(A_32)=k2_funct_1(A_32) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.56  tff(c_143, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_137])).
% 3.36/1.56  tff(c_149, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_143])).
% 3.36/1.56  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.56  tff(c_159, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_149, c_2])).
% 3.36/1.56  tff(c_167, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_159])).
% 3.36/1.56  tff(c_10, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.56  tff(c_153, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_149, c_10])).
% 3.36/1.56  tff(c_163, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_153])).
% 3.36/1.56  tff(c_343, plain, (![A_44, B_45]: (k1_relat_1(k5_relat_1(A_44, B_45))=k1_relat_1(A_44) | ~r1_tarski(k2_relat_1(A_44), k1_relat_1(B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.56  tff(c_362, plain, (![A_44]: (k1_relat_1(k5_relat_1(A_44, k2_funct_1('#skF_1')))=k1_relat_1(A_44) | ~r1_tarski(k2_relat_1(A_44), k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_163, c_343])).
% 3.36/1.56  tff(c_1145, plain, (![A_71]: (k1_relat_1(k5_relat_1(A_71, k2_funct_1('#skF_1')))=k1_relat_1(A_71) | ~r1_tarski(k2_relat_1(A_71), k2_relat_1('#skF_1')) | ~v1_relat_1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_362])).
% 3.36/1.56  tff(c_1178, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_220, c_1145])).
% 3.36/1.56  tff(c_1200, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1178])).
% 3.36/1.56  tff(c_1202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_1200])).
% 3.36/1.56  tff(c_1203, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.36/1.56  tff(c_1284, plain, (![A_79]: (k4_relat_1(A_79)=k2_funct_1(A_79) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.56  tff(c_1290, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1284])).
% 3.36/1.56  tff(c_1296, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1290])).
% 3.36/1.56  tff(c_1306, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1296, c_2])).
% 3.36/1.56  tff(c_1314, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1306])).
% 3.36/1.56  tff(c_1442, plain, (![B_89, A_90]: (k9_relat_1(B_89, k2_relat_1(A_90))=k2_relat_1(k5_relat_1(A_90, B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.36/1.56  tff(c_8, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.56  tff(c_1303, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1296, c_8])).
% 3.36/1.56  tff(c_1312, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1303])).
% 3.36/1.56  tff(c_1300, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1296, c_10])).
% 3.36/1.56  tff(c_1310, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1300])).
% 3.36/1.56  tff(c_4, plain, (![A_2]: (k9_relat_1(A_2, k1_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.56  tff(c_1319, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1310, c_4])).
% 3.36/1.56  tff(c_1323, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1314, c_1319])).
% 3.36/1.56  tff(c_1360, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_1323])).
% 3.36/1.56  tff(c_1448, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1442, c_1360])).
% 3.36/1.56  tff(c_1477, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1314, c_1448])).
% 3.36/1.56  tff(c_1479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1203, c_1477])).
% 3.36/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.56  
% 3.36/1.56  Inference rules
% 3.36/1.56  ----------------------
% 3.36/1.56  #Ref     : 0
% 3.36/1.56  #Sup     : 337
% 3.36/1.56  #Fact    : 0
% 3.36/1.56  #Define  : 0
% 3.36/1.56  #Split   : 4
% 3.36/1.56  #Chain   : 0
% 3.36/1.56  #Close   : 0
% 3.36/1.56  
% 3.36/1.56  Ordering : KBO
% 3.36/1.56  
% 3.36/1.56  Simplification rules
% 3.36/1.56  ----------------------
% 3.36/1.56  #Subsume      : 6
% 3.36/1.56  #Demod        : 313
% 3.36/1.56  #Tautology    : 160
% 3.36/1.56  #SimpNegUnit  : 2
% 3.36/1.56  #BackRed      : 0
% 3.36/1.56  
% 3.36/1.56  #Partial instantiations: 0
% 3.36/1.56  #Strategies tried      : 1
% 3.36/1.56  
% 3.36/1.56  Timing (in seconds)
% 3.36/1.56  ----------------------
% 3.36/1.56  Preprocessing        : 0.31
% 3.36/1.56  Parsing              : 0.17
% 3.36/1.56  CNF conversion       : 0.02
% 3.36/1.56  Main loop            : 0.46
% 3.36/1.56  Inferencing          : 0.17
% 3.36/1.56  Reduction            : 0.16
% 3.36/1.56  Demodulation         : 0.12
% 3.36/1.56  BG Simplification    : 0.02
% 3.36/1.56  Subsumption          : 0.07
% 3.36/1.56  Abstraction          : 0.03
% 3.36/1.56  MUC search           : 0.00
% 3.36/1.56  Cooper               : 0.00
% 3.36/1.56  Total                : 0.80
% 3.36/1.56  Index Insertion      : 0.00
% 3.36/1.56  Index Deletion       : 0.00
% 3.36/1.56  Index Matching       : 0.00
% 3.36/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
