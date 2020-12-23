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
% DateTime   : Thu Dec  3 09:59:03 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 321 expanded)
%              Number of leaves         :   25 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          :  144 ( 635 expanded)
%              Number of equality atoms :   39 ( 122 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_32,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_57,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_16,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_109,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_29,B_30)),k2_relat_1(B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_114,plain,(
    ! [A_29] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_29,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_109])).

tff(c_118,plain,(
    ! [A_31] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_31,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_114])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_95,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_149,plain,(
    ! [A_34] :
      ( k2_relat_1(k5_relat_1(A_34,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_118,c_95])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_164,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_34,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_34,k1_xboole_0))
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_20])).

tff(c_175,plain,(
    ! [A_35] :
      ( ~ v1_relat_1(k5_relat_1(A_35,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_35,k1_xboole_0))
      | ~ v1_relat_1(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_164])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_184,plain,(
    ! [A_36] :
      ( k5_relat_1(A_36,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_36,k1_xboole_0))
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_175,c_4])).

tff(c_188,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_184])).

tff(c_192,plain,(
    ! [A_37] :
      ( k5_relat_1(A_37,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_188])).

tff(c_206,plain,(
    ! [A_6] :
      ( k5_relat_1(k4_relat_1(A_6),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_192])).

tff(c_22,plain,(
    ! [A_10] :
      ( k4_relat_1(k4_relat_1(A_10)) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_128,plain,(
    ! [B_32,A_33] :
      ( k5_relat_1(k4_relat_1(B_32),k4_relat_1(A_33)) = k4_relat_1(k5_relat_1(A_33,B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_388,plain,(
    ! [A_43,B_44] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_43),B_44)) = k5_relat_1(k4_relat_1(B_44),A_43)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k4_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_128])).

tff(c_421,plain,(
    ! [A_6] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_6) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_388])).

tff(c_432,plain,(
    ! [A_45] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_45) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_421])).

tff(c_447,plain,(
    ! [A_46] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_46) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_16,c_432])).

tff(c_460,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_206])).

tff(c_501,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_460])).

tff(c_446,plain,(
    ! [A_6] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_6) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_432])).

tff(c_609,plain,(
    ! [A_49] :
      ( k5_relat_1(k1_xboole_0,A_49) = k1_xboole_0
      | ~ v1_relat_1(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_501,c_446])).

tff(c_624,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_609])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_624])).

tff(c_634,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_696,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_58,B_59)),k2_relat_1(B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_704,plain,(
    ! [A_58] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_58,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_696])).

tff(c_710,plain,(
    ! [A_60] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_60,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_704])).

tff(c_673,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_682,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_673])).

tff(c_720,plain,(
    ! [A_61] :
      ( k2_relat_1(k5_relat_1(A_61,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_710,c_682])).

tff(c_735,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_61,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_61,k1_xboole_0))
      | ~ v1_relat_1(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_20])).

tff(c_767,plain,(
    ! [A_64] :
      ( ~ v1_relat_1(k5_relat_1(A_64,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_64,k1_xboole_0))
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_735])).

tff(c_776,plain,(
    ! [A_65] :
      ( k5_relat_1(A_65,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_65,k1_xboole_0))
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_767,c_4])).

tff(c_780,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_776])).

tff(c_784,plain,(
    ! [A_66] :
      ( k5_relat_1(A_66,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_780])).

tff(c_796,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_784])).

tff(c_803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_634,c_796])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.35  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.58/1.35  
% 2.58/1.35  %Foreground sorts:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Background operators:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Foreground operators:
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.58/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.58/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.58/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.35  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.58/1.35  
% 2.58/1.37  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.58/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.58/1.37  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.58/1.37  tff(f_46, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.58/1.37  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.58/1.37  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.58/1.37  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.58/1.37  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.58/1.37  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.37  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.58/1.37  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.58/1.37  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 2.58/1.37  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 2.58/1.37  tff(c_32, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.58/1.37  tff(c_57, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.58/1.37  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.58/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.58/1.37  tff(c_52, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.58/1.37  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.58/1.37  tff(c_16, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.58/1.37  tff(c_18, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.58/1.37  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.58/1.37  tff(c_109, plain, (![A_29, B_30]: (r1_tarski(k2_relat_1(k5_relat_1(A_29, B_30)), k2_relat_1(B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.37  tff(c_114, plain, (![A_29]: (r1_tarski(k2_relat_1(k5_relat_1(A_29, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_28, c_109])).
% 2.58/1.37  tff(c_118, plain, (![A_31]: (r1_tarski(k2_relat_1(k5_relat_1(A_31, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_114])).
% 2.58/1.37  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.37  tff(c_86, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.58/1.37  tff(c_95, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_86])).
% 2.58/1.37  tff(c_149, plain, (![A_34]: (k2_relat_1(k5_relat_1(A_34, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_118, c_95])).
% 2.58/1.37  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.37  tff(c_164, plain, (![A_34]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_34, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_34, k1_xboole_0)) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_149, c_20])).
% 2.58/1.37  tff(c_175, plain, (![A_35]: (~v1_relat_1(k5_relat_1(A_35, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_35, k1_xboole_0)) | ~v1_relat_1(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_164])).
% 2.58/1.37  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.58/1.37  tff(c_184, plain, (![A_36]: (k5_relat_1(A_36, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_36, k1_xboole_0)) | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_175, c_4])).
% 2.58/1.37  tff(c_188, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_184])).
% 2.58/1.37  tff(c_192, plain, (![A_37]: (k5_relat_1(A_37, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_188])).
% 2.58/1.37  tff(c_206, plain, (![A_6]: (k5_relat_1(k4_relat_1(A_6), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_192])).
% 2.58/1.37  tff(c_22, plain, (![A_10]: (k4_relat_1(k4_relat_1(A_10))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.58/1.37  tff(c_128, plain, (![B_32, A_33]: (k5_relat_1(k4_relat_1(B_32), k4_relat_1(A_33))=k4_relat_1(k5_relat_1(A_33, B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.58/1.37  tff(c_388, plain, (![A_43, B_44]: (k4_relat_1(k5_relat_1(k4_relat_1(A_43), B_44))=k5_relat_1(k4_relat_1(B_44), A_43) | ~v1_relat_1(B_44) | ~v1_relat_1(k4_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_22, c_128])).
% 2.58/1.37  tff(c_421, plain, (![A_6]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_6)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_206, c_388])).
% 2.58/1.37  tff(c_432, plain, (![A_45]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_45)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_45)) | ~v1_relat_1(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_421])).
% 2.58/1.37  tff(c_447, plain, (![A_46]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_46)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_16, c_432])).
% 2.58/1.37  tff(c_460, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_447, c_206])).
% 2.58/1.37  tff(c_501, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_460])).
% 2.58/1.37  tff(c_446, plain, (![A_6]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_6)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_432])).
% 2.58/1.37  tff(c_609, plain, (![A_49]: (k5_relat_1(k1_xboole_0, A_49)=k1_xboole_0 | ~v1_relat_1(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_501, c_446])).
% 2.58/1.37  tff(c_624, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_609])).
% 2.58/1.37  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_624])).
% 2.58/1.37  tff(c_634, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.58/1.37  tff(c_696, plain, (![A_58, B_59]: (r1_tarski(k2_relat_1(k5_relat_1(A_58, B_59)), k2_relat_1(B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.37  tff(c_704, plain, (![A_58]: (r1_tarski(k2_relat_1(k5_relat_1(A_58, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_28, c_696])).
% 2.58/1.37  tff(c_710, plain, (![A_60]: (r1_tarski(k2_relat_1(k5_relat_1(A_60, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_704])).
% 2.58/1.37  tff(c_673, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.58/1.37  tff(c_682, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_673])).
% 2.58/1.37  tff(c_720, plain, (![A_61]: (k2_relat_1(k5_relat_1(A_61, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_710, c_682])).
% 2.58/1.37  tff(c_735, plain, (![A_61]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_61, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_61, k1_xboole_0)) | ~v1_relat_1(A_61))), inference(superposition, [status(thm), theory('equality')], [c_720, c_20])).
% 2.58/1.37  tff(c_767, plain, (![A_64]: (~v1_relat_1(k5_relat_1(A_64, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_64, k1_xboole_0)) | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_735])).
% 2.58/1.37  tff(c_776, plain, (![A_65]: (k5_relat_1(A_65, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_65, k1_xboole_0)) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_767, c_4])).
% 2.58/1.37  tff(c_780, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_776])).
% 2.58/1.37  tff(c_784, plain, (![A_66]: (k5_relat_1(A_66, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_780])).
% 2.58/1.37  tff(c_796, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_784])).
% 2.58/1.37  tff(c_803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_634, c_796])).
% 2.58/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  Inference rules
% 2.58/1.37  ----------------------
% 2.58/1.37  #Ref     : 0
% 2.58/1.37  #Sup     : 178
% 2.58/1.37  #Fact    : 0
% 2.58/1.37  #Define  : 0
% 2.58/1.37  #Split   : 1
% 2.58/1.37  #Chain   : 0
% 2.58/1.37  #Close   : 0
% 2.58/1.37  
% 2.58/1.37  Ordering : KBO
% 2.58/1.37  
% 2.58/1.37  Simplification rules
% 2.58/1.37  ----------------------
% 2.58/1.37  #Subsume      : 12
% 2.58/1.37  #Demod        : 132
% 2.58/1.37  #Tautology    : 93
% 2.58/1.37  #SimpNegUnit  : 2
% 2.58/1.37  #BackRed      : 1
% 2.58/1.37  
% 2.58/1.37  #Partial instantiations: 0
% 2.58/1.37  #Strategies tried      : 1
% 2.58/1.37  
% 2.58/1.37  Timing (in seconds)
% 2.58/1.37  ----------------------
% 2.58/1.37  Preprocessing        : 0.29
% 2.58/1.37  Parsing              : 0.17
% 2.58/1.37  CNF conversion       : 0.02
% 2.58/1.37  Main loop            : 0.31
% 2.58/1.37  Inferencing          : 0.12
% 2.58/1.37  Reduction            : 0.09
% 2.58/1.37  Demodulation         : 0.06
% 2.58/1.37  BG Simplification    : 0.02
% 2.58/1.37  Subsumption          : 0.06
% 2.58/1.37  Abstraction          : 0.02
% 2.58/1.37  MUC search           : 0.00
% 2.58/1.37  Cooper               : 0.00
% 2.58/1.37  Total                : 0.64
% 2.58/1.37  Index Insertion      : 0.00
% 2.58/1.37  Index Deletion       : 0.00
% 2.58/1.37  Index Matching       : 0.00
% 2.58/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
