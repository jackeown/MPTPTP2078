%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:45 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 193 expanded)
%              Number of leaves         :   21 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 663 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k2_wellord1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( v2_wellord1(B)
         => v2_wellord1(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v1_relat_2(B)
       => v1_relat_2(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_wellord1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v1_wellord1(B)
       => v1_wellord1(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_wellord1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_2(B)
       => v4_relat_2(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_wellord1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v6_relat_2(B)
       => v6_relat_2(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_wellord1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v8_relat_2(B)
       => v8_relat_2(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_wellord1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k2_wellord1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_1] :
      ( v8_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_16] :
      ( v1_relat_2(A_16)
      | ~ v2_wellord1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,
    ( v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_38,plain,(
    v1_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_35])).

tff(c_16,plain,(
    ! [B_5,A_4] :
      ( v1_relat_2(k2_wellord1(B_5,A_4))
      | ~ v1_relat_2(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_1] :
      ( v6_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ! [A_18] :
      ( v1_wellord1(A_18)
      | ~ v2_wellord1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,
    ( v1_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_46,plain,(
    v1_wellord1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_43])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( v1_wellord1(k2_wellord1(B_13,A_12))
      | ~ v1_wellord1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_1] :
      ( v4_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( v4_relat_2(k2_wellord1(B_11,A_10))
      | ~ v4_relat_2(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [B_7,A_6] :
      ( v6_relat_2(k2_wellord1(B_7,A_6))
      | ~ v6_relat_2(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [B_9,A_8] :
      ( v8_relat_2(k2_wellord1(B_9,A_8))
      | ~ v8_relat_2(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_54,plain,(
    ! [A_31] :
      ( v2_wellord1(A_31)
      | ~ v1_wellord1(A_31)
      | ~ v6_relat_2(A_31)
      | ~ v4_relat_2(A_31)
      | ~ v8_relat_2(A_31)
      | ~ v1_relat_2(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [B_32,A_33] :
      ( v2_wellord1(k2_wellord1(B_32,A_33))
      | ~ v1_wellord1(k2_wellord1(B_32,A_33))
      | ~ v6_relat_2(k2_wellord1(B_32,A_33))
      | ~ v4_relat_2(k2_wellord1(B_32,A_33))
      | ~ v1_relat_2(k2_wellord1(B_32,A_33))
      | ~ v1_relat_1(k2_wellord1(B_32,A_33))
      | ~ v8_relat_2(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_20,c_54])).

tff(c_72,plain,(
    ! [B_34,A_35] :
      ( v2_wellord1(k2_wellord1(B_34,A_35))
      | ~ v1_wellord1(k2_wellord1(B_34,A_35))
      | ~ v4_relat_2(k2_wellord1(B_34,A_35))
      | ~ v1_relat_2(k2_wellord1(B_34,A_35))
      | ~ v1_relat_1(k2_wellord1(B_34,A_35))
      | ~ v8_relat_2(B_34)
      | ~ v6_relat_2(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_81,plain,(
    ! [B_36,A_37] :
      ( v2_wellord1(k2_wellord1(B_36,A_37))
      | ~ v1_wellord1(k2_wellord1(B_36,A_37))
      | ~ v1_relat_2(k2_wellord1(B_36,A_37))
      | ~ v1_relat_1(k2_wellord1(B_36,A_37))
      | ~ v8_relat_2(B_36)
      | ~ v6_relat_2(B_36)
      | ~ v4_relat_2(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_26,plain,(
    ~ v2_wellord1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,
    ( ~ v1_wellord1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v8_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_26])).

tff(c_95,plain,
    ( ~ v1_wellord1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v8_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_90])).

tff(c_96,plain,(
    ~ v4_relat_2('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_99,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_99])).

tff(c_104,plain,
    ( ~ v6_relat_2('#skF_2')
    | ~ v8_relat_2('#skF_2')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_wellord1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_106,plain,(
    ~ v1_wellord1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_109,plain,
    ( ~ v1_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_46,c_109])).

tff(c_114,plain,
    ( ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v8_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_116,plain,(
    ~ v6_relat_2('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_119,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_119])).

tff(c_124,plain,
    ( ~ v8_relat_2('#skF_2')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_126,plain,(
    ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_129,plain,
    ( ~ v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38,c_129])).

tff(c_134,plain,
    ( ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v8_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_136,plain,(
    ~ v8_relat_2('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_139,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_139])).

tff(c_144,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_154,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_144])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:09:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.57  
% 2.40/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.58  %$ v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k2_wellord1 > #nlpp > #skF_2 > #skF_1
% 2.40/1.58  
% 2.40/1.58  %Foreground sorts:
% 2.40/1.58  
% 2.40/1.58  
% 2.40/1.58  %Background operators:
% 2.40/1.58  
% 2.40/1.58  
% 2.40/1.58  %Foreground operators:
% 2.40/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.58  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.40/1.58  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.40/1.58  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 2.40/1.58  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.40/1.58  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.40/1.58  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.58  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.58  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.40/1.58  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 2.40/1.58  
% 2.40/1.60  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => v2_wellord1(k2_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_wellord1)).
% 2.40/1.60  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 2.40/1.60  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 2.40/1.60  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v1_relat_2(B) => v1_relat_2(k2_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_wellord1)).
% 2.40/1.60  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v1_wellord1(B) => v1_wellord1(k2_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_wellord1)).
% 2.40/1.60  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_2(B) => v4_relat_2(k2_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_wellord1)).
% 2.40/1.60  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v6_relat_2(B) => v6_relat_2(k2_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_wellord1)).
% 2.40/1.60  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v8_relat_2(B) => v8_relat_2(k2_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_wellord1)).
% 2.40/1.60  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.40/1.60  tff(c_14, plain, (![A_2, B_3]: (v1_relat_1(k2_wellord1(A_2, B_3)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.40/1.60  tff(c_28, plain, (v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.40/1.60  tff(c_10, plain, (![A_1]: (v8_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.60  tff(c_32, plain, (![A_16]: (v1_relat_2(A_16) | ~v2_wellord1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.60  tff(c_35, plain, (v1_relat_2('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_32])).
% 2.40/1.60  tff(c_38, plain, (v1_relat_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_35])).
% 2.40/1.60  tff(c_16, plain, (![B_5, A_4]: (v1_relat_2(k2_wellord1(B_5, A_4)) | ~v1_relat_2(B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.40/1.60  tff(c_6, plain, (![A_1]: (v6_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.60  tff(c_40, plain, (![A_18]: (v1_wellord1(A_18) | ~v2_wellord1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.60  tff(c_43, plain, (v1_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_40])).
% 2.40/1.60  tff(c_46, plain, (v1_wellord1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_43])).
% 2.40/1.60  tff(c_24, plain, (![B_13, A_12]: (v1_wellord1(k2_wellord1(B_13, A_12)) | ~v1_wellord1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.60  tff(c_8, plain, (![A_1]: (v4_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.60  tff(c_22, plain, (![B_11, A_10]: (v4_relat_2(k2_wellord1(B_11, A_10)) | ~v4_relat_2(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.40/1.60  tff(c_18, plain, (![B_7, A_6]: (v6_relat_2(k2_wellord1(B_7, A_6)) | ~v6_relat_2(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.40/1.60  tff(c_20, plain, (![B_9, A_8]: (v8_relat_2(k2_wellord1(B_9, A_8)) | ~v8_relat_2(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.40/1.60  tff(c_54, plain, (![A_31]: (v2_wellord1(A_31) | ~v1_wellord1(A_31) | ~v6_relat_2(A_31) | ~v4_relat_2(A_31) | ~v8_relat_2(A_31) | ~v1_relat_2(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.60  tff(c_63, plain, (![B_32, A_33]: (v2_wellord1(k2_wellord1(B_32, A_33)) | ~v1_wellord1(k2_wellord1(B_32, A_33)) | ~v6_relat_2(k2_wellord1(B_32, A_33)) | ~v4_relat_2(k2_wellord1(B_32, A_33)) | ~v1_relat_2(k2_wellord1(B_32, A_33)) | ~v1_relat_1(k2_wellord1(B_32, A_33)) | ~v8_relat_2(B_32) | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_20, c_54])).
% 2.40/1.60  tff(c_72, plain, (![B_34, A_35]: (v2_wellord1(k2_wellord1(B_34, A_35)) | ~v1_wellord1(k2_wellord1(B_34, A_35)) | ~v4_relat_2(k2_wellord1(B_34, A_35)) | ~v1_relat_2(k2_wellord1(B_34, A_35)) | ~v1_relat_1(k2_wellord1(B_34, A_35)) | ~v8_relat_2(B_34) | ~v6_relat_2(B_34) | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_18, c_63])).
% 2.40/1.60  tff(c_81, plain, (![B_36, A_37]: (v2_wellord1(k2_wellord1(B_36, A_37)) | ~v1_wellord1(k2_wellord1(B_36, A_37)) | ~v1_relat_2(k2_wellord1(B_36, A_37)) | ~v1_relat_1(k2_wellord1(B_36, A_37)) | ~v8_relat_2(B_36) | ~v6_relat_2(B_36) | ~v4_relat_2(B_36) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_22, c_72])).
% 2.40/1.60  tff(c_26, plain, (~v2_wellord1(k2_wellord1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.40/1.60  tff(c_90, plain, (~v1_wellord1(k2_wellord1('#skF_2', '#skF_1')) | ~v1_relat_2(k2_wellord1('#skF_2', '#skF_1')) | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1')) | ~v8_relat_2('#skF_2') | ~v6_relat_2('#skF_2') | ~v4_relat_2('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_81, c_26])).
% 2.40/1.60  tff(c_95, plain, (~v1_wellord1(k2_wellord1('#skF_2', '#skF_1')) | ~v1_relat_2(k2_wellord1('#skF_2', '#skF_1')) | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1')) | ~v8_relat_2('#skF_2') | ~v6_relat_2('#skF_2') | ~v4_relat_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_90])).
% 2.40/1.60  tff(c_96, plain, (~v4_relat_2('#skF_2')), inference(splitLeft, [status(thm)], [c_95])).
% 2.40/1.60  tff(c_99, plain, (~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_96])).
% 2.40/1.60  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_99])).
% 2.40/1.60  tff(c_104, plain, (~v6_relat_2('#skF_2') | ~v8_relat_2('#skF_2') | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1')) | ~v1_relat_2(k2_wellord1('#skF_2', '#skF_1')) | ~v1_wellord1(k2_wellord1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_95])).
% 2.40/1.60  tff(c_106, plain, (~v1_wellord1(k2_wellord1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_104])).
% 2.40/1.60  tff(c_109, plain, (~v1_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_106])).
% 2.40/1.60  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_46, c_109])).
% 2.40/1.60  tff(c_114, plain, (~v1_relat_2(k2_wellord1('#skF_2', '#skF_1')) | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1')) | ~v8_relat_2('#skF_2') | ~v6_relat_2('#skF_2')), inference(splitRight, [status(thm)], [c_104])).
% 2.40/1.60  tff(c_116, plain, (~v6_relat_2('#skF_2')), inference(splitLeft, [status(thm)], [c_114])).
% 2.40/1.60  tff(c_119, plain, (~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_116])).
% 2.40/1.60  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_119])).
% 2.40/1.60  tff(c_124, plain, (~v8_relat_2('#skF_2') | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1')) | ~v1_relat_2(k2_wellord1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_114])).
% 2.40/1.60  tff(c_126, plain, (~v1_relat_2(k2_wellord1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_124])).
% 2.40/1.60  tff(c_129, plain, (~v1_relat_2('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_126])).
% 2.40/1.60  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_38, c_129])).
% 2.40/1.60  tff(c_134, plain, (~v1_relat_1(k2_wellord1('#skF_2', '#skF_1')) | ~v8_relat_2('#skF_2')), inference(splitRight, [status(thm)], [c_124])).
% 2.40/1.60  tff(c_136, plain, (~v8_relat_2('#skF_2')), inference(splitLeft, [status(thm)], [c_134])).
% 2.40/1.60  tff(c_139, plain, (~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_136])).
% 2.40/1.60  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_139])).
% 2.40/1.60  tff(c_144, plain, (~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_134])).
% 2.40/1.60  tff(c_154, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_144])).
% 2.40/1.60  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_154])).
% 2.40/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.60  
% 2.40/1.60  Inference rules
% 2.40/1.60  ----------------------
% 2.40/1.60  #Ref     : 0
% 2.40/1.60  #Sup     : 18
% 2.40/1.60  #Fact    : 0
% 2.40/1.60  #Define  : 0
% 2.40/1.60  #Split   : 5
% 2.40/1.60  #Chain   : 0
% 2.40/1.60  #Close   : 0
% 2.40/1.60  
% 2.40/1.60  Ordering : KBO
% 2.40/1.60  
% 2.40/1.60  Simplification rules
% 2.40/1.60  ----------------------
% 2.40/1.60  #Subsume      : 0
% 2.40/1.60  #Demod        : 20
% 2.40/1.60  #Tautology    : 6
% 2.40/1.60  #SimpNegUnit  : 0
% 2.40/1.60  #BackRed      : 0
% 2.40/1.60  
% 2.40/1.60  #Partial instantiations: 0
% 2.40/1.60  #Strategies tried      : 1
% 2.40/1.60  
% 2.40/1.60  Timing (in seconds)
% 2.40/1.60  ----------------------
% 2.40/1.61  Preprocessing        : 0.41
% 2.40/1.61  Parsing              : 0.22
% 2.40/1.61  CNF conversion       : 0.03
% 2.40/1.61  Main loop            : 0.29
% 2.40/1.61  Inferencing          : 0.12
% 2.40/1.61  Reduction            : 0.07
% 2.40/1.61  Demodulation         : 0.05
% 2.40/1.61  BG Simplification    : 0.02
% 2.40/1.61  Subsumption          : 0.06
% 2.40/1.61  Abstraction          : 0.01
% 2.40/1.61  MUC search           : 0.00
% 2.40/1.61  Cooper               : 0.00
% 2.40/1.61  Total                : 0.76
% 2.40/1.61  Index Insertion      : 0.00
% 2.40/1.61  Index Deletion       : 0.00
% 2.40/1.61  Index Matching       : 0.00
% 2.40/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
