%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:50 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 131 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  141 ( 326 expanded)
%              Number of equality atoms :   37 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1224,plain,(
    ! [A_82] :
      ( k4_relat_1(A_82) = k2_funct_1(A_82)
      | ~ v2_funct_1(A_82)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1227,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1224])).

tff(c_1230,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1227])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1234,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_2])).

tff(c_1238,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1234])).

tff(c_1240,plain,(
    ! [A_83] :
      ( k1_relat_1(k2_funct_1(A_83)) = k2_relat_1(A_83)
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_2] :
      ( k9_relat_1(A_2,k1_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1599,plain,(
    ! [A_109] :
      ( k9_relat_1(k2_funct_1(A_109),k2_relat_1(A_109)) = k2_relat_1(k2_funct_1(A_109))
      | ~ v1_relat_1(k2_funct_1(A_109))
      | ~ v2_funct_1(A_109)
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1240,c_4])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( k9_relat_1(B_5,k2_relat_1(A_3)) = k2_relat_1(k5_relat_1(A_3,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3075,plain,(
    ! [A_160] :
      ( k2_relat_1(k5_relat_1(A_160,k2_funct_1(A_160))) = k2_relat_1(k2_funct_1(A_160))
      | ~ v1_relat_1(k2_funct_1(A_160))
      | ~ v1_relat_1(A_160)
      | ~ v1_relat_1(k2_funct_1(A_160))
      | ~ v2_funct_1(A_160)
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1599,c_6])).

tff(c_103,plain,(
    ! [A_26] :
      ( k4_relat_1(A_26) = k2_funct_1(A_26)
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_106,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_109,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_106])).

tff(c_130,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_2])).

tff(c_134,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_130])).

tff(c_20,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    ! [A_24] :
      ( k5_relat_1(A_24,k6_relat_1(k2_relat_1(A_24))) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_89,plain,(
    ! [A_12] :
      ( k5_relat_1(k6_relat_1(A_12),k6_relat_1(A_12)) = k6_relat_1(A_12)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_93,plain,(
    ! [A_12] : k5_relat_1(k6_relat_1(A_12),k6_relat_1(A_12)) = k6_relat_1(A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_89])).

tff(c_110,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_27,B_28)),k2_relat_1(B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [A_12] :
      ( r1_tarski(k2_relat_1(k6_relat_1(A_12)),k2_relat_1(k6_relat_1(A_12)))
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_110])).

tff(c_121,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_14,c_14,c_113])).

tff(c_26,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_243,plain,(
    ! [A_38,B_39] :
      ( k1_relat_1(k5_relat_1(A_38,B_39)) = k1_relat_1(A_38)
      | ~ r1_tarski(k2_relat_1(A_38),k1_relat_1(B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1063,plain,(
    ! [A_76,A_77] :
      ( k1_relat_1(k5_relat_1(A_76,k2_funct_1(A_77))) = k1_relat_1(A_76)
      | ~ r1_tarski(k2_relat_1(A_76),k2_relat_1(A_77))
      | ~ v1_relat_1(k2_funct_1(A_77))
      | ~ v1_relat_1(A_76)
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_243])).

tff(c_1134,plain,(
    ! [A_78] :
      ( k1_relat_1(k5_relat_1(A_78,k2_funct_1(A_78))) = k1_relat_1(A_78)
      | ~ v1_relat_1(k2_funct_1(A_78))
      | ~ v2_funct_1(A_78)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_121,c_1063])).

tff(c_28,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_1165,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1134,c_70])).

tff(c_1182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_134,c_1165])).

tff(c_1183,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_3152,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3075,c_1183])).

tff(c_3177,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_1238,c_34,c_1238,c_3152])).

tff(c_3183,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3177])).

tff(c_3187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_3183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:36 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.98  
% 4.69/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.98  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 4.69/1.98  
% 4.69/1.98  %Foreground sorts:
% 4.69/1.98  
% 4.69/1.98  
% 4.69/1.98  %Background operators:
% 4.69/1.98  
% 4.69/1.98  
% 4.69/1.98  %Foreground operators:
% 4.69/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.69/1.98  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.69/1.98  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.69/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.69/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.69/1.98  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.69/1.98  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.69/1.98  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.69/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.69/1.98  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.69/1.98  
% 5.03/1.99  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 5.03/1.99  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.03/1.99  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 5.03/1.99  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.03/1.99  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 5.03/1.99  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 5.03/1.99  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.03/1.99  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.03/1.99  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 5.03/1.99  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 5.03/1.99  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 5.03/1.99  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.03/1.99  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.03/1.99  tff(c_30, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.03/1.99  tff(c_24, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.03/1.99  tff(c_1224, plain, (![A_82]: (k4_relat_1(A_82)=k2_funct_1(A_82) | ~v2_funct_1(A_82) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.03/1.99  tff(c_1227, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1224])).
% 5.03/1.99  tff(c_1230, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1227])).
% 5.03/1.99  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.03/1.99  tff(c_1234, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1230, c_2])).
% 5.03/1.99  tff(c_1238, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1234])).
% 5.03/1.99  tff(c_1240, plain, (![A_83]: (k1_relat_1(k2_funct_1(A_83))=k2_relat_1(A_83) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.03/1.99  tff(c_4, plain, (![A_2]: (k9_relat_1(A_2, k1_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.03/1.99  tff(c_1599, plain, (![A_109]: (k9_relat_1(k2_funct_1(A_109), k2_relat_1(A_109))=k2_relat_1(k2_funct_1(A_109)) | ~v1_relat_1(k2_funct_1(A_109)) | ~v2_funct_1(A_109) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_1240, c_4])).
% 5.03/1.99  tff(c_6, plain, (![B_5, A_3]: (k9_relat_1(B_5, k2_relat_1(A_3))=k2_relat_1(k5_relat_1(A_3, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.03/1.99  tff(c_3075, plain, (![A_160]: (k2_relat_1(k5_relat_1(A_160, k2_funct_1(A_160)))=k2_relat_1(k2_funct_1(A_160)) | ~v1_relat_1(k2_funct_1(A_160)) | ~v1_relat_1(A_160) | ~v1_relat_1(k2_funct_1(A_160)) | ~v2_funct_1(A_160) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(superposition, [status(thm), theory('equality')], [c_1599, c_6])).
% 5.03/1.99  tff(c_103, plain, (![A_26]: (k4_relat_1(A_26)=k2_funct_1(A_26) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.03/1.99  tff(c_106, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_103])).
% 5.03/1.99  tff(c_109, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_106])).
% 5.03/1.99  tff(c_130, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_109, c_2])).
% 5.03/1.99  tff(c_134, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_130])).
% 5.03/1.99  tff(c_20, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.03/1.99  tff(c_14, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.03/1.99  tff(c_80, plain, (![A_24]: (k5_relat_1(A_24, k6_relat_1(k2_relat_1(A_24)))=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.03/1.99  tff(c_89, plain, (![A_12]: (k5_relat_1(k6_relat_1(A_12), k6_relat_1(A_12))=k6_relat_1(A_12) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_80])).
% 5.03/1.99  tff(c_93, plain, (![A_12]: (k5_relat_1(k6_relat_1(A_12), k6_relat_1(A_12))=k6_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_89])).
% 5.03/1.99  tff(c_110, plain, (![A_27, B_28]: (r1_tarski(k2_relat_1(k5_relat_1(A_27, B_28)), k2_relat_1(B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.03/1.99  tff(c_113, plain, (![A_12]: (r1_tarski(k2_relat_1(k6_relat_1(A_12)), k2_relat_1(k6_relat_1(A_12))) | ~v1_relat_1(k6_relat_1(A_12)) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_110])).
% 5.03/1.99  tff(c_121, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_14, c_14, c_113])).
% 5.03/1.99  tff(c_26, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.03/1.99  tff(c_243, plain, (![A_38, B_39]: (k1_relat_1(k5_relat_1(A_38, B_39))=k1_relat_1(A_38) | ~r1_tarski(k2_relat_1(A_38), k1_relat_1(B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.03/1.99  tff(c_1063, plain, (![A_76, A_77]: (k1_relat_1(k5_relat_1(A_76, k2_funct_1(A_77)))=k1_relat_1(A_76) | ~r1_tarski(k2_relat_1(A_76), k2_relat_1(A_77)) | ~v1_relat_1(k2_funct_1(A_77)) | ~v1_relat_1(A_76) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_26, c_243])).
% 5.03/1.99  tff(c_1134, plain, (![A_78]: (k1_relat_1(k5_relat_1(A_78, k2_funct_1(A_78)))=k1_relat_1(A_78) | ~v1_relat_1(k2_funct_1(A_78)) | ~v2_funct_1(A_78) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_121, c_1063])).
% 5.03/1.99  tff(c_28, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.03/1.99  tff(c_70, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 5.03/1.99  tff(c_1165, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1134, c_70])).
% 5.03/1.99  tff(c_1182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_134, c_1165])).
% 5.03/1.99  tff(c_1183, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 5.03/1.99  tff(c_3152, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3075, c_1183])).
% 5.03/1.99  tff(c_3177, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_1238, c_34, c_1238, c_3152])).
% 5.03/1.99  tff(c_3183, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_3177])).
% 5.03/1.99  tff(c_3187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_3183])).
% 5.03/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.03/1.99  
% 5.03/1.99  Inference rules
% 5.03/1.99  ----------------------
% 5.03/1.99  #Ref     : 0
% 5.03/1.99  #Sup     : 779
% 5.03/1.99  #Fact    : 0
% 5.03/1.99  #Define  : 0
% 5.03/1.99  #Split   : 2
% 5.03/1.99  #Chain   : 0
% 5.03/1.99  #Close   : 0
% 5.03/1.99  
% 5.03/1.99  Ordering : KBO
% 5.03/1.99  
% 5.03/1.99  Simplification rules
% 5.03/1.99  ----------------------
% 5.03/1.99  #Subsume      : 96
% 5.03/1.99  #Demod        : 691
% 5.03/1.99  #Tautology    : 228
% 5.03/1.99  #SimpNegUnit  : 0
% 5.03/1.99  #BackRed      : 0
% 5.03/1.99  
% 5.03/1.99  #Partial instantiations: 0
% 5.03/1.99  #Strategies tried      : 1
% 5.03/1.99  
% 5.03/1.99  Timing (in seconds)
% 5.03/1.99  ----------------------
% 5.03/1.99  Preprocessing        : 0.33
% 5.03/1.99  Parsing              : 0.18
% 5.03/1.99  CNF conversion       : 0.02
% 5.03/2.00  Main loop            : 0.80
% 5.03/2.00  Inferencing          : 0.29
% 5.03/2.00  Reduction            : 0.28
% 5.03/2.00  Demodulation         : 0.21
% 5.03/2.00  BG Simplification    : 0.04
% 5.03/2.00  Subsumption          : 0.14
% 5.03/2.00  Abstraction          : 0.05
% 5.03/2.00  MUC search           : 0.00
% 5.03/2.00  Cooper               : 0.00
% 5.03/2.00  Total                : 1.16
% 5.03/2.00  Index Insertion      : 0.00
% 5.03/2.00  Index Deletion       : 0.00
% 5.03/2.00  Index Matching       : 0.00
% 5.03/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
