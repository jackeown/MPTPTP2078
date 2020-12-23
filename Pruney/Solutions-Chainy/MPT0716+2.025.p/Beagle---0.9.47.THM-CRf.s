%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:40 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 216 expanded)
%              Number of leaves         :   23 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 609 expanded)
%              Number of equality atoms :    6 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_30,B_31)),k1_relat_1(A_30))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_37,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_37,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [C_3] :
      ( r1_tarski('#skF_4',C_3)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_55,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_45])).

tff(c_61,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_55])).

tff(c_8,plain,(
    ! [A_9,B_11] :
      ( k10_relat_1(A_9,k1_relat_1(B_11)) = k1_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,k10_relat_1(B_16,A_15)),A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    ! [C_35,A_36,B_37] :
      ( r1_tarski(k9_relat_1(C_35,A_36),k9_relat_1(C_35,B_37))
      | ~ r1_tarski(A_36,B_37)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_150,plain,(
    ! [C_50,A_51,B_52] :
      ( k2_xboole_0(k9_relat_1(C_50,A_51),k9_relat_1(C_50,B_52)) = k9_relat_1(C_50,B_52)
      | ~ r1_tarski(A_51,B_52)
      | ~ v1_relat_1(C_50) ) ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_172,plain,(
    ! [C_53,A_54,C_55,B_56] :
      ( r1_tarski(k9_relat_1(C_53,A_54),C_55)
      | ~ r1_tarski(k9_relat_1(C_53,B_56),C_55)
      | ~ r1_tarski(A_54,B_56)
      | ~ v1_relat_1(C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_2])).

tff(c_182,plain,(
    ! [B_57,A_58,A_59] :
      ( r1_tarski(k9_relat_1(B_57,A_58),A_59)
      | ~ r1_tarski(A_58,k10_relat_1(B_57,A_59))
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_12,c_172])).

tff(c_28,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_99,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_28])).

tff(c_100,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_187,plain,
    ( ~ r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_182,c_100])).

tff(c_194,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_187])).

tff(c_200,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_194])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_37,c_200])).

tff(c_205,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_223,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_205,c_24])).

tff(c_204,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_26,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_238,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_205,c_26])).

tff(c_283,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(A_69,k10_relat_1(C_70,B_71))
      | ~ r1_tarski(k9_relat_1(C_70,A_69),B_71)
      | ~ r1_tarski(A_69,k1_relat_1(C_70))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_289,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_238,c_283])).

tff(c_307,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_204,c_289])).

tff(c_321,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_307])).

tff(c_324,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_321])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_324])).

tff(c_328,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_381,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_30])).

tff(c_327,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_333,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_32])).

tff(c_558,plain,(
    ! [A_107,C_108,B_109] :
      ( r1_tarski(A_107,k10_relat_1(C_108,B_109))
      | ~ r1_tarski(k9_relat_1(C_108,A_107),B_109)
      | ~ r1_tarski(A_107,k1_relat_1(C_108))
      | ~ v1_funct_1(C_108)
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_579,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_333,c_558])).

tff(c_594,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_327,c_579])).

tff(c_602,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_594])).

tff(c_607,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_602])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:54:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.43  
% 2.51/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.44  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.81/1.44  
% 2.81/1.44  %Foreground sorts:
% 2.81/1.44  
% 2.81/1.44  
% 2.81/1.44  %Background operators:
% 2.81/1.44  
% 2.81/1.44  
% 2.81/1.44  %Foreground operators:
% 2.81/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.81/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.81/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.81/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.44  
% 2.81/1.45  tff(f_86, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 2.81/1.45  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.81/1.45  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.81/1.45  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.81/1.45  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.81/1.45  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.81/1.45  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 2.81/1.45  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 2.81/1.45  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.45  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.45  tff(c_51, plain, (![A_30, B_31]: (r1_tarski(k1_relat_1(k5_relat_1(A_30, B_31)), k1_relat_1(A_30)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.81/1.45  tff(c_34, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.45  tff(c_37, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_34])).
% 2.81/1.45  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.45  tff(c_41, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_37, c_4])).
% 2.81/1.45  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.45  tff(c_45, plain, (![C_3]: (r1_tarski('#skF_4', C_3) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_3))), inference(superposition, [status(thm), theory('equality')], [c_41, c_2])).
% 2.81/1.45  tff(c_55, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_51, c_45])).
% 2.81/1.45  tff(c_61, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_55])).
% 2.81/1.45  tff(c_8, plain, (![A_9, B_11]: (k10_relat_1(A_9, k1_relat_1(B_11))=k1_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.45  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.45  tff(c_12, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, k10_relat_1(B_16, A_15)), A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.81/1.45  tff(c_81, plain, (![C_35, A_36, B_37]: (r1_tarski(k9_relat_1(C_35, A_36), k9_relat_1(C_35, B_37)) | ~r1_tarski(A_36, B_37) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.45  tff(c_150, plain, (![C_50, A_51, B_52]: (k2_xboole_0(k9_relat_1(C_50, A_51), k9_relat_1(C_50, B_52))=k9_relat_1(C_50, B_52) | ~r1_tarski(A_51, B_52) | ~v1_relat_1(C_50))), inference(resolution, [status(thm)], [c_81, c_4])).
% 2.81/1.45  tff(c_172, plain, (![C_53, A_54, C_55, B_56]: (r1_tarski(k9_relat_1(C_53, A_54), C_55) | ~r1_tarski(k9_relat_1(C_53, B_56), C_55) | ~r1_tarski(A_54, B_56) | ~v1_relat_1(C_53))), inference(superposition, [status(thm), theory('equality')], [c_150, c_2])).
% 2.81/1.45  tff(c_182, plain, (![B_57, A_58, A_59]: (r1_tarski(k9_relat_1(B_57, A_58), A_59) | ~r1_tarski(A_58, k10_relat_1(B_57, A_59)) | ~v1_funct_1(B_57) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_12, c_172])).
% 2.81/1.45  tff(c_28, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.45  tff(c_99, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_28])).
% 2.81/1.45  tff(c_100, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_99])).
% 2.81/1.45  tff(c_187, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_182, c_100])).
% 2.81/1.45  tff(c_194, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_187])).
% 2.81/1.45  tff(c_200, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_194])).
% 2.81/1.45  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_37, c_200])).
% 2.81/1.45  tff(c_205, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_99])).
% 2.81/1.45  tff(c_24, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.45  tff(c_223, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_205, c_24])).
% 2.81/1.45  tff(c_204, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_99])).
% 2.81/1.45  tff(c_26, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.45  tff(c_238, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_205, c_26])).
% 2.81/1.45  tff(c_283, plain, (![A_69, C_70, B_71]: (r1_tarski(A_69, k10_relat_1(C_70, B_71)) | ~r1_tarski(k9_relat_1(C_70, A_69), B_71) | ~r1_tarski(A_69, k1_relat_1(C_70)) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.81/1.45  tff(c_289, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_238, c_283])).
% 2.81/1.45  tff(c_307, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_204, c_289])).
% 2.81/1.45  tff(c_321, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_307])).
% 2.81/1.45  tff(c_324, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_321])).
% 2.81/1.45  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_324])).
% 2.81/1.45  tff(c_328, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_34])).
% 2.81/1.45  tff(c_30, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.45  tff(c_381, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_328, c_30])).
% 2.81/1.45  tff(c_327, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_34])).
% 2.81/1.45  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.45  tff(c_333, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_328, c_32])).
% 2.81/1.45  tff(c_558, plain, (![A_107, C_108, B_109]: (r1_tarski(A_107, k10_relat_1(C_108, B_109)) | ~r1_tarski(k9_relat_1(C_108, A_107), B_109) | ~r1_tarski(A_107, k1_relat_1(C_108)) | ~v1_funct_1(C_108) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.81/1.45  tff(c_579, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_333, c_558])).
% 2.81/1.45  tff(c_594, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_327, c_579])).
% 2.81/1.45  tff(c_602, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_594])).
% 2.81/1.45  tff(c_607, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_602])).
% 2.81/1.45  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_607])).
% 2.81/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  
% 2.81/1.45  Inference rules
% 2.81/1.45  ----------------------
% 2.81/1.45  #Ref     : 0
% 2.81/1.45  #Sup     : 133
% 2.81/1.45  #Fact    : 0
% 2.81/1.45  #Define  : 0
% 2.81/1.45  #Split   : 3
% 2.81/1.45  #Chain   : 0
% 2.81/1.45  #Close   : 0
% 2.81/1.45  
% 2.81/1.45  Ordering : KBO
% 2.81/1.45  
% 2.81/1.45  Simplification rules
% 2.81/1.45  ----------------------
% 2.81/1.45  #Subsume      : 5
% 2.81/1.45  #Demod        : 56
% 2.81/1.45  #Tautology    : 50
% 2.81/1.45  #SimpNegUnit  : 4
% 2.81/1.45  #BackRed      : 0
% 2.81/1.45  
% 2.81/1.45  #Partial instantiations: 0
% 2.81/1.45  #Strategies tried      : 1
% 2.81/1.45  
% 2.81/1.45  Timing (in seconds)
% 2.81/1.45  ----------------------
% 2.81/1.46  Preprocessing        : 0.32
% 2.81/1.46  Parsing              : 0.17
% 2.81/1.46  CNF conversion       : 0.02
% 2.81/1.46  Main loop            : 0.31
% 2.81/1.46  Inferencing          : 0.13
% 2.81/1.46  Reduction            : 0.08
% 2.81/1.46  Demodulation         : 0.06
% 2.81/1.46  BG Simplification    : 0.02
% 2.81/1.46  Subsumption          : 0.06
% 2.81/1.46  Abstraction          : 0.02
% 2.81/1.46  MUC search           : 0.00
% 2.81/1.46  Cooper               : 0.00
% 2.81/1.46  Total                : 0.67
% 2.81/1.46  Index Insertion      : 0.00
% 2.81/1.46  Index Deletion       : 0.00
% 2.81/1.46  Index Matching       : 0.00
% 2.81/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
