%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:55 EST 2020

% Result     : Theorem 16.00s
% Output     : CNFRefutation 16.00s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 180 expanded)
%              Number of leaves         :   35 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 275 expanded)
%              Number of equality atoms :   48 ( 101 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_263,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k3_subset_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_279,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_263])).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_297,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_6])).

tff(c_367,plain,(
    ! [A_83,B_84] :
      ( k3_subset_1(A_83,k3_subset_1(A_83,B_84)) = B_84
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_379,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_367])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_300,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_4])).

tff(c_38,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_197,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(B_60,A_61)
      | ~ r2_hidden(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_200,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_203,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_200])).

tff(c_866,plain,(
    ! [A_128,C_129] :
      ( k4_xboole_0(A_128,C_129) = k3_subset_1(A_128,C_129)
      | ~ r1_tarski(C_129,A_128) ) ),
    inference(resolution,[status(thm)],[c_203,c_263])).

tff(c_911,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_300,c_866])).

tff(c_946,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_379,c_911])).

tff(c_239,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_324,plain,(
    ! [A_77,A_78,B_79] :
      ( r1_tarski(A_77,A_78)
      | ~ r1_tarski(A_77,k4_xboole_0(A_78,B_79)) ) ),
    inference(resolution,[status(thm)],[c_4,c_239])).

tff(c_389,plain,(
    ! [A_85,B_86,B_87] : r1_tarski(k4_xboole_0(k4_xboole_0(A_85,B_86),B_87),A_85) ),
    inference(resolution,[status(thm)],[c_4,c_324])).

tff(c_408,plain,(
    ! [A_6,B_7,B_87] : r1_tarski(k4_xboole_0(k3_xboole_0(A_6,B_7),B_87),A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_389])).

tff(c_1044,plain,(
    ! [B_134] : r1_tarski(k4_xboole_0('#skF_4',B_134),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_408])).

tff(c_277,plain,(
    ! [A_13,C_17] :
      ( k4_xboole_0(A_13,C_17) = k3_subset_1(A_13,C_17)
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(resolution,[status(thm)],[c_203,c_263])).

tff(c_18700,plain,(
    ! [B_491] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',B_491)) = k3_subset_1('#skF_3',k4_xboole_0('#skF_4',B_491)) ),
    inference(resolution,[status(thm)],[c_1044,c_277])).

tff(c_10,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_121,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(B_53,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_95])).

tff(c_24,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_127,plain,(
    ! [B_53,A_52] : k2_xboole_0(B_53,A_52) = k2_xboole_0(A_52,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_24])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_280,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_263])).

tff(c_307,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_6])).

tff(c_380,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_367])).

tff(c_310,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_4])).

tff(c_908,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_310,c_866])).

tff(c_944,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_380,c_908])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k4_xboole_0(A_8,B_9),k3_xboole_0(A_8,C_10)) = k4_xboole_0(A_8,k4_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_975,plain,(
    ! [B_9] : k4_xboole_0('#skF_3',k4_xboole_0(B_9,'#skF_5')) = k2_xboole_0(k4_xboole_0('#skF_3',B_9),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_8])).

tff(c_988,plain,(
    ! [B_9] : k4_xboole_0('#skF_3',k4_xboole_0(B_9,'#skF_5')) = k2_xboole_0('#skF_5',k4_xboole_0('#skF_3',B_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_975])).

tff(c_18721,plain,(
    k3_subset_1('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18700,c_988])).

tff(c_18853,plain,(
    k3_subset_1('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_18721])).

tff(c_474,plain,(
    ! [A_98,B_99,C_100] :
      ( k7_subset_1(A_98,B_99,C_100) = k4_xboole_0(B_99,C_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_486,plain,(
    ! [C_100] : k7_subset_1('#skF_3','#skF_4',C_100) = k4_xboole_0('#skF_4',C_100) ),
    inference(resolution,[status(thm)],[c_50,c_474])).

tff(c_46,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') != k3_subset_1('#skF_3',k7_subset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_488,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') != k3_subset_1('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_46])).

tff(c_21908,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') != k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18853,c_488])).

tff(c_1779,plain,(
    ! [A_179,B_180,C_181] :
      ( k4_subset_1(A_179,B_180,C_181) = k2_xboole_0(B_180,C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(A_179))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(A_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2051,plain,(
    ! [B_208] :
      ( k4_subset_1('#skF_3',B_208,'#skF_5') = k2_xboole_0(B_208,'#skF_5')
      | ~ m1_subset_1(B_208,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1779])).

tff(c_4050,plain,(
    ! [C_257] :
      ( k4_subset_1('#skF_3',C_257,'#skF_5') = k2_xboole_0(C_257,'#skF_5')
      | ~ r1_tarski(C_257,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_203,c_2051])).

tff(c_4259,plain,(
    ! [B_5] : k4_subset_1('#skF_3',k4_xboole_0('#skF_3',B_5),'#skF_5') = k2_xboole_0(k4_xboole_0('#skF_3',B_5),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_4050])).

tff(c_35697,plain,(
    ! [B_665] : k4_subset_1('#skF_3',k4_xboole_0('#skF_3',B_665),'#skF_5') = k2_xboole_0('#skF_5',k4_xboole_0('#skF_3',B_665)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_4259])).

tff(c_35780,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') = k2_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_35697])).

tff(c_35809,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') = k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_35780])).

tff(c_35811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21908,c_35809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.00/8.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.00/8.41  
% 16.00/8.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.00/8.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 16.00/8.41  
% 16.00/8.41  %Foreground sorts:
% 16.00/8.41  
% 16.00/8.41  
% 16.00/8.41  %Background operators:
% 16.00/8.41  
% 16.00/8.41  
% 16.00/8.41  %Foreground operators:
% 16.00/8.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.00/8.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.00/8.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.00/8.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.00/8.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.00/8.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 16.00/8.41  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 16.00/8.41  tff('#skF_5', type, '#skF_5': $i).
% 16.00/8.41  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 16.00/8.41  tff('#skF_3', type, '#skF_3': $i).
% 16.00/8.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.00/8.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.00/8.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.00/8.41  tff('#skF_4', type, '#skF_4': $i).
% 16.00/8.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.00/8.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.00/8.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.00/8.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.00/8.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.00/8.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.00/8.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.00/8.41  
% 16.00/8.43  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 16.00/8.43  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 16.00/8.43  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.00/8.43  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 16.00/8.43  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 16.00/8.43  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 16.00/8.43  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 16.00/8.43  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 16.00/8.43  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.00/8.43  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 16.00/8.43  tff(f_48, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 16.00/8.43  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 16.00/8.43  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 16.00/8.43  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 16.00/8.43  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.00/8.43  tff(c_263, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k3_subset_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.00/8.43  tff(c_279, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_263])).
% 16.00/8.43  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.00/8.43  tff(c_297, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_279, c_6])).
% 16.00/8.43  tff(c_367, plain, (![A_83, B_84]: (k3_subset_1(A_83, k3_subset_1(A_83, B_84))=B_84 | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.00/8.43  tff(c_379, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_50, c_367])).
% 16.00/8.43  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.00/8.43  tff(c_300, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_279, c_4])).
% 16.00/8.43  tff(c_38, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.00/8.43  tff(c_14, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.00/8.43  tff(c_197, plain, (![B_60, A_61]: (m1_subset_1(B_60, A_61) | ~r2_hidden(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.00/8.43  tff(c_200, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(resolution, [status(thm)], [c_14, c_197])).
% 16.00/8.43  tff(c_203, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(negUnitSimplification, [status(thm)], [c_38, c_200])).
% 16.00/8.43  tff(c_866, plain, (![A_128, C_129]: (k4_xboole_0(A_128, C_129)=k3_subset_1(A_128, C_129) | ~r1_tarski(C_129, A_128))), inference(resolution, [status(thm)], [c_203, c_263])).
% 16.00/8.43  tff(c_911, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_300, c_866])).
% 16.00/8.43  tff(c_946, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_297, c_379, c_911])).
% 16.00/8.43  tff(c_239, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.00/8.43  tff(c_324, plain, (![A_77, A_78, B_79]: (r1_tarski(A_77, A_78) | ~r1_tarski(A_77, k4_xboole_0(A_78, B_79)))), inference(resolution, [status(thm)], [c_4, c_239])).
% 16.00/8.43  tff(c_389, plain, (![A_85, B_86, B_87]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_85, B_86), B_87), A_85))), inference(resolution, [status(thm)], [c_4, c_324])).
% 16.00/8.43  tff(c_408, plain, (![A_6, B_7, B_87]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_6, B_7), B_87), A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_389])).
% 16.00/8.43  tff(c_1044, plain, (![B_134]: (r1_tarski(k4_xboole_0('#skF_4', B_134), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_946, c_408])).
% 16.00/8.43  tff(c_277, plain, (![A_13, C_17]: (k4_xboole_0(A_13, C_17)=k3_subset_1(A_13, C_17) | ~r1_tarski(C_17, A_13))), inference(resolution, [status(thm)], [c_203, c_263])).
% 16.00/8.43  tff(c_18700, plain, (![B_491]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', B_491))=k3_subset_1('#skF_3', k4_xboole_0('#skF_4', B_491)))), inference(resolution, [status(thm)], [c_1044, c_277])).
% 16.00/8.43  tff(c_10, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.00/8.43  tff(c_95, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 16.00/8.43  tff(c_121, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(B_53, A_52))), inference(superposition, [status(thm), theory('equality')], [c_10, c_95])).
% 16.00/8.43  tff(c_24, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 16.00/8.43  tff(c_127, plain, (![B_53, A_52]: (k2_xboole_0(B_53, A_52)=k2_xboole_0(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_121, c_24])).
% 16.00/8.43  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.00/8.43  tff(c_280, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_263])).
% 16.00/8.43  tff(c_307, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_280, c_6])).
% 16.00/8.43  tff(c_380, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_48, c_367])).
% 16.00/8.43  tff(c_310, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_280, c_4])).
% 16.00/8.43  tff(c_908, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_310, c_866])).
% 16.00/8.43  tff(c_944, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_380, c_908])).
% 16.00/8.43  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k4_xboole_0(A_8, B_9), k3_xboole_0(A_8, C_10))=k4_xboole_0(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.00/8.43  tff(c_975, plain, (![B_9]: (k4_xboole_0('#skF_3', k4_xboole_0(B_9, '#skF_5'))=k2_xboole_0(k4_xboole_0('#skF_3', B_9), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_944, c_8])).
% 16.00/8.43  tff(c_988, plain, (![B_9]: (k4_xboole_0('#skF_3', k4_xboole_0(B_9, '#skF_5'))=k2_xboole_0('#skF_5', k4_xboole_0('#skF_3', B_9)))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_975])).
% 16.00/8.43  tff(c_18721, plain, (k3_subset_1('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18700, c_988])).
% 16.00/8.43  tff(c_18853, plain, (k3_subset_1('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_18721])).
% 16.00/8.43  tff(c_474, plain, (![A_98, B_99, C_100]: (k7_subset_1(A_98, B_99, C_100)=k4_xboole_0(B_99, C_100) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.00/8.43  tff(c_486, plain, (![C_100]: (k7_subset_1('#skF_3', '#skF_4', C_100)=k4_xboole_0('#skF_4', C_100))), inference(resolution, [status(thm)], [c_50, c_474])).
% 16.00/8.43  tff(c_46, plain, (k4_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'), '#skF_5')!=k3_subset_1('#skF_3', k7_subset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.00/8.43  tff(c_488, plain, (k4_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'), '#skF_5')!=k3_subset_1('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_46])).
% 16.00/8.43  tff(c_21908, plain, (k4_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'), '#skF_5')!=k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18853, c_488])).
% 16.00/8.43  tff(c_1779, plain, (![A_179, B_180, C_181]: (k4_subset_1(A_179, B_180, C_181)=k2_xboole_0(B_180, C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(A_179)) | ~m1_subset_1(B_180, k1_zfmisc_1(A_179)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.00/8.43  tff(c_2051, plain, (![B_208]: (k4_subset_1('#skF_3', B_208, '#skF_5')=k2_xboole_0(B_208, '#skF_5') | ~m1_subset_1(B_208, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_1779])).
% 16.00/8.43  tff(c_4050, plain, (![C_257]: (k4_subset_1('#skF_3', C_257, '#skF_5')=k2_xboole_0(C_257, '#skF_5') | ~r1_tarski(C_257, '#skF_3'))), inference(resolution, [status(thm)], [c_203, c_2051])).
% 16.00/8.43  tff(c_4259, plain, (![B_5]: (k4_subset_1('#skF_3', k4_xboole_0('#skF_3', B_5), '#skF_5')=k2_xboole_0(k4_xboole_0('#skF_3', B_5), '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_4050])).
% 16.00/8.43  tff(c_35697, plain, (![B_665]: (k4_subset_1('#skF_3', k4_xboole_0('#skF_3', B_665), '#skF_5')=k2_xboole_0('#skF_5', k4_xboole_0('#skF_3', B_665)))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_4259])).
% 16.00/8.43  tff(c_35780, plain, (k4_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'), '#skF_5')=k2_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_279, c_35697])).
% 16.00/8.43  tff(c_35809, plain, (k4_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'), '#skF_5')=k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_35780])).
% 16.00/8.43  tff(c_35811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21908, c_35809])).
% 16.00/8.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.00/8.43  
% 16.00/8.43  Inference rules
% 16.00/8.43  ----------------------
% 16.00/8.43  #Ref     : 0
% 16.00/8.43  #Sup     : 8161
% 16.00/8.43  #Fact    : 0
% 16.00/8.43  #Define  : 0
% 16.00/8.43  #Split   : 0
% 16.00/8.43  #Chain   : 0
% 16.00/8.43  #Close   : 0
% 16.00/8.43  
% 16.00/8.43  Ordering : KBO
% 16.00/8.43  
% 16.00/8.43  Simplification rules
% 16.00/8.43  ----------------------
% 16.00/8.43  #Subsume      : 315
% 16.00/8.43  #Demod        : 3100
% 16.00/8.43  #Tautology    : 1844
% 16.00/8.43  #SimpNegUnit  : 45
% 16.00/8.43  #BackRed      : 7
% 16.00/8.43  
% 16.00/8.43  #Partial instantiations: 0
% 16.00/8.43  #Strategies tried      : 1
% 16.00/8.43  
% 16.00/8.43  Timing (in seconds)
% 16.00/8.43  ----------------------
% 16.00/8.43  Preprocessing        : 0.36
% 16.00/8.43  Parsing              : 0.18
% 16.00/8.43  CNF conversion       : 0.03
% 16.00/8.43  Main loop            : 7.23
% 16.00/8.43  Inferencing          : 1.14
% 16.00/8.43  Reduction            : 3.68
% 16.00/8.43  Demodulation         : 3.24
% 16.00/8.43  BG Simplification    : 0.17
% 16.00/8.43  Subsumption          : 1.83
% 16.00/8.43  Abstraction          : 0.25
% 16.00/8.43  MUC search           : 0.00
% 16.00/8.43  Cooper               : 0.00
% 16.00/8.43  Total                : 7.62
% 16.00/8.43  Index Insertion      : 0.00
% 16.00/8.43  Index Deletion       : 0.00
% 16.00/8.43  Index Matching       : 0.00
% 16.00/8.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
