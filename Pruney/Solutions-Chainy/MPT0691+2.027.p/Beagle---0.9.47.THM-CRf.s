%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:43 EST 2020

% Result     : Theorem 24.40s
% Output     : CNFRefutation 24.44s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 255 expanded)
%              Number of leaves         :   30 (  94 expanded)
%              Depth                    :   21
%              Number of atoms          :  120 ( 457 expanded)
%              Number of equality atoms :   34 ( 104 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k7_relat_1(A_18,B_19))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_29] :
      ( k10_relat_1(A_29,k2_relat_1(A_29)) = k1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_885,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(k10_relat_1(B_101,A_102),k10_relat_1(B_101,k2_relat_1(B_101)))
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6685,plain,(
    ! [A_203] :
      ( r1_tarski(k1_relat_1(A_203),k10_relat_1(A_203,k2_relat_1(A_203)))
      | ~ v1_relat_1(A_203)
      | ~ v1_relat_1(A_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_885])).

tff(c_40,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_91,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(A_44,B_45) = B_45
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_91])).

tff(c_189,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(k2_xboole_0(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_192,plain,(
    ! [C_58] :
      ( r1_tarski('#skF_1',C_58)
      | ~ r1_tarski(k1_relat_1('#skF_2'),C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_189])).

tff(c_6696,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6685,c_192])).

tff(c_6719,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6696])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6736,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6719,c_18])).

tff(c_36,plain,(
    ! [A_35,C_37,B_36] :
      ( k3_xboole_0(A_35,k10_relat_1(C_37,B_36)) = k10_relat_1(k7_relat_1(C_37,A_35),B_36)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6804,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6736,c_36])).

tff(c_6868,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6804])).

tff(c_26,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k10_relat_1(B_28,A_27),k1_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7179,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6868,c_26])).

tff(c_97091,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_7179])).

tff(c_97556,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_97091])).

tff(c_97560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_97556])).

tff(c_97562,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_7179])).

tff(c_97561,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7179])).

tff(c_172,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_55,A_56)),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_184,plain,(
    ! [B_55,A_56] :
      ( k1_relat_1(k7_relat_1(B_55,A_56)) = A_56
      | ~ r1_tarski(A_56,k1_relat_1(k7_relat_1(B_55,A_56)))
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_172,c_4])).

tff(c_97581,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_97561,c_184])).

tff(c_97605,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_97581])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_34] :
      ( k7_relat_1(A_34,k1_relat_1(A_34)) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_585,plain,(
    ! [B_86,A_87] :
      ( k2_relat_1(k7_relat_1(B_86,A_87)) = k9_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_597,plain,(
    ! [A_34] :
      ( k9_relat_1(A_34,k1_relat_1(A_34)) = k2_relat_1(A_34)
      | ~ v1_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_585])).

tff(c_97690,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97605,c_597])).

tff(c_97758,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97562,c_97562,c_97690])).

tff(c_24,plain,(
    ! [A_22,C_26,B_25] :
      ( k9_relat_1(k7_relat_1(A_22,C_26),B_25) = k9_relat_1(A_22,B_25)
      | ~ r1_tarski(B_25,C_26)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_99957,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_97758,c_24])).

tff(c_99968,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_99957])).

tff(c_100017,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_99968,c_28])).

tff(c_100053,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97562,c_97605,c_100017])).

tff(c_1140,plain,(
    ! [A_113,C_114,B_115] :
      ( k3_xboole_0(A_113,k10_relat_1(C_114,B_115)) = k10_relat_1(k7_relat_1(C_114,A_113),B_115)
      | ~ v1_relat_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8774,plain,(
    ! [C_223,B_224,A_225] :
      ( k3_xboole_0(k10_relat_1(C_223,B_224),A_225) = k10_relat_1(k7_relat_1(C_223,A_225),B_224)
      | ~ v1_relat_1(C_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_2])).

tff(c_349,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(A_73,B_74)
      | ~ r1_tarski(A_73,k3_xboole_0(B_74,C_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_382,plain,(
    ! [B_74,C_75] : r1_tarski(k3_xboole_0(B_74,C_75),B_74) ),
    inference(resolution,[status(thm)],[c_8,c_349])).

tff(c_8952,plain,(
    ! [C_223,A_225,B_224] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_223,A_225),B_224),k10_relat_1(C_223,B_224))
      | ~ v1_relat_1(C_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8774,c_382])).

tff(c_100162,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100053,c_8952])).

tff(c_100279,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_100162])).

tff(c_100281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_100279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:06:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.40/15.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.44/15.86  
% 24.44/15.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.44/15.86  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 24.44/15.86  
% 24.44/15.86  %Foreground sorts:
% 24.44/15.86  
% 24.44/15.86  
% 24.44/15.86  %Background operators:
% 24.44/15.86  
% 24.44/15.86  
% 24.44/15.86  %Foreground operators:
% 24.44/15.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.44/15.86  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 24.44/15.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.44/15.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 24.44/15.86  tff('#skF_2', type, '#skF_2': $i).
% 24.44/15.86  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 24.44/15.86  tff('#skF_1', type, '#skF_1': $i).
% 24.44/15.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.44/15.86  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 24.44/15.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.44/15.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.44/15.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.44/15.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.44/15.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 24.44/15.86  
% 24.44/15.88  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 24.44/15.88  tff(f_57, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 24.44/15.88  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 24.44/15.88  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 24.44/15.88  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 24.44/15.88  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 24.44/15.88  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 24.44/15.88  tff(f_92, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 24.44/15.88  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 24.44/15.88  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 24.44/15.88  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.44/15.88  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 24.44/15.88  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 24.44/15.88  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 24.44/15.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 24.44/15.88  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 24.44/15.88  tff(c_38, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 24.44/15.88  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 24.44/15.88  tff(c_20, plain, (![A_18, B_19]: (v1_relat_1(k7_relat_1(A_18, B_19)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 24.44/15.88  tff(c_28, plain, (![A_29]: (k10_relat_1(A_29, k2_relat_1(A_29))=k1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 24.44/15.88  tff(c_885, plain, (![B_101, A_102]: (r1_tarski(k10_relat_1(B_101, A_102), k10_relat_1(B_101, k2_relat_1(B_101))) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_80])).
% 24.44/15.88  tff(c_6685, plain, (![A_203]: (r1_tarski(k1_relat_1(A_203), k10_relat_1(A_203, k2_relat_1(A_203))) | ~v1_relat_1(A_203) | ~v1_relat_1(A_203))), inference(superposition, [status(thm), theory('equality')], [c_28, c_885])).
% 24.44/15.88  tff(c_40, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 24.44/15.88  tff(c_91, plain, (![A_44, B_45]: (k2_xboole_0(A_44, B_45)=B_45 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 24.44/15.88  tff(c_98, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_91])).
% 24.44/15.88  tff(c_189, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(k2_xboole_0(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_41])).
% 24.44/15.88  tff(c_192, plain, (![C_58]: (r1_tarski('#skF_1', C_58) | ~r1_tarski(k1_relat_1('#skF_2'), C_58))), inference(superposition, [status(thm), theory('equality')], [c_98, c_189])).
% 24.44/15.88  tff(c_6696, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6685, c_192])).
% 24.44/15.88  tff(c_6719, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6696])).
% 24.44/15.88  tff(c_18, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 24.44/15.88  tff(c_6736, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))='#skF_1'), inference(resolution, [status(thm)], [c_6719, c_18])).
% 24.44/15.88  tff(c_36, plain, (![A_35, C_37, B_36]: (k3_xboole_0(A_35, k10_relat_1(C_37, B_36))=k10_relat_1(k7_relat_1(C_37, A_35), B_36) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.44/15.88  tff(c_6804, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6736, c_36])).
% 24.44/15.88  tff(c_6868, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6804])).
% 24.44/15.88  tff(c_26, plain, (![B_28, A_27]: (r1_tarski(k10_relat_1(B_28, A_27), k1_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 24.44/15.88  tff(c_7179, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6868, c_26])).
% 24.44/15.88  tff(c_97091, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_7179])).
% 24.44/15.88  tff(c_97556, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_97091])).
% 24.44/15.88  tff(c_97560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_97556])).
% 24.44/15.88  tff(c_97562, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_7179])).
% 24.44/15.88  tff(c_97561, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_7179])).
% 24.44/15.88  tff(c_172, plain, (![B_55, A_56]: (r1_tarski(k1_relat_1(k7_relat_1(B_55, A_56)), A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.44/15.88  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.44/15.88  tff(c_184, plain, (![B_55, A_56]: (k1_relat_1(k7_relat_1(B_55, A_56))=A_56 | ~r1_tarski(A_56, k1_relat_1(k7_relat_1(B_55, A_56))) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_172, c_4])).
% 24.44/15.88  tff(c_97581, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_97561, c_184])).
% 24.44/15.88  tff(c_97605, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_97581])).
% 24.44/15.88  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.44/15.88  tff(c_34, plain, (![A_34]: (k7_relat_1(A_34, k1_relat_1(A_34))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 24.44/15.88  tff(c_585, plain, (![B_86, A_87]: (k2_relat_1(k7_relat_1(B_86, A_87))=k9_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 24.44/15.88  tff(c_597, plain, (![A_34]: (k9_relat_1(A_34, k1_relat_1(A_34))=k2_relat_1(A_34) | ~v1_relat_1(A_34) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_34, c_585])).
% 24.44/15.88  tff(c_97690, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_97605, c_597])).
% 24.44/15.88  tff(c_97758, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_97562, c_97562, c_97690])).
% 24.44/15.88  tff(c_24, plain, (![A_22, C_26, B_25]: (k9_relat_1(k7_relat_1(A_22, C_26), B_25)=k9_relat_1(A_22, B_25) | ~r1_tarski(B_25, C_26) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.44/15.88  tff(c_99957, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_97758, c_24])).
% 24.44/15.88  tff(c_99968, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_99957])).
% 24.44/15.88  tff(c_100017, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99968, c_28])).
% 24.44/15.88  tff(c_100053, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_97562, c_97605, c_100017])).
% 24.44/15.88  tff(c_1140, plain, (![A_113, C_114, B_115]: (k3_xboole_0(A_113, k10_relat_1(C_114, B_115))=k10_relat_1(k7_relat_1(C_114, A_113), B_115) | ~v1_relat_1(C_114))), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.44/15.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.44/15.88  tff(c_8774, plain, (![C_223, B_224, A_225]: (k3_xboole_0(k10_relat_1(C_223, B_224), A_225)=k10_relat_1(k7_relat_1(C_223, A_225), B_224) | ~v1_relat_1(C_223))), inference(superposition, [status(thm), theory('equality')], [c_1140, c_2])).
% 24.44/15.88  tff(c_349, plain, (![A_73, B_74, C_75]: (r1_tarski(A_73, B_74) | ~r1_tarski(A_73, k3_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 24.44/15.88  tff(c_382, plain, (![B_74, C_75]: (r1_tarski(k3_xboole_0(B_74, C_75), B_74))), inference(resolution, [status(thm)], [c_8, c_349])).
% 24.44/15.88  tff(c_8952, plain, (![C_223, A_225, B_224]: (r1_tarski(k10_relat_1(k7_relat_1(C_223, A_225), B_224), k10_relat_1(C_223, B_224)) | ~v1_relat_1(C_223))), inference(superposition, [status(thm), theory('equality')], [c_8774, c_382])).
% 24.44/15.88  tff(c_100162, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100053, c_8952])).
% 24.44/15.88  tff(c_100279, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_100162])).
% 24.44/15.88  tff(c_100281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_100279])).
% 24.44/15.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.44/15.88  
% 24.44/15.88  Inference rules
% 24.44/15.88  ----------------------
% 24.44/15.88  #Ref     : 0
% 24.44/15.88  #Sup     : 25428
% 24.44/15.88  #Fact    : 0
% 24.44/15.88  #Define  : 0
% 24.44/15.88  #Split   : 2
% 24.44/15.88  #Chain   : 0
% 24.44/15.88  #Close   : 0
% 24.44/15.88  
% 24.44/15.88  Ordering : KBO
% 24.44/15.88  
% 24.44/15.88  Simplification rules
% 24.44/15.88  ----------------------
% 24.44/15.88  #Subsume      : 4546
% 24.44/15.88  #Demod        : 15272
% 24.44/15.88  #Tautology    : 9987
% 24.44/15.88  #SimpNegUnit  : 3
% 24.44/15.88  #BackRed      : 14
% 24.44/15.88  
% 24.44/15.88  #Partial instantiations: 0
% 24.44/15.88  #Strategies tried      : 1
% 24.44/15.88  
% 24.44/15.88  Timing (in seconds)
% 24.44/15.88  ----------------------
% 24.44/15.88  Preprocessing        : 0.34
% 24.44/15.88  Parsing              : 0.19
% 24.44/15.88  CNF conversion       : 0.02
% 24.44/15.88  Main loop            : 14.73
% 24.44/15.88  Inferencing          : 1.76
% 24.44/15.88  Reduction            : 7.59
% 24.44/15.88  Demodulation         : 6.84
% 24.44/15.88  BG Simplification    : 0.23
% 24.44/15.88  Subsumption          : 4.37
% 24.44/15.88  Abstraction          : 0.38
% 24.44/15.88  MUC search           : 0.00
% 24.44/15.88  Cooper               : 0.00
% 24.44/15.88  Total                : 15.11
% 24.44/15.88  Index Insertion      : 0.00
% 24.44/15.88  Index Deletion       : 0.00
% 24.44/15.88  Index Matching       : 0.00
% 24.44/15.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
