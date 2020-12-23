%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:43 EST 2020

% Result     : Theorem 25.25s
% Output     : CNFRefutation 25.25s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 273 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          :  121 ( 481 expanded)
%              Number of equality atoms :   34 ( 116 expanded)
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

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_99,axiom,(
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

tff(f_109,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_44,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_44,C_46,B_45] :
      ( k3_xboole_0(A_44,k10_relat_1(C_46,B_45)) = k10_relat_1(k7_relat_1(C_46,A_44),B_45)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    ! [A_31] :
      ( k10_relat_1(A_31,k2_relat_1(A_31)) = k1_relat_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1167,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(k10_relat_1(B_122,A_123),k10_relat_1(B_122,k2_relat_1(B_122)))
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7952,plain,(
    ! [A_237] :
      ( r1_tarski(k1_relat_1(A_237),k10_relat_1(A_237,k2_relat_1(A_237)))
      | ~ v1_relat_1(A_237)
      | ~ v1_relat_1(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1167])).

tff(c_46,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_104,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_104])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_217,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(k3_xboole_0(A_71,C_72),B_73)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_313,plain,(
    ! [B_77,A_78,B_79] :
      ( r1_tarski(k3_xboole_0(B_77,A_78),B_79)
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_217])).

tff(c_327,plain,(
    ! [B_79] :
      ( r1_tarski('#skF_1',B_79)
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_313])).

tff(c_7976,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7952,c_327])).

tff(c_8001,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7976])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8025,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8001,c_16])).

tff(c_8139,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_8025])).

tff(c_8175,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8139])).

tff(c_28,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k10_relat_1(B_30,A_29),k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8346,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8175,c_28])).

tff(c_93760,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_8346])).

tff(c_93763,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_93760])).

tff(c_93767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_93763])).

tff(c_93769,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_8346])).

tff(c_93768,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8346])).

tff(c_199,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_67,A_68)),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_205,plain,(
    ! [B_67,A_68] :
      ( k1_relat_1(k7_relat_1(B_67,A_68)) = A_68
      | ~ r1_tarski(A_68,k1_relat_1(k7_relat_1(B_67,A_68)))
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_93780,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_93768,c_205])).

tff(c_93806,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_93780])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_989,plain,(
    ! [B_109,A_110] :
      ( k7_relat_1(B_109,A_110) = B_109
      | ~ r1_tarski(k1_relat_1(B_109),A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1009,plain,(
    ! [B_111] :
      ( k7_relat_1(B_111,k1_relat_1(B_111)) = B_111
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_8,c_989])).

tff(c_24,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1015,plain,(
    ! [B_111] :
      ( k9_relat_1(B_111,k1_relat_1(B_111)) = k2_relat_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_24])).

tff(c_93860,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93806,c_1015])).

tff(c_93952,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93769,c_93769,c_93860])).

tff(c_26,plain,(
    ! [A_24,C_28,B_27] :
      ( k9_relat_1(k7_relat_1(A_24,C_28),B_27) = k9_relat_1(A_24,B_27)
      | ~ r1_tarski(B_27,C_28)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107945,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93952,c_26])).

tff(c_107956,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8,c_107945])).

tff(c_108004,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_107956,c_30])).

tff(c_108040,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93769,c_93806,c_108004])).

tff(c_1932,plain,(
    ! [A_147,C_148,B_149] :
      ( k3_xboole_0(A_147,k10_relat_1(C_148,B_149)) = k10_relat_1(k7_relat_1(C_148,A_147),B_149)
      | ~ v1_relat_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_53,plain,(
    ! [B_52,A_53] : k3_xboole_0(B_52,A_53) = k3_xboole_0(A_53,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [B_52,A_53] : r1_tarski(k3_xboole_0(B_52,A_53),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_12])).

tff(c_2014,plain,(
    ! [C_148,A_147,B_149] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_148,A_147),B_149),k10_relat_1(C_148,B_149))
      | ~ v1_relat_1(C_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1932,c_68])).

tff(c_108411,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_108040,c_2014])).

tff(c_108507,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_108411])).

tff(c_108509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_108507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:13:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.25/16.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.25/16.74  
% 25.25/16.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.25/16.74  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 25.25/16.74  
% 25.25/16.74  %Foreground sorts:
% 25.25/16.74  
% 25.25/16.74  
% 25.25/16.74  %Background operators:
% 25.25/16.74  
% 25.25/16.74  
% 25.25/16.74  %Foreground operators:
% 25.25/16.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.25/16.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 25.25/16.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.25/16.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 25.25/16.74  tff('#skF_2', type, '#skF_2': $i).
% 25.25/16.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 25.25/16.74  tff('#skF_1', type, '#skF_1': $i).
% 25.25/16.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.25/16.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 25.25/16.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 25.25/16.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.25/16.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.25/16.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.25/16.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 25.25/16.74  
% 25.25/16.76  tff(f_120, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 25.25/16.76  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 25.25/16.76  tff(f_113, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 25.25/16.76  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 25.25/16.76  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 25.25/16.76  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 25.25/16.76  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 25.25/16.76  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 25.25/16.76  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 25.25/16.76  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 25.25/16.76  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 25.25/16.76  tff(f_109, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 25.25/16.76  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 25.25/16.76  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 25.25/16.76  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 25.25/16.76  tff(c_44, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 25.25/16.76  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 25.25/16.76  tff(c_22, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 25.25/16.76  tff(c_42, plain, (![A_44, C_46, B_45]: (k3_xboole_0(A_44, k10_relat_1(C_46, B_45))=k10_relat_1(k7_relat_1(C_46, A_44), B_45) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_113])).
% 25.25/16.76  tff(c_30, plain, (![A_31]: (k10_relat_1(A_31, k2_relat_1(A_31))=k1_relat_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 25.25/16.76  tff(c_1167, plain, (![B_122, A_123]: (r1_tarski(k10_relat_1(B_122, A_123), k10_relat_1(B_122, k2_relat_1(B_122))) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_84])).
% 25.25/16.76  tff(c_7952, plain, (![A_237]: (r1_tarski(k1_relat_1(A_237), k10_relat_1(A_237, k2_relat_1(A_237))) | ~v1_relat_1(A_237) | ~v1_relat_1(A_237))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1167])).
% 25.25/16.76  tff(c_46, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 25.25/16.76  tff(c_104, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.25/16.76  tff(c_128, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_46, c_104])).
% 25.25/16.76  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 25.25/16.76  tff(c_217, plain, (![A_71, C_72, B_73]: (r1_tarski(k3_xboole_0(A_71, C_72), B_73) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.25/16.76  tff(c_313, plain, (![B_77, A_78, B_79]: (r1_tarski(k3_xboole_0(B_77, A_78), B_79) | ~r1_tarski(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_2, c_217])).
% 25.25/16.76  tff(c_327, plain, (![B_79]: (r1_tarski('#skF_1', B_79) | ~r1_tarski(k1_relat_1('#skF_2'), B_79))), inference(superposition, [status(thm), theory('equality')], [c_128, c_313])).
% 25.25/16.76  tff(c_7976, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_7952, c_327])).
% 25.25/16.76  tff(c_8001, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7976])).
% 25.25/16.76  tff(c_16, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.25/16.76  tff(c_8025, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))='#skF_1'), inference(resolution, [status(thm)], [c_8001, c_16])).
% 25.25/16.76  tff(c_8139, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_8025])).
% 25.25/16.76  tff(c_8175, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8139])).
% 25.25/16.76  tff(c_28, plain, (![B_30, A_29]: (r1_tarski(k10_relat_1(B_30, A_29), k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_76])).
% 25.25/16.76  tff(c_8346, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8175, c_28])).
% 25.25/16.76  tff(c_93760, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_8346])).
% 25.25/16.76  tff(c_93763, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_93760])).
% 25.25/16.76  tff(c_93767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_93763])).
% 25.25/16.76  tff(c_93769, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_8346])).
% 25.25/16.76  tff(c_93768, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_8346])).
% 25.25/16.76  tff(c_199, plain, (![B_67, A_68]: (r1_tarski(k1_relat_1(k7_relat_1(B_67, A_68)), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_99])).
% 25.25/16.76  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.25/16.76  tff(c_205, plain, (![B_67, A_68]: (k1_relat_1(k7_relat_1(B_67, A_68))=A_68 | ~r1_tarski(A_68, k1_relat_1(k7_relat_1(B_67, A_68))) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_199, c_4])).
% 25.25/16.76  tff(c_93780, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_93768, c_205])).
% 25.25/16.76  tff(c_93806, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_93780])).
% 25.25/16.76  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.25/16.76  tff(c_989, plain, (![B_109, A_110]: (k7_relat_1(B_109, A_110)=B_109 | ~r1_tarski(k1_relat_1(B_109), A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_109])).
% 25.25/16.76  tff(c_1009, plain, (![B_111]: (k7_relat_1(B_111, k1_relat_1(B_111))=B_111 | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_8, c_989])).
% 25.25/16.76  tff(c_24, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 25.25/16.76  tff(c_1015, plain, (![B_111]: (k9_relat_1(B_111, k1_relat_1(B_111))=k2_relat_1(B_111) | ~v1_relat_1(B_111) | ~v1_relat_1(B_111))), inference(superposition, [status(thm), theory('equality')], [c_1009, c_24])).
% 25.25/16.76  tff(c_93860, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_93806, c_1015])).
% 25.25/16.76  tff(c_93952, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93769, c_93769, c_93860])).
% 25.25/16.76  tff(c_26, plain, (![A_24, C_28, B_27]: (k9_relat_1(k7_relat_1(A_24, C_28), B_27)=k9_relat_1(A_24, B_27) | ~r1_tarski(B_27, C_28) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 25.25/16.76  tff(c_107945, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93952, c_26])).
% 25.25/16.76  tff(c_107956, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8, c_107945])).
% 25.25/16.76  tff(c_108004, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_107956, c_30])).
% 25.25/16.76  tff(c_108040, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93769, c_93806, c_108004])).
% 25.25/16.76  tff(c_1932, plain, (![A_147, C_148, B_149]: (k3_xboole_0(A_147, k10_relat_1(C_148, B_149))=k10_relat_1(k7_relat_1(C_148, A_147), B_149) | ~v1_relat_1(C_148))), inference(cnfTransformation, [status(thm)], [f_113])).
% 25.25/16.76  tff(c_53, plain, (![B_52, A_53]: (k3_xboole_0(B_52, A_53)=k3_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 25.25/16.76  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.25/16.76  tff(c_68, plain, (![B_52, A_53]: (r1_tarski(k3_xboole_0(B_52, A_53), A_53))), inference(superposition, [status(thm), theory('equality')], [c_53, c_12])).
% 25.25/16.76  tff(c_2014, plain, (![C_148, A_147, B_149]: (r1_tarski(k10_relat_1(k7_relat_1(C_148, A_147), B_149), k10_relat_1(C_148, B_149)) | ~v1_relat_1(C_148))), inference(superposition, [status(thm), theory('equality')], [c_1932, c_68])).
% 25.25/16.76  tff(c_108411, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_108040, c_2014])).
% 25.25/16.76  tff(c_108507, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_108411])).
% 25.25/16.76  tff(c_108509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_108507])).
% 25.25/16.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.25/16.76  
% 25.25/16.76  Inference rules
% 25.25/16.76  ----------------------
% 25.25/16.76  #Ref     : 0
% 25.25/16.76  #Sup     : 27395
% 25.25/16.76  #Fact    : 0
% 25.25/16.76  #Define  : 0
% 25.25/16.76  #Split   : 5
% 25.25/16.76  #Chain   : 0
% 25.25/16.76  #Close   : 0
% 25.25/16.76  
% 25.25/16.76  Ordering : KBO
% 25.25/16.76  
% 25.25/16.76  Simplification rules
% 25.25/16.76  ----------------------
% 25.25/16.76  #Subsume      : 6364
% 25.25/16.76  #Demod        : 17427
% 25.25/16.76  #Tautology    : 11483
% 25.25/16.76  #SimpNegUnit  : 3
% 25.25/16.76  #BackRed      : 10
% 25.25/16.76  
% 25.25/16.76  #Partial instantiations: 0
% 25.25/16.76  #Strategies tried      : 1
% 25.25/16.76  
% 25.25/16.76  Timing (in seconds)
% 25.25/16.76  ----------------------
% 25.25/16.76  Preprocessing        : 0.32
% 25.25/16.76  Parsing              : 0.17
% 25.25/16.76  CNF conversion       : 0.02
% 25.25/16.76  Main loop            : 15.68
% 25.25/16.76  Inferencing          : 1.87
% 25.25/16.76  Reduction            : 7.79
% 25.25/16.76  Demodulation         : 6.92
% 25.25/16.76  BG Simplification    : 0.22
% 25.25/16.76  Subsumption          : 5.01
% 25.25/16.76  Abstraction          : 0.38
% 25.25/16.76  MUC search           : 0.00
% 25.25/16.76  Cooper               : 0.00
% 25.25/16.76  Total                : 16.03
% 25.25/16.76  Index Insertion      : 0.00
% 25.25/16.76  Index Deletion       : 0.00
% 25.25/16.76  Index Matching       : 0.00
% 25.25/16.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
