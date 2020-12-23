%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:29 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 138 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :   97 ( 238 expanded)
%              Number of equality atoms :   31 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_34,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [A_40] :
      ( k10_relat_1(A_40,k2_relat_1(A_40)) = k1_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,(
    ! [A_11] :
      ( k10_relat_1(k6_relat_1(A_11),A_11) = k1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_118,plain,(
    ! [A_11] : k10_relat_1(k6_relat_1(A_11),A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_111])).

tff(c_22,plain,(
    ! [A_12] : v1_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_544,plain,(
    ! [B_78,A_79] :
      ( k9_relat_1(B_78,k10_relat_1(B_78,A_79)) = A_79
      | ~ r1_tarski(A_79,k2_relat_1(B_78))
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_561,plain,(
    ! [A_11,A_79] :
      ( k9_relat_1(k6_relat_1(A_11),k10_relat_1(k6_relat_1(A_11),A_79)) = A_79
      | ~ r1_tarski(A_79,A_11)
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_544])).

tff(c_573,plain,(
    ! [A_80,A_81] :
      ( k9_relat_1(k6_relat_1(A_80),k10_relat_1(k6_relat_1(A_80),A_81)) = A_81
      | ~ r1_tarski(A_81,A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_561])).

tff(c_585,plain,(
    ! [A_11] :
      ( k9_relat_1(k6_relat_1(A_11),A_11) = A_11
      | ~ r1_tarski(A_11,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_573])).

tff(c_595,plain,(
    ! [A_11] : k9_relat_1(k6_relat_1(A_11),A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_585])).

tff(c_1005,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(A_104,k10_relat_1(C_105,B_106))
      | ~ r1_tarski(k9_relat_1(C_105,A_104),B_106)
      | ~ r1_tarski(A_104,k1_relat_1(C_105))
      | ~ v1_funct_1(C_105)
      | ~ v1_relat_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1020,plain,(
    ! [A_11,B_106] :
      ( r1_tarski(A_11,k10_relat_1(k6_relat_1(A_11),B_106))
      | ~ r1_tarski(A_11,B_106)
      | ~ r1_tarski(A_11,k1_relat_1(k6_relat_1(A_11)))
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_1005])).

tff(c_1414,plain,(
    ! [A_124,B_125] :
      ( r1_tarski(A_124,k10_relat_1(k6_relat_1(A_124),B_125))
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_6,c_16,c_1020])).

tff(c_72,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(k10_relat_1(B_34,A_35),k1_relat_1(B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [A_11,A_35] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_11),A_35),A_11)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_72])).

tff(c_77,plain,(
    ! [A_11,A_35] : r1_tarski(k10_relat_1(k6_relat_1(A_11),A_35),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_75])).

tff(c_79,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_11,A_35] :
      ( k10_relat_1(k6_relat_1(A_11),A_35) = A_11
      | ~ r1_tarski(A_11,k10_relat_1(k6_relat_1(A_11),A_35)) ) ),
    inference(resolution,[status(thm)],[c_77,c_79])).

tff(c_1490,plain,(
    ! [A_128,B_129] :
      ( k10_relat_1(k6_relat_1(A_128),B_129) = A_128
      | ~ r1_tarski(A_128,B_129) ) ),
    inference(resolution,[status(thm)],[c_1414,c_88])).

tff(c_796,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,k9_relat_1(B_95,k1_relat_1(B_95))) = k9_relat_1(B_95,k10_relat_1(B_95,A_94))
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_808,plain,(
    ! [A_11,A_94] :
      ( k9_relat_1(k6_relat_1(A_11),k10_relat_1(k6_relat_1(A_11),A_94)) = k3_xboole_0(A_94,k9_relat_1(k6_relat_1(A_11),A_11))
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_796])).

tff(c_812,plain,(
    ! [A_11,A_94] : k9_relat_1(k6_relat_1(A_11),k10_relat_1(k6_relat_1(A_11),A_94)) = k3_xboole_0(A_94,A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_595,c_808])).

tff(c_1521,plain,(
    ! [A_128,B_129] :
      ( k9_relat_1(k6_relat_1(A_128),A_128) = k3_xboole_0(B_129,A_128)
      | ~ r1_tarski(A_128,B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1490,c_812])).

tff(c_1663,plain,(
    ! [B_130,A_131] :
      ( k3_xboole_0(B_130,A_131) = A_131
      | ~ r1_tarski(A_131,B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_1521])).

tff(c_1734,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1663])).

tff(c_24,plain,(
    ! [A_13,C_15,B_14] :
      ( k3_xboole_0(A_13,k10_relat_1(C_15,B_14)) = k10_relat_1(k7_relat_1(C_15,A_13),B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1755,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1734,c_24])).

tff(c_1766,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1755])).

tff(c_1768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.65  
% 3.55/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.65  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.55/1.65  
% 3.55/1.65  %Foreground sorts:
% 3.55/1.65  
% 3.55/1.65  
% 3.55/1.65  %Background operators:
% 3.55/1.65  
% 3.55/1.65  
% 3.55/1.65  %Foreground operators:
% 3.55/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.55/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.55/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.65  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.55/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.55/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/1.65  
% 3.55/1.67  tff(f_99, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.55/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.55/1.67  tff(f_55, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.55/1.67  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.55/1.67  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.55/1.67  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 3.55/1.67  tff(f_89, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 3.55/1.67  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 3.55/1.67  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 3.55/1.67  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.55/1.67  tff(c_34, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.55/1.67  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.55/1.67  tff(c_36, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.55/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.67  tff(c_20, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.67  tff(c_16, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.55/1.67  tff(c_18, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.55/1.67  tff(c_95, plain, (![A_40]: (k10_relat_1(A_40, k2_relat_1(A_40))=k1_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.67  tff(c_111, plain, (![A_11]: (k10_relat_1(k6_relat_1(A_11), A_11)=k1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_95])).
% 3.55/1.67  tff(c_118, plain, (![A_11]: (k10_relat_1(k6_relat_1(A_11), A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_111])).
% 3.55/1.67  tff(c_22, plain, (![A_12]: (v1_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.67  tff(c_544, plain, (![B_78, A_79]: (k9_relat_1(B_78, k10_relat_1(B_78, A_79))=A_79 | ~r1_tarski(A_79, k2_relat_1(B_78)) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.67  tff(c_561, plain, (![A_11, A_79]: (k9_relat_1(k6_relat_1(A_11), k10_relat_1(k6_relat_1(A_11), A_79))=A_79 | ~r1_tarski(A_79, A_11) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_544])).
% 3.55/1.67  tff(c_573, plain, (![A_80, A_81]: (k9_relat_1(k6_relat_1(A_80), k10_relat_1(k6_relat_1(A_80), A_81))=A_81 | ~r1_tarski(A_81, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_561])).
% 3.55/1.67  tff(c_585, plain, (![A_11]: (k9_relat_1(k6_relat_1(A_11), A_11)=A_11 | ~r1_tarski(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_118, c_573])).
% 3.55/1.67  tff(c_595, plain, (![A_11]: (k9_relat_1(k6_relat_1(A_11), A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_585])).
% 3.55/1.67  tff(c_1005, plain, (![A_104, C_105, B_106]: (r1_tarski(A_104, k10_relat_1(C_105, B_106)) | ~r1_tarski(k9_relat_1(C_105, A_104), B_106) | ~r1_tarski(A_104, k1_relat_1(C_105)) | ~v1_funct_1(C_105) | ~v1_relat_1(C_105))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.55/1.67  tff(c_1020, plain, (![A_11, B_106]: (r1_tarski(A_11, k10_relat_1(k6_relat_1(A_11), B_106)) | ~r1_tarski(A_11, B_106) | ~r1_tarski(A_11, k1_relat_1(k6_relat_1(A_11))) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_595, c_1005])).
% 3.55/1.67  tff(c_1414, plain, (![A_124, B_125]: (r1_tarski(A_124, k10_relat_1(k6_relat_1(A_124), B_125)) | ~r1_tarski(A_124, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_6, c_16, c_1020])).
% 3.55/1.67  tff(c_72, plain, (![B_34, A_35]: (r1_tarski(k10_relat_1(B_34, A_35), k1_relat_1(B_34)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.55/1.67  tff(c_75, plain, (![A_11, A_35]: (r1_tarski(k10_relat_1(k6_relat_1(A_11), A_35), A_11) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_72])).
% 3.55/1.67  tff(c_77, plain, (![A_11, A_35]: (r1_tarski(k10_relat_1(k6_relat_1(A_11), A_35), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_75])).
% 3.55/1.67  tff(c_79, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.67  tff(c_88, plain, (![A_11, A_35]: (k10_relat_1(k6_relat_1(A_11), A_35)=A_11 | ~r1_tarski(A_11, k10_relat_1(k6_relat_1(A_11), A_35)))), inference(resolution, [status(thm)], [c_77, c_79])).
% 3.55/1.67  tff(c_1490, plain, (![A_128, B_129]: (k10_relat_1(k6_relat_1(A_128), B_129)=A_128 | ~r1_tarski(A_128, B_129))), inference(resolution, [status(thm)], [c_1414, c_88])).
% 3.55/1.67  tff(c_796, plain, (![A_94, B_95]: (k3_xboole_0(A_94, k9_relat_1(B_95, k1_relat_1(B_95)))=k9_relat_1(B_95, k10_relat_1(B_95, A_94)) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.55/1.67  tff(c_808, plain, (![A_11, A_94]: (k9_relat_1(k6_relat_1(A_11), k10_relat_1(k6_relat_1(A_11), A_94))=k3_xboole_0(A_94, k9_relat_1(k6_relat_1(A_11), A_11)) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_796])).
% 3.55/1.67  tff(c_812, plain, (![A_11, A_94]: (k9_relat_1(k6_relat_1(A_11), k10_relat_1(k6_relat_1(A_11), A_94))=k3_xboole_0(A_94, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_595, c_808])).
% 3.55/1.67  tff(c_1521, plain, (![A_128, B_129]: (k9_relat_1(k6_relat_1(A_128), A_128)=k3_xboole_0(B_129, A_128) | ~r1_tarski(A_128, B_129))), inference(superposition, [status(thm), theory('equality')], [c_1490, c_812])).
% 3.55/1.67  tff(c_1663, plain, (![B_130, A_131]: (k3_xboole_0(B_130, A_131)=A_131 | ~r1_tarski(A_131, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_595, c_1521])).
% 3.55/1.67  tff(c_1734, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_1663])).
% 3.55/1.67  tff(c_24, plain, (![A_13, C_15, B_14]: (k3_xboole_0(A_13, k10_relat_1(C_15, B_14))=k10_relat_1(k7_relat_1(C_15, A_13), B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.67  tff(c_1755, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1734, c_24])).
% 3.55/1.67  tff(c_1766, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1755])).
% 3.55/1.67  tff(c_1768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1766])).
% 3.55/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.67  
% 3.55/1.67  Inference rules
% 3.55/1.67  ----------------------
% 3.55/1.67  #Ref     : 0
% 3.55/1.67  #Sup     : 379
% 3.55/1.67  #Fact    : 0
% 3.55/1.67  #Define  : 0
% 3.55/1.67  #Split   : 1
% 3.55/1.67  #Chain   : 0
% 3.55/1.67  #Close   : 0
% 3.55/1.67  
% 3.55/1.67  Ordering : KBO
% 3.55/1.67  
% 3.55/1.67  Simplification rules
% 3.55/1.67  ----------------------
% 3.55/1.67  #Subsume      : 22
% 3.55/1.67  #Demod        : 299
% 3.55/1.67  #Tautology    : 166
% 3.55/1.67  #SimpNegUnit  : 1
% 3.55/1.67  #BackRed      : 4
% 3.55/1.67  
% 3.55/1.67  #Partial instantiations: 0
% 3.55/1.67  #Strategies tried      : 1
% 3.55/1.67  
% 3.55/1.67  Timing (in seconds)
% 3.55/1.67  ----------------------
% 3.55/1.67  Preprocessing        : 0.31
% 3.55/1.67  Parsing              : 0.17
% 3.55/1.67  CNF conversion       : 0.02
% 3.55/1.67  Main loop            : 0.57
% 3.55/1.67  Inferencing          : 0.19
% 3.55/1.67  Reduction            : 0.20
% 3.55/1.67  Demodulation         : 0.16
% 3.55/1.67  BG Simplification    : 0.03
% 3.55/1.67  Subsumption          : 0.10
% 3.55/1.67  Abstraction          : 0.03
% 3.55/1.67  MUC search           : 0.00
% 3.55/1.67  Cooper               : 0.00
% 3.55/1.67  Total                : 0.92
% 3.55/1.67  Index Insertion      : 0.00
% 3.55/1.67  Index Deletion       : 0.00
% 3.55/1.67  Index Matching       : 0.00
% 3.55/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
