%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:41 EST 2020

% Result     : Theorem 7.00s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 334 expanded)
%              Number of leaves         :   28 ( 122 expanded)
%              Depth                    :   19
%              Number of atoms          :  109 ( 559 expanded)
%              Number of equality atoms :   41 ( 208 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_32,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_300,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(A_66,k3_xboole_0(B_67,C_68))
      | ~ r1_tarski(A_66,C_68)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_110,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_74])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_133,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_14])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_148,plain,(
    ! [B_44,A_45] : r1_tarski(k3_xboole_0(B_44,A_45),A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_8])).

tff(c_182,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_191,plain,(
    ! [B_44,A_45] :
      ( k3_xboole_0(B_44,A_45) = A_45
      | ~ r1_tarski(A_45,k3_xboole_0(B_44,A_45)) ) ),
    inference(resolution,[status(thm)],[c_148,c_182])).

tff(c_308,plain,(
    ! [B_67,C_68] :
      ( k3_xboole_0(B_67,C_68) = C_68
      | ~ r1_tarski(C_68,C_68)
      | ~ r1_tarski(C_68,B_67) ) ),
    inference(resolution,[status(thm)],[c_300,c_191])).

tff(c_453,plain,(
    ! [B_72,C_73] :
      ( k3_xboole_0(B_72,C_73) = C_73
      | ~ r1_tarski(C_73,B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_308])).

tff(c_480,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_453])).

tff(c_26,plain,(
    ! [B_26,A_25] :
      ( k3_xboole_0(k1_relat_1(B_26),A_25) = k1_relat_1(k7_relat_1(B_26,A_25))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_552,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_26])).

tff(c_589,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_552])).

tff(c_28,plain,(
    ! [A_27] :
      ( k7_relat_1(A_27,k1_relat_1(A_27)) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_620,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_28])).

tff(c_629,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_620])).

tff(c_632,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_629])).

tff(c_636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_632])).

tff(c_638,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_620])).

tff(c_200,plain,(
    ! [B_50,A_51] :
      ( k2_relat_1(k7_relat_1(B_50,A_51)) = k9_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1853,plain,(
    ! [A_105] :
      ( k9_relat_1(A_105,k1_relat_1(A_105)) = k2_relat_1(A_105)
      | ~ v1_relat_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_200])).

tff(c_1873,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_1853])).

tff(c_1877,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_638,c_1873])).

tff(c_22,plain,(
    ! [A_19,C_23,B_22] :
      ( k9_relat_1(k7_relat_1(A_19,C_23),B_22) = k9_relat_1(A_19,B_22)
      | ~ r1_tarski(B_22,C_23)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1884,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1877,c_22])).

tff(c_1891,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6,c_1884])).

tff(c_192,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_182])).

tff(c_316,plain,(
    ! [B_67,C_68] :
      ( k3_xboole_0(B_67,C_68) = B_67
      | ~ r1_tarski(B_67,C_68)
      | ~ r1_tarski(B_67,B_67) ) ),
    inference(resolution,[status(thm)],[c_300,c_192])).

tff(c_341,plain,(
    ! [B_69,C_70] :
      ( k3_xboole_0(B_69,C_70) = B_69
      | ~ r1_tarski(B_69,C_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_316])).

tff(c_371,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_341])).

tff(c_637,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_620])).

tff(c_24,plain,(
    ! [A_24] :
      ( k10_relat_1(A_24,k2_relat_1(A_24)) = k1_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_483,plain,(
    ! [A_74,C_75,B_76] :
      ( k3_xboole_0(A_74,k10_relat_1(C_75,B_76)) = k10_relat_1(k7_relat_1(C_75,A_74),B_76)
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1921,plain,(
    ! [A_106,A_107] :
      ( k10_relat_1(k7_relat_1(A_106,A_107),k2_relat_1(A_106)) = k3_xboole_0(A_107,k1_relat_1(A_106))
      | ~ v1_relat_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_483])).

tff(c_1943,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_1921])).

tff(c_1961,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_638,c_1891,c_371,c_589,c_1943])).

tff(c_8063,plain,(
    ! [C_197,A_198,B_199] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_197,A_198),B_199),k10_relat_1(C_197,B_199))
      | ~ v1_relat_1(C_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_148])).

tff(c_8092,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1961,c_8063])).

tff(c_8125,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8092])).

tff(c_8127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.00/2.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.60  
% 7.00/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.60  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.00/2.60  
% 7.00/2.60  %Foreground sorts:
% 7.00/2.60  
% 7.00/2.60  
% 7.00/2.60  %Background operators:
% 7.00/2.60  
% 7.00/2.60  
% 7.00/2.60  %Foreground operators:
% 7.00/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.00/2.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.00/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.00/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.00/2.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.00/2.60  tff('#skF_2', type, '#skF_2': $i).
% 7.00/2.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.00/2.60  tff('#skF_1', type, '#skF_1': $i).
% 7.00/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.00/2.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.00/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.00/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.00/2.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.00/2.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.00/2.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.31/2.60  
% 7.31/2.62  tff(f_87, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 7.31/2.62  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.31/2.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.31/2.62  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 7.31/2.62  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.31/2.62  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.31/2.62  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.31/2.62  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 7.31/2.62  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 7.31/2.62  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 7.31/2.62  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 7.31/2.62  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 7.31/2.62  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 7.31/2.62  tff(c_32, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.31/2.62  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.31/2.62  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.31/2.62  tff(c_34, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.31/2.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.31/2.62  tff(c_300, plain, (![A_66, B_67, C_68]: (r1_tarski(A_66, k3_xboole_0(B_67, C_68)) | ~r1_tarski(A_66, C_68) | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.31/2.62  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.31/2.62  tff(c_74, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.62  tff(c_110, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_12, c_74])).
% 7.31/2.62  tff(c_14, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.62  tff(c_133, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_110, c_14])).
% 7.31/2.62  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.31/2.62  tff(c_148, plain, (![B_44, A_45]: (r1_tarski(k3_xboole_0(B_44, A_45), A_45))), inference(superposition, [status(thm), theory('equality')], [c_133, c_8])).
% 7.31/2.62  tff(c_182, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.31/2.62  tff(c_191, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=A_45 | ~r1_tarski(A_45, k3_xboole_0(B_44, A_45)))), inference(resolution, [status(thm)], [c_148, c_182])).
% 7.31/2.62  tff(c_308, plain, (![B_67, C_68]: (k3_xboole_0(B_67, C_68)=C_68 | ~r1_tarski(C_68, C_68) | ~r1_tarski(C_68, B_67))), inference(resolution, [status(thm)], [c_300, c_191])).
% 7.31/2.62  tff(c_453, plain, (![B_72, C_73]: (k3_xboole_0(B_72, C_73)=C_73 | ~r1_tarski(C_73, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_308])).
% 7.31/2.62  tff(c_480, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_34, c_453])).
% 7.31/2.62  tff(c_26, plain, (![B_26, A_25]: (k3_xboole_0(k1_relat_1(B_26), A_25)=k1_relat_1(k7_relat_1(B_26, A_25)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.31/2.62  tff(c_552, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_480, c_26])).
% 7.31/2.62  tff(c_589, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_552])).
% 7.31/2.62  tff(c_28, plain, (![A_27]: (k7_relat_1(A_27, k1_relat_1(A_27))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.31/2.62  tff(c_620, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_589, c_28])).
% 7.31/2.62  tff(c_629, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_620])).
% 7.31/2.62  tff(c_632, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_629])).
% 7.31/2.62  tff(c_636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_632])).
% 7.31/2.62  tff(c_638, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_620])).
% 7.31/2.62  tff(c_200, plain, (![B_50, A_51]: (k2_relat_1(k7_relat_1(B_50, A_51))=k9_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.31/2.62  tff(c_1853, plain, (![A_105]: (k9_relat_1(A_105, k1_relat_1(A_105))=k2_relat_1(A_105) | ~v1_relat_1(A_105) | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_28, c_200])).
% 7.31/2.62  tff(c_1873, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_589, c_1853])).
% 7.31/2.62  tff(c_1877, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_638, c_638, c_1873])).
% 7.31/2.62  tff(c_22, plain, (![A_19, C_23, B_22]: (k9_relat_1(k7_relat_1(A_19, C_23), B_22)=k9_relat_1(A_19, B_22) | ~r1_tarski(B_22, C_23) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.31/2.62  tff(c_1884, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1877, c_22])).
% 7.31/2.62  tff(c_1891, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6, c_1884])).
% 7.31/2.62  tff(c_192, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_182])).
% 7.31/2.62  tff(c_316, plain, (![B_67, C_68]: (k3_xboole_0(B_67, C_68)=B_67 | ~r1_tarski(B_67, C_68) | ~r1_tarski(B_67, B_67))), inference(resolution, [status(thm)], [c_300, c_192])).
% 7.31/2.62  tff(c_341, plain, (![B_69, C_70]: (k3_xboole_0(B_69, C_70)=B_69 | ~r1_tarski(B_69, C_70))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_316])).
% 7.31/2.62  tff(c_371, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_341])).
% 7.31/2.62  tff(c_637, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_620])).
% 7.31/2.62  tff(c_24, plain, (![A_24]: (k10_relat_1(A_24, k2_relat_1(A_24))=k1_relat_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.31/2.62  tff(c_483, plain, (![A_74, C_75, B_76]: (k3_xboole_0(A_74, k10_relat_1(C_75, B_76))=k10_relat_1(k7_relat_1(C_75, A_74), B_76) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.31/2.62  tff(c_1921, plain, (![A_106, A_107]: (k10_relat_1(k7_relat_1(A_106, A_107), k2_relat_1(A_106))=k3_xboole_0(A_107, k1_relat_1(A_106)) | ~v1_relat_1(A_106) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_24, c_483])).
% 7.31/2.62  tff(c_1943, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_637, c_1921])).
% 7.31/2.62  tff(c_1961, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_638, c_638, c_1891, c_371, c_589, c_1943])).
% 7.31/2.62  tff(c_8063, plain, (![C_197, A_198, B_199]: (r1_tarski(k10_relat_1(k7_relat_1(C_197, A_198), B_199), k10_relat_1(C_197, B_199)) | ~v1_relat_1(C_197))), inference(superposition, [status(thm), theory('equality')], [c_483, c_148])).
% 7.31/2.62  tff(c_8092, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1961, c_8063])).
% 7.31/2.62  tff(c_8125, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8092])).
% 7.31/2.62  tff(c_8127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_8125])).
% 7.31/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.62  
% 7.31/2.62  Inference rules
% 7.31/2.62  ----------------------
% 7.31/2.62  #Ref     : 0
% 7.31/2.62  #Sup     : 1913
% 7.31/2.62  #Fact    : 0
% 7.31/2.62  #Define  : 0
% 7.31/2.62  #Split   : 3
% 7.31/2.62  #Chain   : 0
% 7.31/2.62  #Close   : 0
% 7.31/2.62  
% 7.31/2.62  Ordering : KBO
% 7.31/2.62  
% 7.31/2.62  Simplification rules
% 7.31/2.62  ----------------------
% 7.31/2.62  #Subsume      : 285
% 7.31/2.62  #Demod        : 2551
% 7.31/2.62  #Tautology    : 992
% 7.31/2.62  #SimpNegUnit  : 3
% 7.31/2.62  #BackRed      : 2
% 7.31/2.62  
% 7.31/2.62  #Partial instantiations: 0
% 7.31/2.62  #Strategies tried      : 1
% 7.31/2.62  
% 7.31/2.62  Timing (in seconds)
% 7.31/2.62  ----------------------
% 7.31/2.62  Preprocessing        : 0.40
% 7.31/2.62  Parsing              : 0.21
% 7.31/2.62  CNF conversion       : 0.02
% 7.31/2.62  Main loop            : 1.44
% 7.31/2.62  Inferencing          : 0.40
% 7.31/2.62  Reduction            : 0.68
% 7.31/2.62  Demodulation         : 0.57
% 7.31/2.62  BG Simplification    : 0.06
% 7.31/2.62  Subsumption          : 0.23
% 7.31/2.62  Abstraction          : 0.08
% 7.31/2.62  MUC search           : 0.00
% 7.31/2.62  Cooper               : 0.00
% 7.31/2.62  Total                : 1.88
% 7.31/2.62  Index Insertion      : 0.00
% 7.31/2.62  Index Deletion       : 0.00
% 7.31/2.62  Index Matching       : 0.00
% 7.31/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
