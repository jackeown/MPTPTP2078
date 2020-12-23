%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:08 EST 2020

% Result     : Theorem 27.34s
% Output     : CNFRefutation 27.34s
% Verified   : 
% Statistics : Number of formulae       :  137 (2646 expanded)
%              Number of leaves         :   25 ( 973 expanded)
%              Depth                    :   26
%              Number of atoms          :  383 (8600 expanded)
%              Number of equality atoms :   31 ( 409 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_140,plain,(
    ! [B_42,A_43] :
      ( k10_relat_1(k2_funct_1(B_42),A_43) = k9_relat_1(B_42,A_43)
      | ~ v2_funct_1(B_42)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [C_9,A_7,B_8] :
      ( r1_tarski(k10_relat_1(C_9,A_7),k10_relat_1(C_9,B_8))
      | ~ r1_tarski(A_7,B_8)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1619,plain,(
    ! [B_131,A_132,A_133] :
      ( r1_tarski(k10_relat_1(k2_funct_1(B_131),A_132),k9_relat_1(B_131,A_133))
      | ~ r1_tarski(A_132,A_133)
      | ~ v1_relat_1(k2_funct_1(B_131))
      | ~ v2_funct_1(B_131)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_8])).

tff(c_28,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_45,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_tarski(A_24,C_25)
      | ~ r1_tarski(B_26,C_25)
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,k9_relat_1('#skF_3','#skF_2'))
      | ~ r1_tarski(A_24,k9_relat_1('#skF_3','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k9_relat_1(B_5,A_4),k2_relat_1(B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_31,B_32,A_33] :
      ( r1_tarski(A_31,k2_relat_1(B_32))
      | ~ r1_tarski(A_31,k9_relat_1(B_32,A_33))
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_4,c_45])).

tff(c_83,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_24,k9_relat_1('#skF_3','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_53,c_80])).

tff(c_89,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_24,k9_relat_1('#skF_3','#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_83])).

tff(c_1645,plain,(
    ! [A_132] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),A_132),k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_132,'#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1619,c_89])).

tff(c_1691,plain,(
    ! [A_132] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),A_132),k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_132,'#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1645])).

tff(c_1697,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1691])).

tff(c_1700,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1697])).

tff(c_1704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1700])).

tff(c_1706,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1691])).

tff(c_10,plain,(
    ! [A_10] :
      ( v1_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,
    ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_80])).

tff(c_92,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86])).

tff(c_218,plain,(
    ! [B_48,A_49] :
      ( k9_relat_1(B_48,k10_relat_1(B_48,A_49)) = A_49
      | ~ r1_tarski(A_49,k2_relat_1(B_48))
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_223,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))) = k9_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_218])).

tff(c_229,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_223])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k10_relat_1(B_14,k9_relat_1(B_14,A_13)),A_13)
      | ~ v2_funct_1(B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_234,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_16])).

tff(c_247,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_234])).

tff(c_163,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(k10_relat_1(B_44,k9_relat_1(B_44,A_45)),A_45)
      | ~ v2_funct_1(B_44)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_493,plain,(
    ! [A_66,A_67,B_68] :
      ( r1_tarski(A_66,A_67)
      | ~ r1_tarski(A_66,k10_relat_1(B_68,k9_relat_1(B_68,A_67)))
      | ~ v2_funct_1(B_68)
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_507,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_247,c_493])).

tff(c_532,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_507])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k10_relat_1(k2_funct_1(B_16),A_15) = k9_relat_1(B_16,A_15)
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1800,plain,(
    ! [A_137] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),A_137),k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_137,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_1691])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k9_relat_1(B_12,k10_relat_1(B_12,A_11)) = A_11
      | ~ r1_tarski(A_11,k2_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1812,plain,(
    ! [A_137] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',k10_relat_1(k2_funct_1('#skF_3'),A_137))) = k10_relat_1(k2_funct_1('#skF_3'),A_137)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_137,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1800,c_14])).

tff(c_5264,plain,(
    ! [A_205] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',k10_relat_1(k2_funct_1('#skF_3'),A_205))) = k10_relat_1(k2_funct_1('#skF_3'),A_205)
      | ~ r1_tarski(A_205,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1812])).

tff(c_5366,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_15))) = k10_relat_1(k2_funct_1('#skF_3'),A_15)
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5264])).

tff(c_5451,plain,(
    ! [A_208] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_208))) = k10_relat_1(k2_funct_1('#skF_3'),A_208)
      | ~ r1_tarski(A_208,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_5366])).

tff(c_5584,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))) = k9_relat_1('#skF_3',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))
    | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_5451])).

tff(c_5629,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_229,c_5584])).

tff(c_122,plain,(
    ! [B_40,A_41] :
      ( k9_relat_1(k2_funct_1(B_40),A_41) = k10_relat_1(B_40,A_41)
      | ~ v2_funct_1(B_40)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_642,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(k10_relat_1(B_74,A_75),k2_relat_1(k2_funct_1(B_74)))
      | ~ v1_relat_1(k2_funct_1(B_74))
      | ~ v2_funct_1(B_74)
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_4])).

tff(c_6595,plain,(
    ! [A_218,B_219,A_220] :
      ( r1_tarski(A_218,k2_relat_1(k2_funct_1(B_219)))
      | ~ r1_tarski(A_218,k10_relat_1(B_219,A_220))
      | ~ v1_relat_1(k2_funct_1(B_219))
      | ~ v2_funct_1(B_219)
      | ~ v1_funct_1(B_219)
      | ~ v1_relat_1(B_219) ) ),
    inference(resolution,[status(thm)],[c_642,c_2])).

tff(c_6657,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_247,c_6595])).

tff(c_6712,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1706,c_6657])).

tff(c_6733,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))) = k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6712,c_14])).

tff(c_6755,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k9_relat_1('#skF_3','#skF_1')) = k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_5629,c_6733])).

tff(c_8437,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6755])).

tff(c_8440,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_8437])).

tff(c_8444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_8440])).

tff(c_8446,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6755])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [A_6] :
      ( k10_relat_1(A_6,k2_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5224,plain,(
    ! [A_204] :
      ( r1_tarski(k1_relat_1(A_204),k2_relat_1(k2_funct_1(A_204)))
      | ~ v1_relat_1(k2_funct_1(A_204))
      | ~ v2_funct_1(A_204)
      | ~ v1_funct_1(A_204)
      | ~ v1_relat_1(A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_642])).

tff(c_85356,plain,(
    ! [A_866,A_867] :
      ( r1_tarski(A_866,k2_relat_1(k2_funct_1(A_867)))
      | ~ r1_tarski(A_866,k1_relat_1(A_867))
      | ~ v1_relat_1(k2_funct_1(A_867))
      | ~ v2_funct_1(A_867)
      | ~ v1_funct_1(A_867)
      | ~ v1_relat_1(A_867) ) ),
    inference(resolution,[status(thm)],[c_5224,c_2])).

tff(c_160,plain,(
    ! [B_42] :
      ( k9_relat_1(B_42,k2_relat_1(k2_funct_1(B_42))) = k1_relat_1(k2_funct_1(B_42))
      | ~ v2_funct_1(B_42)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k2_funct_1(B_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_140])).

tff(c_230,plain,(
    ! [B_5,A_4] :
      ( k9_relat_1(B_5,k10_relat_1(B_5,k9_relat_1(B_5,A_4))) = k9_relat_1(B_5,A_4)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_4,c_218])).

tff(c_5535,plain,(
    ! [A_208] :
      ( k10_relat_1(k2_funct_1('#skF_3'),A_208) = k9_relat_1('#skF_3',A_208)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_208,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_230])).

tff(c_5630,plain,(
    ! [A_209] :
      ( k10_relat_1(k2_funct_1('#skF_3'),A_209) = k9_relat_1('#skF_3',A_209)
      | ~ r1_tarski(A_209,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_5535])).

tff(c_149,plain,(
    ! [B_42,A_7,A_43] :
      ( r1_tarski(k10_relat_1(k2_funct_1(B_42),A_7),k9_relat_1(B_42,A_43))
      | ~ r1_tarski(A_7,A_43)
      | ~ v1_relat_1(k2_funct_1(B_42))
      | ~ v2_funct_1(B_42)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_8])).

tff(c_5700,plain,(
    ! [A_209,A_43] :
      ( r1_tarski(k9_relat_1('#skF_3',A_209),k9_relat_1('#skF_3',A_43))
      | ~ r1_tarski(A_209,A_43)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_209,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5630,c_149])).

tff(c_5814,plain,(
    ! [A_209,A_43] :
      ( r1_tarski(k9_relat_1('#skF_3',A_209),k9_relat_1('#skF_3',A_43))
      | ~ r1_tarski(A_209,A_43)
      | ~ r1_tarski(A_209,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1706,c_5700])).

tff(c_1898,plain,(
    ! [B_139,A_140,B_141] :
      ( r1_tarski(k9_relat_1(B_139,A_140),k10_relat_1(k2_funct_1(B_139),B_141))
      | ~ r1_tarski(A_140,B_141)
      | ~ v1_relat_1(k2_funct_1(B_139))
      | ~ v2_funct_1(B_139)
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_8])).

tff(c_1927,plain,(
    ! [B_141] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),k10_relat_1(k2_funct_1('#skF_3'),B_141))
      | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),B_141)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_1898])).

tff(c_3999,plain,(
    ! [B_187] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),k10_relat_1(k2_funct_1('#skF_3'),B_187))
      | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),B_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1706,c_1927])).

tff(c_4028,plain,(
    ! [A_15] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',A_15))
      | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),A_15)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3999])).

tff(c_4057,plain,(
    ! [A_188] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',A_188))
      | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_4028])).

tff(c_4178,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_532,c_4057])).

tff(c_13089,plain,(
    ! [A_300,B_301,B_302,A_303] :
      ( r1_tarski(A_300,k10_relat_1(k2_funct_1(B_301),B_302))
      | ~ r1_tarski(A_300,k9_relat_1(B_301,A_303))
      | ~ r1_tarski(A_303,B_302)
      | ~ v1_relat_1(k2_funct_1(B_301))
      | ~ v2_funct_1(B_301)
      | ~ v1_funct_1(B_301)
      | ~ v1_relat_1(B_301) ) ),
    inference(resolution,[status(thm)],[c_1898,c_2])).

tff(c_13138,plain,(
    ! [B_302] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),k10_relat_1(k2_funct_1('#skF_3'),B_302))
      | ~ r1_tarski('#skF_1',B_302)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4178,c_13089])).

tff(c_13630,plain,(
    ! [B_308] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),k10_relat_1(k2_funct_1('#skF_3'),B_308))
      | ~ r1_tarski('#skF_1',B_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1706,c_13138])).

tff(c_13688,plain,(
    ! [A_15] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',A_15))
      | ~ r1_tarski('#skF_1',A_15)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_13630])).

tff(c_13735,plain,(
    ! [A_309] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',A_309))
      | ~ r1_tarski('#skF_1',A_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_13688])).

tff(c_14290,plain,(
    ! [A_316,A_317] :
      ( r1_tarski(A_316,k9_relat_1('#skF_3',A_317))
      | ~ r1_tarski(A_316,k9_relat_1('#skF_3','#skF_1'))
      | ~ r1_tarski('#skF_1',A_317) ) ),
    inference(resolution,[status(thm)],[c_13735,c_2])).

tff(c_14652,plain,(
    ! [A_319,A_320] :
      ( r1_tarski(k9_relat_1('#skF_3',A_319),k9_relat_1('#skF_3',A_320))
      | ~ r1_tarski('#skF_1',A_320)
      | ~ r1_tarski(A_319,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5814,c_14290])).

tff(c_14762,plain,(
    ! [A_319] :
      ( r1_tarski(k9_relat_1('#skF_3',A_319),k1_relat_1(k2_funct_1('#skF_3')))
      | ~ r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
      | ~ r1_tarski(A_319,'#skF_1')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_14652])).

tff(c_14824,plain,(
    ! [A_319] :
      ( r1_tarski(k9_relat_1('#skF_3',A_319),k1_relat_1(k2_funct_1('#skF_3')))
      | ~ r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
      | ~ r1_tarski(A_319,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_32,c_30,c_24,c_14762])).

tff(c_42126,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_14824])).

tff(c_85369,plain,
    ( ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85356,c_42126])).

tff(c_85483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1706,c_26,c_85369])).

tff(c_85485,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_14824])).

tff(c_85537,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_85485,c_14])).

tff(c_85583,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_8446,c_85537])).

tff(c_8445,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k9_relat_1('#skF_3','#skF_1')) = k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6755])).

tff(c_296,plain,(
    ! [B_54,A_55] :
      ( k9_relat_1(B_54,k10_relat_1(B_54,k9_relat_1(B_54,A_55))) = k9_relat_1(B_54,A_55)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_4,c_218])).

tff(c_337,plain,(
    ! [B_16,A_55] :
      ( k9_relat_1(k2_funct_1(B_16),k9_relat_1(B_16,k9_relat_1(k2_funct_1(B_16),A_55))) = k9_relat_1(k2_funct_1(B_16),A_55)
      | ~ v1_funct_1(k2_funct_1(B_16))
      | ~ v1_relat_1(k2_funct_1(B_16))
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_296])).

tff(c_85657,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = k9_relat_1(k2_funct_1('#skF_3'),k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_85583,c_337])).

tff(c_85786,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1706,c_8446,c_85583,c_8445,c_85657])).

tff(c_146,plain,(
    ! [B_42,A_43,B_8] :
      ( r1_tarski(k9_relat_1(B_42,A_43),k10_relat_1(k2_funct_1(B_42),B_8))
      | ~ r1_tarski(A_43,B_8)
      | ~ v1_relat_1(k2_funct_1(B_42))
      | ~ v2_funct_1(B_42)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_8])).

tff(c_5694,plain,(
    ! [A_43,A_209] :
      ( r1_tarski(k9_relat_1('#skF_3',A_43),k9_relat_1('#skF_3',A_209))
      | ~ r1_tarski(A_43,A_209)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_209,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5630,c_146])).

tff(c_5812,plain,(
    ! [A_43,A_209] :
      ( r1_tarski(k9_relat_1('#skF_3',A_43),k9_relat_1('#skF_3',A_209))
      | ~ r1_tarski(A_43,A_209)
      | ~ r1_tarski(A_209,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1706,c_5694])).

tff(c_7206,plain,(
    ! [A_229,A_230] :
      ( r1_tarski(k9_relat_1('#skF_3',A_229),k9_relat_1('#skF_3',A_230))
      | ~ r1_tarski(A_229,A_230)
      | ~ r1_tarski(A_229,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1706,c_5700])).

tff(c_93,plain,(
    ! [C_34,A_35,B_36] :
      ( r1_tarski(k10_relat_1(C_34,A_35),k10_relat_1(C_34,B_36))
      | ~ r1_tarski(A_35,B_36)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_357,plain,(
    ! [A_56,C_57,B_58,A_59] :
      ( r1_tarski(A_56,k10_relat_1(C_57,B_58))
      | ~ r1_tarski(A_56,k10_relat_1(C_57,A_59))
      | ~ r1_tarski(A_59,B_58)
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_952,plain,(
    ! [C_95,A_96,B_97,B_98] :
      ( r1_tarski(k10_relat_1(C_95,A_96),k10_relat_1(C_95,B_97))
      | ~ r1_tarski(B_98,B_97)
      | ~ r1_tarski(A_96,B_98)
      | ~ v1_relat_1(C_95) ) ),
    inference(resolution,[status(thm)],[c_8,c_357])).

tff(c_1063,plain,(
    ! [C_101,A_102] :
      ( r1_tarski(k10_relat_1(C_101,A_102),k10_relat_1(C_101,k9_relat_1('#skF_3','#skF_2')))
      | ~ r1_tarski(A_102,k9_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1(C_101) ) ),
    inference(resolution,[status(thm)],[c_28,c_952])).

tff(c_186,plain,(
    ! [A_1,A_45,B_44] :
      ( r1_tarski(A_1,A_45)
      | ~ r1_tarski(A_1,k10_relat_1(B_44,k9_relat_1(B_44,A_45)))
      | ~ v2_funct_1(B_44)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_1079,plain,(
    ! [A_102] :
      ( r1_tarski(k10_relat_1('#skF_3',A_102),'#skF_2')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ r1_tarski(A_102,k9_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1063,c_186])).

tff(c_1114,plain,(
    ! [A_103] :
      ( r1_tarski(k10_relat_1('#skF_3',A_103),'#skF_2')
      | ~ r1_tarski(A_103,k9_relat_1('#skF_3','#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1079])).

tff(c_1136,plain,(
    ! [A_104,A_105] :
      ( r1_tarski(A_104,'#skF_2')
      | ~ r1_tarski(A_104,k10_relat_1('#skF_3',A_105))
      | ~ r1_tarski(A_105,k9_relat_1('#skF_3','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1114,c_2])).

tff(c_1161,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k10_relat_1('#skF_3',A_7),'#skF_2')
      | ~ r1_tarski(B_8,k9_relat_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_7,B_8)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_1136])).

tff(c_1183,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k10_relat_1('#skF_3',A_7),'#skF_2')
      | ~ r1_tarski(B_8,k9_relat_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1161])).

tff(c_7536,plain,(
    ! [A_234,A_235] :
      ( r1_tarski(k10_relat_1('#skF_3',A_234),'#skF_2')
      | ~ r1_tarski(A_234,k9_relat_1('#skF_3',A_235))
      | ~ r1_tarski(A_235,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_7206,c_1183])).

tff(c_7637,plain,(
    ! [A_236,A_237] :
      ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_236)),'#skF_2')
      | ~ r1_tarski(A_236,A_237)
      | ~ r1_tarski(A_237,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5812,c_7536])).

tff(c_7759,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))),'#skF_2')
    | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_247,c_7637])).

tff(c_7845,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_229,c_7759])).

tff(c_85882,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85786,c_7845])).

tff(c_85900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_85882])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.34/18.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.34/18.94  
% 27.34/18.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.34/18.94  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 27.34/18.94  
% 27.34/18.94  %Foreground sorts:
% 27.34/18.94  
% 27.34/18.94  
% 27.34/18.94  %Background operators:
% 27.34/18.94  
% 27.34/18.94  
% 27.34/18.94  %Foreground operators:
% 27.34/18.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 27.34/18.94  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 27.34/18.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 27.34/18.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.34/18.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.34/18.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.34/18.94  tff('#skF_2', type, '#skF_2': $i).
% 27.34/18.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 27.34/18.94  tff('#skF_3', type, '#skF_3': $i).
% 27.34/18.94  tff('#skF_1', type, '#skF_1': $i).
% 27.34/18.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.34/18.94  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 27.34/18.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.34/18.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.34/18.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.34/18.94  
% 27.34/18.96  tff(f_98, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 27.34/18.96  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 27.34/18.96  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 27.34/18.96  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 27.34/18.96  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 27.34/18.96  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 27.34/18.96  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 27.34/18.96  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 27.34/18.96  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 27.34/18.96  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 27.34/18.96  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.34/18.96  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.34/18.96  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.34/18.96  tff(c_24, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.34/18.96  tff(c_12, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.34/18.96  tff(c_140, plain, (![B_42, A_43]: (k10_relat_1(k2_funct_1(B_42), A_43)=k9_relat_1(B_42, A_43) | ~v2_funct_1(B_42) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.34/18.96  tff(c_8, plain, (![C_9, A_7, B_8]: (r1_tarski(k10_relat_1(C_9, A_7), k10_relat_1(C_9, B_8)) | ~r1_tarski(A_7, B_8) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.34/18.96  tff(c_1619, plain, (![B_131, A_132, A_133]: (r1_tarski(k10_relat_1(k2_funct_1(B_131), A_132), k9_relat_1(B_131, A_133)) | ~r1_tarski(A_132, A_133) | ~v1_relat_1(k2_funct_1(B_131)) | ~v2_funct_1(B_131) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131))), inference(superposition, [status(thm), theory('equality')], [c_140, c_8])).
% 27.34/18.96  tff(c_28, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.34/18.96  tff(c_45, plain, (![A_24, C_25, B_26]: (r1_tarski(A_24, C_25) | ~r1_tarski(B_26, C_25) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.34/18.96  tff(c_53, plain, (![A_24]: (r1_tarski(A_24, k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(A_24, k9_relat_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_28, c_45])).
% 27.34/18.96  tff(c_4, plain, (![B_5, A_4]: (r1_tarski(k9_relat_1(B_5, A_4), k2_relat_1(B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.34/18.96  tff(c_80, plain, (![A_31, B_32, A_33]: (r1_tarski(A_31, k2_relat_1(B_32)) | ~r1_tarski(A_31, k9_relat_1(B_32, A_33)) | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_4, c_45])).
% 27.34/18.96  tff(c_83, plain, (![A_24]: (r1_tarski(A_24, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~r1_tarski(A_24, k9_relat_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_53, c_80])).
% 27.34/18.96  tff(c_89, plain, (![A_24]: (r1_tarski(A_24, k2_relat_1('#skF_3')) | ~r1_tarski(A_24, k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_83])).
% 27.34/18.96  tff(c_1645, plain, (![A_132]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), A_132), k2_relat_1('#skF_3')) | ~r1_tarski(A_132, '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1619, c_89])).
% 27.34/18.96  tff(c_1691, plain, (![A_132]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), A_132), k2_relat_1('#skF_3')) | ~r1_tarski(A_132, '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1645])).
% 27.34/18.96  tff(c_1697, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1691])).
% 27.34/18.96  tff(c_1700, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1697])).
% 27.34/18.96  tff(c_1704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1700])).
% 27.34/18.96  tff(c_1706, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1691])).
% 27.34/18.96  tff(c_10, plain, (![A_10]: (v1_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.34/18.96  tff(c_86, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_80])).
% 27.34/18.96  tff(c_92, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_86])).
% 27.34/18.96  tff(c_218, plain, (![B_48, A_49]: (k9_relat_1(B_48, k10_relat_1(B_48, A_49))=A_49 | ~r1_tarski(A_49, k2_relat_1(B_48)) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 27.34/18.96  tff(c_223, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))=k9_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_218])).
% 27.34/18.96  tff(c_229, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_223])).
% 27.34/18.96  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k10_relat_1(B_14, k9_relat_1(B_14, A_13)), A_13) | ~v2_funct_1(B_14) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 27.34/18.96  tff(c_234, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_229, c_16])).
% 27.34/18.96  tff(c_247, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_234])).
% 27.34/18.96  tff(c_163, plain, (![B_44, A_45]: (r1_tarski(k10_relat_1(B_44, k9_relat_1(B_44, A_45)), A_45) | ~v2_funct_1(B_44) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 27.34/18.96  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.34/18.96  tff(c_493, plain, (![A_66, A_67, B_68]: (r1_tarski(A_66, A_67) | ~r1_tarski(A_66, k10_relat_1(B_68, k9_relat_1(B_68, A_67))) | ~v2_funct_1(B_68) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_163, c_2])).
% 27.34/18.96  tff(c_507, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_247, c_493])).
% 27.34/18.96  tff(c_532, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_507])).
% 27.34/18.96  tff(c_18, plain, (![B_16, A_15]: (k10_relat_1(k2_funct_1(B_16), A_15)=k9_relat_1(B_16, A_15) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.34/18.96  tff(c_1800, plain, (![A_137]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), A_137), k2_relat_1('#skF_3')) | ~r1_tarski(A_137, '#skF_1'))), inference(splitRight, [status(thm)], [c_1691])).
% 27.34/18.96  tff(c_14, plain, (![B_12, A_11]: (k9_relat_1(B_12, k10_relat_1(B_12, A_11))=A_11 | ~r1_tarski(A_11, k2_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 27.34/18.96  tff(c_1812, plain, (![A_137]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k10_relat_1(k2_funct_1('#skF_3'), A_137)))=k10_relat_1(k2_funct_1('#skF_3'), A_137) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_137, '#skF_1'))), inference(resolution, [status(thm)], [c_1800, c_14])).
% 27.34/18.96  tff(c_5264, plain, (![A_205]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k10_relat_1(k2_funct_1('#skF_3'), A_205)))=k10_relat_1(k2_funct_1('#skF_3'), A_205) | ~r1_tarski(A_205, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1812])).
% 27.34/18.96  tff(c_5366, plain, (![A_15]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_15)))=k10_relat_1(k2_funct_1('#skF_3'), A_15) | ~r1_tarski(A_15, '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_5264])).
% 27.34/18.96  tff(c_5451, plain, (![A_208]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_208)))=k10_relat_1(k2_funct_1('#skF_3'), A_208) | ~r1_tarski(A_208, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_5366])).
% 27.34/18.96  tff(c_5584, plain, (k10_relat_1(k2_funct_1('#skF_3'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))=k9_relat_1('#skF_3', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))) | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_229, c_5451])).
% 27.34/18.96  tff(c_5629, plain, (k10_relat_1(k2_funct_1('#skF_3'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_229, c_5584])).
% 27.34/18.96  tff(c_122, plain, (![B_40, A_41]: (k9_relat_1(k2_funct_1(B_40), A_41)=k10_relat_1(B_40, A_41) | ~v2_funct_1(B_40) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_85])).
% 27.34/18.96  tff(c_642, plain, (![B_74, A_75]: (r1_tarski(k10_relat_1(B_74, A_75), k2_relat_1(k2_funct_1(B_74))) | ~v1_relat_1(k2_funct_1(B_74)) | ~v2_funct_1(B_74) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(superposition, [status(thm), theory('equality')], [c_122, c_4])).
% 27.34/18.96  tff(c_6595, plain, (![A_218, B_219, A_220]: (r1_tarski(A_218, k2_relat_1(k2_funct_1(B_219))) | ~r1_tarski(A_218, k10_relat_1(B_219, A_220)) | ~v1_relat_1(k2_funct_1(B_219)) | ~v2_funct_1(B_219) | ~v1_funct_1(B_219) | ~v1_relat_1(B_219))), inference(resolution, [status(thm)], [c_642, c_2])).
% 27.34/18.96  tff(c_6657, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_247, c_6595])).
% 27.34/18.96  tff(c_6712, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1706, c_6657])).
% 27.34/18.96  tff(c_6733, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))))=k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_6712, c_14])).
% 27.34/18.96  tff(c_6755, plain, (k9_relat_1(k2_funct_1('#skF_3'), k9_relat_1('#skF_3', '#skF_1'))=k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_5629, c_6733])).
% 27.34/18.96  tff(c_8437, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6755])).
% 27.34/18.96  tff(c_8440, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_8437])).
% 27.34/18.96  tff(c_8444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_8440])).
% 27.34/18.96  tff(c_8446, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6755])).
% 27.34/18.96  tff(c_26, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.34/18.96  tff(c_6, plain, (![A_6]: (k10_relat_1(A_6, k2_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 27.34/18.96  tff(c_5224, plain, (![A_204]: (r1_tarski(k1_relat_1(A_204), k2_relat_1(k2_funct_1(A_204))) | ~v1_relat_1(k2_funct_1(A_204)) | ~v2_funct_1(A_204) | ~v1_funct_1(A_204) | ~v1_relat_1(A_204) | ~v1_relat_1(A_204))), inference(superposition, [status(thm), theory('equality')], [c_6, c_642])).
% 27.34/18.96  tff(c_85356, plain, (![A_866, A_867]: (r1_tarski(A_866, k2_relat_1(k2_funct_1(A_867))) | ~r1_tarski(A_866, k1_relat_1(A_867)) | ~v1_relat_1(k2_funct_1(A_867)) | ~v2_funct_1(A_867) | ~v1_funct_1(A_867) | ~v1_relat_1(A_867))), inference(resolution, [status(thm)], [c_5224, c_2])).
% 27.34/18.96  tff(c_160, plain, (![B_42]: (k9_relat_1(B_42, k2_relat_1(k2_funct_1(B_42)))=k1_relat_1(k2_funct_1(B_42)) | ~v2_funct_1(B_42) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42) | ~v1_relat_1(k2_funct_1(B_42)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_140])).
% 27.34/18.96  tff(c_230, plain, (![B_5, A_4]: (k9_relat_1(B_5, k10_relat_1(B_5, k9_relat_1(B_5, A_4)))=k9_relat_1(B_5, A_4) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_4, c_218])).
% 27.34/18.96  tff(c_5535, plain, (![A_208]: (k10_relat_1(k2_funct_1('#skF_3'), A_208)=k9_relat_1('#skF_3', A_208) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_208, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5451, c_230])).
% 27.34/18.96  tff(c_5630, plain, (![A_209]: (k10_relat_1(k2_funct_1('#skF_3'), A_209)=k9_relat_1('#skF_3', A_209) | ~r1_tarski(A_209, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_5535])).
% 27.34/18.96  tff(c_149, plain, (![B_42, A_7, A_43]: (r1_tarski(k10_relat_1(k2_funct_1(B_42), A_7), k9_relat_1(B_42, A_43)) | ~r1_tarski(A_7, A_43) | ~v1_relat_1(k2_funct_1(B_42)) | ~v2_funct_1(B_42) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_140, c_8])).
% 27.34/18.96  tff(c_5700, plain, (![A_209, A_43]: (r1_tarski(k9_relat_1('#skF_3', A_209), k9_relat_1('#skF_3', A_43)) | ~r1_tarski(A_209, A_43) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_209, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5630, c_149])).
% 27.34/18.96  tff(c_5814, plain, (![A_209, A_43]: (r1_tarski(k9_relat_1('#skF_3', A_209), k9_relat_1('#skF_3', A_43)) | ~r1_tarski(A_209, A_43) | ~r1_tarski(A_209, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1706, c_5700])).
% 27.34/18.96  tff(c_1898, plain, (![B_139, A_140, B_141]: (r1_tarski(k9_relat_1(B_139, A_140), k10_relat_1(k2_funct_1(B_139), B_141)) | ~r1_tarski(A_140, B_141) | ~v1_relat_1(k2_funct_1(B_139)) | ~v2_funct_1(B_139) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(superposition, [status(thm), theory('equality')], [c_140, c_8])).
% 27.34/18.96  tff(c_1927, plain, (![B_141]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k10_relat_1(k2_funct_1('#skF_3'), B_141)) | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), B_141) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_1898])).
% 27.34/18.96  tff(c_3999, plain, (![B_187]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k10_relat_1(k2_funct_1('#skF_3'), B_187)) | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), B_187))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1706, c_1927])).
% 27.34/18.96  tff(c_4028, plain, (![A_15]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', A_15)) | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), A_15) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3999])).
% 27.34/18.96  tff(c_4057, plain, (![A_188]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', A_188)) | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), A_188))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_4028])).
% 27.34/18.96  tff(c_4178, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_532, c_4057])).
% 27.34/18.96  tff(c_13089, plain, (![A_300, B_301, B_302, A_303]: (r1_tarski(A_300, k10_relat_1(k2_funct_1(B_301), B_302)) | ~r1_tarski(A_300, k9_relat_1(B_301, A_303)) | ~r1_tarski(A_303, B_302) | ~v1_relat_1(k2_funct_1(B_301)) | ~v2_funct_1(B_301) | ~v1_funct_1(B_301) | ~v1_relat_1(B_301))), inference(resolution, [status(thm)], [c_1898, c_2])).
% 27.34/18.96  tff(c_13138, plain, (![B_302]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k10_relat_1(k2_funct_1('#skF_3'), B_302)) | ~r1_tarski('#skF_1', B_302) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4178, c_13089])).
% 27.34/18.96  tff(c_13630, plain, (![B_308]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k10_relat_1(k2_funct_1('#skF_3'), B_308)) | ~r1_tarski('#skF_1', B_308))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1706, c_13138])).
% 27.34/18.96  tff(c_13688, plain, (![A_15]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', A_15)) | ~r1_tarski('#skF_1', A_15) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_13630])).
% 27.34/18.96  tff(c_13735, plain, (![A_309]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', A_309)) | ~r1_tarski('#skF_1', A_309))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_13688])).
% 27.34/18.96  tff(c_14290, plain, (![A_316, A_317]: (r1_tarski(A_316, k9_relat_1('#skF_3', A_317)) | ~r1_tarski(A_316, k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski('#skF_1', A_317))), inference(resolution, [status(thm)], [c_13735, c_2])).
% 27.34/18.96  tff(c_14652, plain, (![A_319, A_320]: (r1_tarski(k9_relat_1('#skF_3', A_319), k9_relat_1('#skF_3', A_320)) | ~r1_tarski('#skF_1', A_320) | ~r1_tarski(A_319, '#skF_1'))), inference(resolution, [status(thm)], [c_5814, c_14290])).
% 27.34/18.96  tff(c_14762, plain, (![A_319]: (r1_tarski(k9_relat_1('#skF_3', A_319), k1_relat_1(k2_funct_1('#skF_3'))) | ~r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~r1_tarski(A_319, '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_160, c_14652])).
% 27.34/18.96  tff(c_14824, plain, (![A_319]: (r1_tarski(k9_relat_1('#skF_3', A_319), k1_relat_1(k2_funct_1('#skF_3'))) | ~r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~r1_tarski(A_319, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_32, c_30, c_24, c_14762])).
% 27.34/18.96  tff(c_42126, plain, (~r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_14824])).
% 27.34/18.96  tff(c_85369, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85356, c_42126])).
% 27.34/18.96  tff(c_85483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1706, c_26, c_85369])).
% 27.34/18.96  tff(c_85485, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_14824])).
% 27.34/18.96  tff(c_85537, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_85485, c_14])).
% 27.34/18.96  tff(c_85583, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_8446, c_85537])).
% 27.34/18.96  tff(c_8445, plain, (k9_relat_1(k2_funct_1('#skF_3'), k9_relat_1('#skF_3', '#skF_1'))=k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_6755])).
% 27.34/18.96  tff(c_296, plain, (![B_54, A_55]: (k9_relat_1(B_54, k10_relat_1(B_54, k9_relat_1(B_54, A_55)))=k9_relat_1(B_54, A_55) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_4, c_218])).
% 27.34/18.96  tff(c_337, plain, (![B_16, A_55]: (k9_relat_1(k2_funct_1(B_16), k9_relat_1(B_16, k9_relat_1(k2_funct_1(B_16), A_55)))=k9_relat_1(k2_funct_1(B_16), A_55) | ~v1_funct_1(k2_funct_1(B_16)) | ~v1_relat_1(k2_funct_1(B_16)) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_296])).
% 27.34/18.96  tff(c_85657, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))=k9_relat_1(k2_funct_1('#skF_3'), k9_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_85583, c_337])).
% 27.34/18.96  tff(c_85786, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1706, c_8446, c_85583, c_8445, c_85657])).
% 27.34/18.96  tff(c_146, plain, (![B_42, A_43, B_8]: (r1_tarski(k9_relat_1(B_42, A_43), k10_relat_1(k2_funct_1(B_42), B_8)) | ~r1_tarski(A_43, B_8) | ~v1_relat_1(k2_funct_1(B_42)) | ~v2_funct_1(B_42) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_140, c_8])).
% 27.34/18.96  tff(c_5694, plain, (![A_43, A_209]: (r1_tarski(k9_relat_1('#skF_3', A_43), k9_relat_1('#skF_3', A_209)) | ~r1_tarski(A_43, A_209) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_209, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5630, c_146])).
% 27.34/18.96  tff(c_5812, plain, (![A_43, A_209]: (r1_tarski(k9_relat_1('#skF_3', A_43), k9_relat_1('#skF_3', A_209)) | ~r1_tarski(A_43, A_209) | ~r1_tarski(A_209, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1706, c_5694])).
% 27.34/18.96  tff(c_7206, plain, (![A_229, A_230]: (r1_tarski(k9_relat_1('#skF_3', A_229), k9_relat_1('#skF_3', A_230)) | ~r1_tarski(A_229, A_230) | ~r1_tarski(A_229, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1706, c_5700])).
% 27.34/18.96  tff(c_93, plain, (![C_34, A_35, B_36]: (r1_tarski(k10_relat_1(C_34, A_35), k10_relat_1(C_34, B_36)) | ~r1_tarski(A_35, B_36) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.34/18.96  tff(c_357, plain, (![A_56, C_57, B_58, A_59]: (r1_tarski(A_56, k10_relat_1(C_57, B_58)) | ~r1_tarski(A_56, k10_relat_1(C_57, A_59)) | ~r1_tarski(A_59, B_58) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_93, c_2])).
% 27.34/18.96  tff(c_952, plain, (![C_95, A_96, B_97, B_98]: (r1_tarski(k10_relat_1(C_95, A_96), k10_relat_1(C_95, B_97)) | ~r1_tarski(B_98, B_97) | ~r1_tarski(A_96, B_98) | ~v1_relat_1(C_95))), inference(resolution, [status(thm)], [c_8, c_357])).
% 27.34/18.96  tff(c_1063, plain, (![C_101, A_102]: (r1_tarski(k10_relat_1(C_101, A_102), k10_relat_1(C_101, k9_relat_1('#skF_3', '#skF_2'))) | ~r1_tarski(A_102, k9_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(C_101))), inference(resolution, [status(thm)], [c_28, c_952])).
% 27.34/18.96  tff(c_186, plain, (![A_1, A_45, B_44]: (r1_tarski(A_1, A_45) | ~r1_tarski(A_1, k10_relat_1(B_44, k9_relat_1(B_44, A_45))) | ~v2_funct_1(B_44) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_163, c_2])).
% 27.34/18.96  tff(c_1079, plain, (![A_102]: (r1_tarski(k10_relat_1('#skF_3', A_102), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~r1_tarski(A_102, k9_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1063, c_186])).
% 27.34/18.96  tff(c_1114, plain, (![A_103]: (r1_tarski(k10_relat_1('#skF_3', A_103), '#skF_2') | ~r1_tarski(A_103, k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1079])).
% 27.34/18.96  tff(c_1136, plain, (![A_104, A_105]: (r1_tarski(A_104, '#skF_2') | ~r1_tarski(A_104, k10_relat_1('#skF_3', A_105)) | ~r1_tarski(A_105, k9_relat_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_1114, c_2])).
% 27.34/18.96  tff(c_1161, plain, (![A_7, B_8]: (r1_tarski(k10_relat_1('#skF_3', A_7), '#skF_2') | ~r1_tarski(B_8, k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(A_7, B_8) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_1136])).
% 27.34/18.96  tff(c_1183, plain, (![A_7, B_8]: (r1_tarski(k10_relat_1('#skF_3', A_7), '#skF_2') | ~r1_tarski(B_8, k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1161])).
% 27.34/18.96  tff(c_7536, plain, (![A_234, A_235]: (r1_tarski(k10_relat_1('#skF_3', A_234), '#skF_2') | ~r1_tarski(A_234, k9_relat_1('#skF_3', A_235)) | ~r1_tarski(A_235, '#skF_1'))), inference(resolution, [status(thm)], [c_7206, c_1183])).
% 27.34/18.96  tff(c_7637, plain, (![A_236, A_237]: (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_236)), '#skF_2') | ~r1_tarski(A_236, A_237) | ~r1_tarski(A_237, '#skF_1'))), inference(resolution, [status(thm)], [c_5812, c_7536])).
% 27.34/18.96  tff(c_7759, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))), '#skF_2') | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_1')), inference(resolution, [status(thm)], [c_247, c_7637])).
% 27.34/18.96  tff(c_7845, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_229, c_7759])).
% 27.34/18.96  tff(c_85882, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_85786, c_7845])).
% 27.34/18.96  tff(c_85900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_85882])).
% 27.34/18.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.34/18.96  
% 27.34/18.96  Inference rules
% 27.34/18.96  ----------------------
% 27.34/18.96  #Ref     : 0
% 27.34/18.96  #Sup     : 20767
% 27.34/18.96  #Fact    : 0
% 27.34/18.96  #Define  : 0
% 27.34/18.96  #Split   : 48
% 27.34/18.96  #Chain   : 0
% 27.34/18.96  #Close   : 0
% 27.34/18.96  
% 27.34/18.96  Ordering : KBO
% 27.34/18.96  
% 27.34/18.96  Simplification rules
% 27.34/18.96  ----------------------
% 27.34/18.96  #Subsume      : 9377
% 27.34/18.96  #Demod        : 16479
% 27.34/18.96  #Tautology    : 1523
% 27.34/18.96  #SimpNegUnit  : 92
% 27.34/18.96  #BackRed      : 67
% 27.34/18.96  
% 27.34/18.96  #Partial instantiations: 0
% 27.34/18.96  #Strategies tried      : 1
% 27.34/18.96  
% 27.34/18.96  Timing (in seconds)
% 27.34/18.96  ----------------------
% 27.34/18.97  Preprocessing        : 0.28
% 27.34/18.97  Parsing              : 0.16
% 27.34/18.97  CNF conversion       : 0.02
% 27.34/18.97  Main loop            : 17.76
% 27.34/18.97  Inferencing          : 2.08
% 27.34/18.97  Reduction            : 3.63
% 27.34/18.97  Demodulation         : 2.50
% 27.34/18.97  BG Simplification    : 0.21
% 27.34/18.97  Subsumption          : 11.08
% 27.34/18.97  Abstraction          : 0.38
% 27.34/18.97  MUC search           : 0.00
% 27.34/18.97  Cooper               : 0.00
% 27.34/18.97  Total                : 18.09
% 27.34/18.97  Index Insertion      : 0.00
% 27.34/18.97  Index Deletion       : 0.00
% 27.34/18.97  Index Matching       : 0.00
% 27.34/18.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
