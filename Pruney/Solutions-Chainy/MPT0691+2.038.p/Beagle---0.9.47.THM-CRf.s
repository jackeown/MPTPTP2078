%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:44 EST 2020

% Result     : Theorem 53.20s
% Output     : CNFRefutation 53.51s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 258 expanded)
%              Number of leaves         :   24 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  106 ( 455 expanded)
%              Number of equality atoms :   28 ( 142 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_82,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_103,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [B_32,A_33] : k3_xboole_0(B_32,A_33) = k3_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    ! [B_32,A_33] : r1_tarski(k3_xboole_0(B_32,A_33),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_14])).

tff(c_1621,plain,(
    ! [B_106,A_107] : k3_xboole_0(k3_xboole_0(B_106,A_107),A_107) = k3_xboole_0(B_106,A_107) ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_2014,plain,(
    ! [B_115,A_116] : k3_xboole_0(k3_xboole_0(B_115,A_116),B_115) = k3_xboole_0(A_116,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1621])).

tff(c_2158,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_2014])).

tff(c_2208,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2158])).

tff(c_24,plain,(
    ! [A_21] :
      ( k10_relat_1(A_21,k2_relat_1(A_21)) = k1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1019,plain,(
    ! [A_94,C_95,B_96] :
      ( k3_xboole_0(A_94,k10_relat_1(C_95,B_96)) = k10_relat_1(k7_relat_1(C_95,A_94),B_96)
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3286,plain,(
    ! [C_135,B_136,B_137] :
      ( k3_xboole_0(k10_relat_1(C_135,B_136),B_137) = k10_relat_1(k7_relat_1(C_135,B_137),B_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1019])).

tff(c_24301,plain,(
    ! [A_393,B_394] :
      ( k10_relat_1(k7_relat_1(A_393,B_394),k2_relat_1(A_393)) = k3_xboole_0(k1_relat_1(A_393),B_394)
      | ~ v1_relat_1(A_393)
      | ~ v1_relat_1(A_393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3286])).

tff(c_571,plain,(
    ! [B_71,A_72] :
      ( k7_relat_1(B_71,A_72) = B_71
      | ~ r1_tarski(k1_relat_1(B_71),A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_586,plain,(
    ! [B_71] :
      ( k7_relat_1(B_71,k1_relat_1(B_71)) = B_71
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_8,c_571])).

tff(c_1842,plain,(
    ! [C_111,A_112,B_113] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_111,A_112),B_113),A_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_14])).

tff(c_1853,plain,(
    ! [B_71,B_113] :
      ( r1_tarski(k10_relat_1(B_71,B_113),k1_relat_1(B_71))
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_1842])).

tff(c_218828,plain,(
    ! [A_1447,B_1448] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(A_1447),B_1448),k1_relat_1(k7_relat_1(A_1447,B_1448)))
      | ~ v1_relat_1(k7_relat_1(A_1447,B_1448))
      | ~ v1_relat_1(k7_relat_1(A_1447,B_1448))
      | ~ v1_relat_1(A_1447)
      | ~ v1_relat_1(A_1447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24301,c_1853])).

tff(c_219006,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2208,c_218828])).

tff(c_219082,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_219006])).

tff(c_219084,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_219082])).

tff(c_219087,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_219084])).

tff(c_219091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_219087])).

tff(c_219093,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_219082])).

tff(c_219092,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_219082])).

tff(c_16281,plain,(
    ! [C_310,A_311] :
      ( r1_tarski(k1_relat_1(k7_relat_1(C_310,A_311)),A_311)
      | ~ v1_relat_1(C_310)
      | ~ v1_relat_1(k7_relat_1(C_310,A_311)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1842])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16312,plain,(
    ! [C_310,A_311] :
      ( k1_relat_1(k7_relat_1(C_310,A_311)) = A_311
      | ~ r1_tarski(A_311,k1_relat_1(k7_relat_1(C_310,A_311)))
      | ~ v1_relat_1(C_310)
      | ~ v1_relat_1(k7_relat_1(C_310,A_311)) ) ),
    inference(resolution,[status(thm)],[c_16281,c_4])).

tff(c_219284,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_219092,c_16312])).

tff(c_219309,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_219093,c_34,c_219284])).

tff(c_301,plain,(
    ! [B_54,A_55] :
      ( k2_relat_1(k7_relat_1(B_54,A_55)) = k9_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_307,plain,(
    ! [B_54,A_55] :
      ( k10_relat_1(k7_relat_1(B_54,A_55),k9_relat_1(B_54,A_55)) = k1_relat_1(k7_relat_1(B_54,A_55))
      | ~ v1_relat_1(k7_relat_1(B_54,A_55))
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_24])).

tff(c_11002,plain,(
    ! [C_237,A_238,B_239] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_237,A_238),B_239),k10_relat_1(C_237,B_239))
      | ~ v1_relat_1(C_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_54])).

tff(c_11025,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_54,A_55)),k10_relat_1(B_54,k9_relat_1(B_54,A_55)))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(k7_relat_1(B_54,A_55))
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_11002])).

tff(c_219366,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_219309,c_11025])).

tff(c_219484,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_219093,c_34,c_219366])).

tff(c_219486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_219484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 53.20/43.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.20/43.64  
% 53.20/43.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.20/43.64  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 53.20/43.64  
% 53.20/43.64  %Foreground sorts:
% 53.20/43.64  
% 53.20/43.64  
% 53.20/43.64  %Background operators:
% 53.20/43.64  
% 53.20/43.64  
% 53.20/43.64  %Foreground operators:
% 53.20/43.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 53.20/43.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 53.20/43.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 53.20/43.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 53.20/43.64  tff('#skF_2', type, '#skF_2': $i).
% 53.20/43.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 53.20/43.64  tff('#skF_1', type, '#skF_1': $i).
% 53.20/43.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 53.20/43.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 53.20/43.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 53.20/43.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 53.20/43.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 53.20/43.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 53.20/43.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 53.20/43.64  
% 53.51/43.66  tff(f_82, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 53.51/43.66  tff(f_57, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 53.51/43.66  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 53.51/43.66  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 53.51/43.66  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 53.51/43.66  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 53.51/43.66  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 53.51/43.66  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 53.51/43.66  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 53.51/43.66  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 53.51/43.66  tff(c_30, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 53.51/43.66  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 53.51/43.66  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 53.51/43.66  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 53.51/43.66  tff(c_88, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 53.51/43.66  tff(c_104, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_88])).
% 53.51/43.66  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 53.51/43.66  tff(c_103, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_88])).
% 53.51/43.66  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 53.51/43.66  tff(c_39, plain, (![B_32, A_33]: (k3_xboole_0(B_32, A_33)=k3_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 53.51/43.66  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 53.51/43.66  tff(c_54, plain, (![B_32, A_33]: (r1_tarski(k3_xboole_0(B_32, A_33), A_33))), inference(superposition, [status(thm), theory('equality')], [c_39, c_14])).
% 53.51/43.66  tff(c_1621, plain, (![B_106, A_107]: (k3_xboole_0(k3_xboole_0(B_106, A_107), A_107)=k3_xboole_0(B_106, A_107))), inference(resolution, [status(thm)], [c_54, c_88])).
% 53.51/43.66  tff(c_2014, plain, (![B_115, A_116]: (k3_xboole_0(k3_xboole_0(B_115, A_116), B_115)=k3_xboole_0(A_116, B_115))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1621])).
% 53.51/43.66  tff(c_2158, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_103, c_2014])).
% 53.51/43.66  tff(c_2208, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2158])).
% 53.51/43.66  tff(c_24, plain, (![A_21]: (k10_relat_1(A_21, k2_relat_1(A_21))=k1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 53.51/43.66  tff(c_1019, plain, (![A_94, C_95, B_96]: (k3_xboole_0(A_94, k10_relat_1(C_95, B_96))=k10_relat_1(k7_relat_1(C_95, A_94), B_96) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_75])).
% 53.51/43.66  tff(c_3286, plain, (![C_135, B_136, B_137]: (k3_xboole_0(k10_relat_1(C_135, B_136), B_137)=k10_relat_1(k7_relat_1(C_135, B_137), B_136) | ~v1_relat_1(C_135))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1019])).
% 53.51/43.66  tff(c_24301, plain, (![A_393, B_394]: (k10_relat_1(k7_relat_1(A_393, B_394), k2_relat_1(A_393))=k3_xboole_0(k1_relat_1(A_393), B_394) | ~v1_relat_1(A_393) | ~v1_relat_1(A_393))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3286])).
% 53.51/43.66  tff(c_571, plain, (![B_71, A_72]: (k7_relat_1(B_71, A_72)=B_71 | ~r1_tarski(k1_relat_1(B_71), A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_71])).
% 53.51/43.66  tff(c_586, plain, (![B_71]: (k7_relat_1(B_71, k1_relat_1(B_71))=B_71 | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_8, c_571])).
% 53.51/43.66  tff(c_1842, plain, (![C_111, A_112, B_113]: (r1_tarski(k10_relat_1(k7_relat_1(C_111, A_112), B_113), A_112) | ~v1_relat_1(C_111))), inference(superposition, [status(thm), theory('equality')], [c_1019, c_14])).
% 53.51/43.66  tff(c_1853, plain, (![B_71, B_113]: (r1_tarski(k10_relat_1(B_71, B_113), k1_relat_1(B_71)) | ~v1_relat_1(B_71) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_586, c_1842])).
% 53.51/43.66  tff(c_218828, plain, (![A_1447, B_1448]: (r1_tarski(k3_xboole_0(k1_relat_1(A_1447), B_1448), k1_relat_1(k7_relat_1(A_1447, B_1448))) | ~v1_relat_1(k7_relat_1(A_1447, B_1448)) | ~v1_relat_1(k7_relat_1(A_1447, B_1448)) | ~v1_relat_1(A_1447) | ~v1_relat_1(A_1447))), inference(superposition, [status(thm), theory('equality')], [c_24301, c_1853])).
% 53.51/43.66  tff(c_219006, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2208, c_218828])).
% 53.51/43.66  tff(c_219082, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_219006])).
% 53.51/43.66  tff(c_219084, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_219082])).
% 53.51/43.66  tff(c_219087, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_219084])).
% 53.51/43.66  tff(c_219091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_219087])).
% 53.51/43.66  tff(c_219093, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_219082])).
% 53.51/43.66  tff(c_219092, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_219082])).
% 53.51/43.66  tff(c_16281, plain, (![C_310, A_311]: (r1_tarski(k1_relat_1(k7_relat_1(C_310, A_311)), A_311) | ~v1_relat_1(C_310) | ~v1_relat_1(k7_relat_1(C_310, A_311)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1842])).
% 53.51/43.66  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 53.51/43.66  tff(c_16312, plain, (![C_310, A_311]: (k1_relat_1(k7_relat_1(C_310, A_311))=A_311 | ~r1_tarski(A_311, k1_relat_1(k7_relat_1(C_310, A_311))) | ~v1_relat_1(C_310) | ~v1_relat_1(k7_relat_1(C_310, A_311)))), inference(resolution, [status(thm)], [c_16281, c_4])).
% 53.51/43.66  tff(c_219284, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_219092, c_16312])).
% 53.51/43.66  tff(c_219309, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_219093, c_34, c_219284])).
% 53.51/43.66  tff(c_301, plain, (![B_54, A_55]: (k2_relat_1(k7_relat_1(B_54, A_55))=k9_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_61])).
% 53.51/43.66  tff(c_307, plain, (![B_54, A_55]: (k10_relat_1(k7_relat_1(B_54, A_55), k9_relat_1(B_54, A_55))=k1_relat_1(k7_relat_1(B_54, A_55)) | ~v1_relat_1(k7_relat_1(B_54, A_55)) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_301, c_24])).
% 53.51/43.66  tff(c_11002, plain, (![C_237, A_238, B_239]: (r1_tarski(k10_relat_1(k7_relat_1(C_237, A_238), B_239), k10_relat_1(C_237, B_239)) | ~v1_relat_1(C_237))), inference(superposition, [status(thm), theory('equality')], [c_1019, c_54])).
% 53.51/43.66  tff(c_11025, plain, (![B_54, A_55]: (r1_tarski(k1_relat_1(k7_relat_1(B_54, A_55)), k10_relat_1(B_54, k9_relat_1(B_54, A_55))) | ~v1_relat_1(B_54) | ~v1_relat_1(k7_relat_1(B_54, A_55)) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_307, c_11002])).
% 53.51/43.66  tff(c_219366, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_219309, c_11025])).
% 53.51/43.66  tff(c_219484, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_219093, c_34, c_219366])).
% 53.51/43.66  tff(c_219486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_219484])).
% 53.51/43.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.51/43.66  
% 53.51/43.66  Inference rules
% 53.51/43.66  ----------------------
% 53.51/43.66  #Ref     : 0
% 53.51/43.66  #Sup     : 55485
% 53.51/43.66  #Fact    : 0
% 53.51/43.66  #Define  : 0
% 53.51/43.66  #Split   : 2
% 53.51/43.66  #Chain   : 0
% 53.51/43.66  #Close   : 0
% 53.51/43.66  
% 53.51/43.66  Ordering : KBO
% 53.51/43.66  
% 53.51/43.66  Simplification rules
% 53.51/43.66  ----------------------
% 53.51/43.66  #Subsume      : 11448
% 53.51/43.66  #Demod        : 39094
% 53.51/43.66  #Tautology    : 23074
% 53.51/43.66  #SimpNegUnit  : 3
% 53.51/43.66  #BackRed      : 1
% 53.51/43.66  
% 53.51/43.66  #Partial instantiations: 0
% 53.51/43.66  #Strategies tried      : 1
% 53.51/43.66  
% 53.51/43.66  Timing (in seconds)
% 53.51/43.66  ----------------------
% 53.51/43.66  Preprocessing        : 0.31
% 53.51/43.66  Parsing              : 0.17
% 53.51/43.66  CNF conversion       : 0.02
% 53.51/43.66  Main loop            : 42.54
% 53.51/43.66  Inferencing          : 3.93
% 53.51/43.66  Reduction            : 23.86
% 53.51/43.67  Demodulation         : 22.04
% 53.51/43.67  BG Simplification    : 0.51
% 53.51/43.67  Subsumption          : 12.32
% 53.51/43.67  Abstraction          : 0.93
% 53.51/43.67  MUC search           : 0.00
% 53.51/43.67  Cooper               : 0.00
% 53.51/43.67  Total                : 42.88
% 53.51/43.67  Index Insertion      : 0.00
% 53.51/43.67  Index Deletion       : 0.00
% 53.51/43.67  Index Matching       : 0.00
% 53.51/43.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
