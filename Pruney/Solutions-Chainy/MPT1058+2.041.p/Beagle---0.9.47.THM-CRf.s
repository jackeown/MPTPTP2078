%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:27 EST 2020

% Result     : Theorem 7.14s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 137 expanded)
%              Number of leaves         :   40 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 220 expanded)
%              Number of equality atoms :   32 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_66,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ! [A_57] : v1_relat_1(k6_relat_1(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ! [A_44] : k1_relat_1(k6_relat_1(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [A_44] : k2_relat_1(k6_relat_1(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_113,plain,(
    ! [A_76] :
      ( k10_relat_1(A_76,k2_relat_1(A_76)) = k1_relat_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_122,plain,(
    ! [A_44] :
      ( k10_relat_1(k6_relat_1(A_44),A_44) = k1_relat_1(k6_relat_1(A_44))
      | ~ v1_relat_1(k6_relat_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_113])).

tff(c_126,plain,(
    ! [A_44] : k10_relat_1(k6_relat_1(A_44),A_44) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_34,c_122])).

tff(c_58,plain,(
    ! [A_57] : v1_funct_1(k6_relat_1(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_512,plain,(
    ! [B_138,A_139] :
      ( k9_relat_1(B_138,k10_relat_1(B_138,A_139)) = A_139
      | ~ r1_tarski(A_139,k2_relat_1(B_138))
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_517,plain,(
    ! [A_44,A_139] :
      ( k9_relat_1(k6_relat_1(A_44),k10_relat_1(k6_relat_1(A_44),A_139)) = A_139
      | ~ r1_tarski(A_139,A_44)
      | ~ v1_funct_1(k6_relat_1(A_44))
      | ~ v1_relat_1(k6_relat_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_512])).

tff(c_525,plain,(
    ! [A_140,A_141] :
      ( k9_relat_1(k6_relat_1(A_140),k10_relat_1(k6_relat_1(A_140),A_141)) = A_141
      | ~ r1_tarski(A_141,A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_517])).

tff(c_534,plain,(
    ! [A_44] :
      ( k9_relat_1(k6_relat_1(A_44),A_44) = A_44
      | ~ r1_tarski(A_44,A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_525])).

tff(c_542,plain,(
    ! [A_44] : k9_relat_1(k6_relat_1(A_44),A_44) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_534])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_468,plain,(
    ! [D_134,A_135,B_136] :
      ( r2_hidden(D_134,k1_relat_1(A_135))
      | ~ r2_hidden(D_134,k10_relat_1(A_135,B_136))
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5983,plain,(
    ! [A_366,B_367,B_368] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_366,B_367),B_368),k1_relat_1(A_366))
      | ~ v1_funct_1(A_366)
      | ~ v1_relat_1(A_366)
      | r1_tarski(k10_relat_1(A_366,B_367),B_368) ) ),
    inference(resolution,[status(thm)],[c_6,c_468])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6035,plain,(
    ! [A_369,B_370] :
      ( ~ v1_funct_1(A_369)
      | ~ v1_relat_1(A_369)
      | r1_tarski(k10_relat_1(A_369,B_370),k1_relat_1(A_369)) ) ),
    inference(resolution,[status(thm)],[c_5983,c_4])).

tff(c_6098,plain,(
    ! [A_44,B_370] :
      ( ~ v1_funct_1(k6_relat_1(A_44))
      | ~ v1_relat_1(k6_relat_1(A_44))
      | r1_tarski(k10_relat_1(k6_relat_1(A_44),B_370),A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6035])).

tff(c_6118,plain,(
    ! [A_44,B_370] : r1_tarski(k10_relat_1(k6_relat_1(A_44),B_370),A_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_6098])).

tff(c_200,plain,(
    ! [C_101,A_102,B_103] :
      ( r1_tarski(k10_relat_1(C_101,A_102),k10_relat_1(C_101,B_103))
      | ~ r1_tarski(A_102,B_103)
      | ~ v1_relat_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_211,plain,(
    ! [A_44,B_103] :
      ( r1_tarski(A_44,k10_relat_1(k6_relat_1(A_44),B_103))
      | ~ r1_tarski(A_44,B_103)
      | ~ v1_relat_1(k6_relat_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_200])).

tff(c_326,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,k10_relat_1(k6_relat_1(A_114),B_115))
      | ~ r1_tarski(A_114,B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_211])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_339,plain,(
    ! [A_114,B_115] :
      ( k10_relat_1(k6_relat_1(A_114),B_115) = A_114
      | ~ r1_tarski(k10_relat_1(k6_relat_1(A_114),B_115),A_114)
      | ~ r1_tarski(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_326,c_8])).

tff(c_6279,plain,(
    ! [A_373,B_374] :
      ( k10_relat_1(k6_relat_1(A_373),B_374) = A_373
      | ~ r1_tarski(A_373,B_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6118,c_339])).

tff(c_1105,plain,(
    ! [A_181,B_182] :
      ( k3_xboole_0(A_181,k9_relat_1(B_182,k1_relat_1(B_182))) = k9_relat_1(B_182,k10_relat_1(B_182,A_181))
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1117,plain,(
    ! [A_44,A_181] :
      ( k9_relat_1(k6_relat_1(A_44),k10_relat_1(k6_relat_1(A_44),A_181)) = k3_xboole_0(A_181,k9_relat_1(k6_relat_1(A_44),A_44))
      | ~ v1_funct_1(k6_relat_1(A_44))
      | ~ v1_relat_1(k6_relat_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1105])).

tff(c_1121,plain,(
    ! [A_44,A_181] : k9_relat_1(k6_relat_1(A_44),k10_relat_1(k6_relat_1(A_44),A_181)) = k3_xboole_0(A_181,A_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_542,c_1117])).

tff(c_6438,plain,(
    ! [A_373,B_374] :
      ( k9_relat_1(k6_relat_1(A_373),A_373) = k3_xboole_0(B_374,A_373)
      | ~ r1_tarski(A_373,B_374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6279,c_1121])).

tff(c_6644,plain,(
    ! [B_376,A_377] :
      ( k3_xboole_0(B_376,A_377) = A_377
      | ~ r1_tarski(A_377,B_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_6438])).

tff(c_6747,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_6644])).

tff(c_60,plain,(
    ! [A_58,C_60,B_59] :
      ( k3_xboole_0(A_58,k10_relat_1(C_60,B_59)) = k10_relat_1(k7_relat_1(C_60,A_58),B_59)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6753,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6747,c_60])).

tff(c_6760,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6753])).

tff(c_6762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.14/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.59  
% 7.44/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.60  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.44/2.60  
% 7.44/2.60  %Foreground sorts:
% 7.44/2.60  
% 7.44/2.60  
% 7.44/2.60  %Background operators:
% 7.44/2.60  
% 7.44/2.60  
% 7.44/2.60  %Foreground operators:
% 7.44/2.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.44/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.44/2.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.44/2.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.44/2.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.44/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.44/2.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.44/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.44/2.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.44/2.60  tff('#skF_5', type, '#skF_5': $i).
% 7.44/2.60  tff('#skF_6', type, '#skF_6': $i).
% 7.44/2.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.44/2.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.44/2.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.44/2.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.44/2.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.44/2.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.44/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.44/2.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.44/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.44/2.60  tff('#skF_4', type, '#skF_4': $i).
% 7.44/2.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.44/2.60  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.44/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.44/2.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.44/2.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.44/2.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.44/2.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.44/2.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.44/2.60  
% 7.44/2.61  tff(f_118, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 7.44/2.61  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.44/2.61  tff(f_90, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.44/2.61  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.44/2.61  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 7.44/2.61  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 7.44/2.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.44/2.61  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 7.44/2.61  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 7.44/2.61  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 7.44/2.61  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 7.44/2.61  tff(c_66, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.44/2.61  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.44/2.61  tff(c_68, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.44/2.61  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.44/2.61  tff(c_56, plain, (![A_57]: (v1_relat_1(k6_relat_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.44/2.61  tff(c_34, plain, (![A_44]: (k1_relat_1(k6_relat_1(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.44/2.61  tff(c_36, plain, (![A_44]: (k2_relat_1(k6_relat_1(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.44/2.61  tff(c_113, plain, (![A_76]: (k10_relat_1(A_76, k2_relat_1(A_76))=k1_relat_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.44/2.61  tff(c_122, plain, (![A_44]: (k10_relat_1(k6_relat_1(A_44), A_44)=k1_relat_1(k6_relat_1(A_44)) | ~v1_relat_1(k6_relat_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_113])).
% 7.44/2.61  tff(c_126, plain, (![A_44]: (k10_relat_1(k6_relat_1(A_44), A_44)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_34, c_122])).
% 7.44/2.61  tff(c_58, plain, (![A_57]: (v1_funct_1(k6_relat_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.44/2.61  tff(c_512, plain, (![B_138, A_139]: (k9_relat_1(B_138, k10_relat_1(B_138, A_139))=A_139 | ~r1_tarski(A_139, k2_relat_1(B_138)) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.44/2.61  tff(c_517, plain, (![A_44, A_139]: (k9_relat_1(k6_relat_1(A_44), k10_relat_1(k6_relat_1(A_44), A_139))=A_139 | ~r1_tarski(A_139, A_44) | ~v1_funct_1(k6_relat_1(A_44)) | ~v1_relat_1(k6_relat_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_512])).
% 7.44/2.61  tff(c_525, plain, (![A_140, A_141]: (k9_relat_1(k6_relat_1(A_140), k10_relat_1(k6_relat_1(A_140), A_141))=A_141 | ~r1_tarski(A_141, A_140))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_517])).
% 7.44/2.61  tff(c_534, plain, (![A_44]: (k9_relat_1(k6_relat_1(A_44), A_44)=A_44 | ~r1_tarski(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_126, c_525])).
% 7.44/2.61  tff(c_542, plain, (![A_44]: (k9_relat_1(k6_relat_1(A_44), A_44)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_534])).
% 7.44/2.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.44/2.61  tff(c_468, plain, (![D_134, A_135, B_136]: (r2_hidden(D_134, k1_relat_1(A_135)) | ~r2_hidden(D_134, k10_relat_1(A_135, B_136)) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.44/2.61  tff(c_5983, plain, (![A_366, B_367, B_368]: (r2_hidden('#skF_1'(k10_relat_1(A_366, B_367), B_368), k1_relat_1(A_366)) | ~v1_funct_1(A_366) | ~v1_relat_1(A_366) | r1_tarski(k10_relat_1(A_366, B_367), B_368))), inference(resolution, [status(thm)], [c_6, c_468])).
% 7.44/2.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.44/2.61  tff(c_6035, plain, (![A_369, B_370]: (~v1_funct_1(A_369) | ~v1_relat_1(A_369) | r1_tarski(k10_relat_1(A_369, B_370), k1_relat_1(A_369)))), inference(resolution, [status(thm)], [c_5983, c_4])).
% 7.44/2.61  tff(c_6098, plain, (![A_44, B_370]: (~v1_funct_1(k6_relat_1(A_44)) | ~v1_relat_1(k6_relat_1(A_44)) | r1_tarski(k10_relat_1(k6_relat_1(A_44), B_370), A_44))), inference(superposition, [status(thm), theory('equality')], [c_34, c_6035])).
% 7.44/2.61  tff(c_6118, plain, (![A_44, B_370]: (r1_tarski(k10_relat_1(k6_relat_1(A_44), B_370), A_44))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_6098])).
% 7.44/2.61  tff(c_200, plain, (![C_101, A_102, B_103]: (r1_tarski(k10_relat_1(C_101, A_102), k10_relat_1(C_101, B_103)) | ~r1_tarski(A_102, B_103) | ~v1_relat_1(C_101))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.44/2.61  tff(c_211, plain, (![A_44, B_103]: (r1_tarski(A_44, k10_relat_1(k6_relat_1(A_44), B_103)) | ~r1_tarski(A_44, B_103) | ~v1_relat_1(k6_relat_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_200])).
% 7.44/2.61  tff(c_326, plain, (![A_114, B_115]: (r1_tarski(A_114, k10_relat_1(k6_relat_1(A_114), B_115)) | ~r1_tarski(A_114, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_211])).
% 7.44/2.61  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.44/2.61  tff(c_339, plain, (![A_114, B_115]: (k10_relat_1(k6_relat_1(A_114), B_115)=A_114 | ~r1_tarski(k10_relat_1(k6_relat_1(A_114), B_115), A_114) | ~r1_tarski(A_114, B_115))), inference(resolution, [status(thm)], [c_326, c_8])).
% 7.44/2.61  tff(c_6279, plain, (![A_373, B_374]: (k10_relat_1(k6_relat_1(A_373), B_374)=A_373 | ~r1_tarski(A_373, B_374))), inference(demodulation, [status(thm), theory('equality')], [c_6118, c_339])).
% 7.44/2.61  tff(c_1105, plain, (![A_181, B_182]: (k3_xboole_0(A_181, k9_relat_1(B_182, k1_relat_1(B_182)))=k9_relat_1(B_182, k10_relat_1(B_182, A_181)) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.44/2.61  tff(c_1117, plain, (![A_44, A_181]: (k9_relat_1(k6_relat_1(A_44), k10_relat_1(k6_relat_1(A_44), A_181))=k3_xboole_0(A_181, k9_relat_1(k6_relat_1(A_44), A_44)) | ~v1_funct_1(k6_relat_1(A_44)) | ~v1_relat_1(k6_relat_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1105])).
% 7.44/2.61  tff(c_1121, plain, (![A_44, A_181]: (k9_relat_1(k6_relat_1(A_44), k10_relat_1(k6_relat_1(A_44), A_181))=k3_xboole_0(A_181, A_44))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_542, c_1117])).
% 7.44/2.61  tff(c_6438, plain, (![A_373, B_374]: (k9_relat_1(k6_relat_1(A_373), A_373)=k3_xboole_0(B_374, A_373) | ~r1_tarski(A_373, B_374))), inference(superposition, [status(thm), theory('equality')], [c_6279, c_1121])).
% 7.44/2.61  tff(c_6644, plain, (![B_376, A_377]: (k3_xboole_0(B_376, A_377)=A_377 | ~r1_tarski(A_377, B_376))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_6438])).
% 7.44/2.61  tff(c_6747, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_6644])).
% 7.44/2.61  tff(c_60, plain, (![A_58, C_60, B_59]: (k3_xboole_0(A_58, k10_relat_1(C_60, B_59))=k10_relat_1(k7_relat_1(C_60, A_58), B_59) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.44/2.61  tff(c_6753, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6747, c_60])).
% 7.44/2.61  tff(c_6760, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6753])).
% 7.44/2.61  tff(c_6762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_6760])).
% 7.44/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.61  
% 7.44/2.61  Inference rules
% 7.44/2.61  ----------------------
% 7.44/2.61  #Ref     : 0
% 7.44/2.61  #Sup     : 1556
% 7.44/2.61  #Fact    : 0
% 7.44/2.61  #Define  : 0
% 7.44/2.61  #Split   : 6
% 7.44/2.61  #Chain   : 0
% 7.44/2.61  #Close   : 0
% 7.44/2.61  
% 7.44/2.61  Ordering : KBO
% 7.44/2.61  
% 7.44/2.61  Simplification rules
% 7.44/2.61  ----------------------
% 7.44/2.61  #Subsume      : 306
% 7.44/2.61  #Demod        : 1146
% 7.44/2.61  #Tautology    : 371
% 7.44/2.61  #SimpNegUnit  : 1
% 7.44/2.61  #BackRed      : 3
% 7.44/2.61  
% 7.44/2.61  #Partial instantiations: 0
% 7.44/2.61  #Strategies tried      : 1
% 7.44/2.61  
% 7.44/2.61  Timing (in seconds)
% 7.44/2.61  ----------------------
% 7.44/2.62  Preprocessing        : 0.38
% 7.44/2.62  Parsing              : 0.21
% 7.44/2.62  CNF conversion       : 0.03
% 7.44/2.62  Main loop            : 1.40
% 7.44/2.62  Inferencing          : 0.43
% 7.44/2.62  Reduction            : 0.42
% 7.44/2.62  Demodulation         : 0.30
% 7.44/2.62  BG Simplification    : 0.05
% 7.44/2.62  Subsumption          : 0.41
% 7.44/2.62  Abstraction          : 0.07
% 7.44/2.62  MUC search           : 0.00
% 7.44/2.62  Cooper               : 0.00
% 7.44/2.62  Total                : 1.82
% 7.44/2.62  Index Insertion      : 0.00
% 7.44/2.62  Index Deletion       : 0.00
% 7.44/2.62  Index Matching       : 0.00
% 7.44/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
