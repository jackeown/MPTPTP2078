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
% DateTime   : Thu Dec  3 10:17:29 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 193 expanded)
%              Number of leaves         :   33 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 ( 307 expanded)
%              Number of equality atoms :   39 ( 126 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_99,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_44,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_434,plain,(
    ! [A_87,B_88] :
      ( k5_relat_1(k6_relat_1(A_87),B_88) = k7_relat_1(B_88,A_87)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [B_34,A_33] : k5_relat_1(k6_relat_1(B_34),k6_relat_1(A_33)) = k6_relat_1(k3_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_441,plain,(
    ! [A_33,A_87] :
      ( k7_relat_1(k6_relat_1(A_33),A_87) = k6_relat_1(k3_xboole_0(A_33,A_87))
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_42])).

tff(c_450,plain,(
    ! [A_33,A_87] : k7_relat_1(k6_relat_1(A_33),A_87) = k6_relat_1(k3_xboole_0(A_33,A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_441])).

tff(c_611,plain,(
    ! [B_105,A_106] :
      ( k2_relat_1(k7_relat_1(B_105,A_106)) = k9_relat_1(B_105,A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_623,plain,(
    ! [A_33,A_87] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_33,A_87))) = k9_relat_1(k6_relat_1(A_33),A_87)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_611])).

tff(c_627,plain,(
    ! [A_33,A_87] : k9_relat_1(k6_relat_1(A_33),A_87) = k3_xboole_0(A_33,A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_623])).

tff(c_32,plain,(
    ! [A_22] : v1_funct_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_140,plain,(
    ! [A_55] :
      ( k10_relat_1(A_55,k2_relat_1(A_55)) = k1_relat_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,(
    ! [A_19] :
      ( k10_relat_1(k6_relat_1(A_19),A_19) = k1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_153,plain,(
    ! [A_19] : k10_relat_1(k6_relat_1(A_19),A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_149])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_895,plain,(
    ! [B_128,A_129] :
      ( k9_relat_1(B_128,k10_relat_1(B_128,A_129)) = A_129
      | ~ r1_tarski(A_129,k2_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3591,plain,(
    ! [B_229] :
      ( k9_relat_1(B_229,k10_relat_1(B_229,k2_relat_1(B_229))) = k2_relat_1(B_229)
      | ~ v1_funct_1(B_229)
      | ~ v1_relat_1(B_229) ) ),
    inference(resolution,[status(thm)],[c_6,c_895])).

tff(c_3620,plain,(
    ! [A_19] :
      ( k9_relat_1(k6_relat_1(A_19),k10_relat_1(k6_relat_1(A_19),A_19)) = k2_relat_1(k6_relat_1(A_19))
      | ~ v1_funct_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3591])).

tff(c_3629,plain,(
    ! [A_19] : k3_xboole_0(A_19,A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_627,c_153,c_26,c_3620])).

tff(c_932,plain,(
    ! [A_19,A_129] :
      ( k9_relat_1(k6_relat_1(A_19),k10_relat_1(k6_relat_1(A_19),A_129)) = A_129
      | ~ r1_tarski(A_129,A_19)
      | ~ v1_funct_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_895])).

tff(c_6722,plain,(
    ! [A_345,A_346] :
      ( k3_xboole_0(A_345,k10_relat_1(k6_relat_1(A_345),A_346)) = A_346
      | ~ r1_tarski(A_346,A_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_627,c_932])).

tff(c_34,plain,(
    ! [A_23,C_25,B_24] :
      ( k3_xboole_0(A_23,k10_relat_1(C_25,B_24)) = k10_relat_1(k7_relat_1(C_25,A_23),B_24)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6959,plain,(
    ! [A_345,A_346] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_345),A_345),A_346) = A_346
      | ~ v1_relat_1(k6_relat_1(A_345))
      | ~ r1_tarski(A_346,A_345) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6722,c_34])).

tff(c_7048,plain,(
    ! [A_347,A_348] :
      ( k10_relat_1(k6_relat_1(A_347),A_348) = A_348
      | ~ r1_tarski(A_348,A_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3629,c_450,c_6959])).

tff(c_2000,plain,(
    ! [A_167,C_168,B_169] :
      ( r1_tarski(A_167,k10_relat_1(C_168,B_169))
      | ~ r1_tarski(k9_relat_1(C_168,A_167),B_169)
      | ~ r1_tarski(A_167,k1_relat_1(C_168))
      | ~ v1_funct_1(C_168)
      | ~ v1_relat_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2020,plain,(
    ! [A_167,C_168] :
      ( r1_tarski(A_167,k10_relat_1(C_168,k9_relat_1(C_168,A_167)))
      | ~ r1_tarski(A_167,k1_relat_1(C_168))
      | ~ v1_funct_1(C_168)
      | ~ v1_relat_1(C_168) ) ),
    inference(resolution,[status(thm)],[c_6,c_2000])).

tff(c_7075,plain,(
    ! [A_167,A_347] :
      ( r1_tarski(A_167,k9_relat_1(k6_relat_1(A_347),A_167))
      | ~ r1_tarski(A_167,k1_relat_1(k6_relat_1(A_347)))
      | ~ v1_funct_1(k6_relat_1(A_347))
      | ~ v1_relat_1(k6_relat_1(A_347))
      | ~ r1_tarski(k9_relat_1(k6_relat_1(A_347),A_167),A_347) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7048,c_2020])).

tff(c_8199,plain,(
    ! [A_358,A_359] :
      ( r1_tarski(A_358,k3_xboole_0(A_359,A_358))
      | ~ r1_tarski(A_358,A_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_627,c_30,c_32,c_24,c_627,c_7075])).

tff(c_628,plain,(
    ! [A_107,C_108,B_109] :
      ( k3_xboole_0(A_107,k10_relat_1(C_108,B_109)) = k10_relat_1(k7_relat_1(C_108,A_107),B_109)
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_709,plain,(
    ! [C_114,A_115,B_116] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_114,A_115),B_116),A_115)
      | ~ v1_relat_1(C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_12])).

tff(c_717,plain,(
    ! [A_33,A_87,B_116] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_33,A_87)),B_116),A_87)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_709])).

tff(c_784,plain,(
    ! [A_118,A_119,B_120] : r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_118,A_119)),B_120),A_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_717])).

tff(c_805,plain,(
    ! [A_121,A_122] : r1_tarski(k3_xboole_0(A_121,A_122),A_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_784])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_814,plain,(
    ! [A_121,A_122] :
      ( k3_xboole_0(A_121,A_122) = A_122
      | ~ r1_tarski(A_122,k3_xboole_0(A_121,A_122)) ) ),
    inference(resolution,[status(thm)],[c_805,c_2])).

tff(c_8273,plain,(
    ! [A_360,A_361] :
      ( k3_xboole_0(A_360,A_361) = A_361
      | ~ r1_tarski(A_361,A_360) ) ),
    inference(resolution,[status(thm)],[c_8199,c_814])).

tff(c_8551,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_8273])).

tff(c_9606,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8551,c_34])).

tff(c_9686,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9606])).

tff(c_9688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_9686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.75/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/2.67  
% 7.75/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/2.67  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.75/2.67  
% 7.75/2.67  %Foreground sorts:
% 7.75/2.67  
% 7.75/2.67  
% 7.75/2.67  %Background operators:
% 7.75/2.67  
% 7.75/2.67  
% 7.75/2.67  %Foreground operators:
% 7.75/2.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.75/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.75/2.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.75/2.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.75/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.75/2.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.75/2.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.75/2.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.75/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.75/2.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.75/2.67  tff('#skF_3', type, '#skF_3': $i).
% 7.75/2.67  tff('#skF_1', type, '#skF_1': $i).
% 7.75/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.75/2.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.75/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.75/2.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.75/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.75/2.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.75/2.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.75/2.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.75/2.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.75/2.67  
% 7.82/2.69  tff(f_109, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 7.82/2.69  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.82/2.69  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.82/2.69  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.82/2.69  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 7.82/2.69  tff(f_99, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 7.82/2.69  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 7.82/2.69  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 7.82/2.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.82/2.69  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 7.82/2.69  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 7.82/2.69  tff(f_97, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 7.82/2.69  tff(c_44, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.82/2.69  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.82/2.69  tff(c_46, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.82/2.69  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.82/2.69  tff(c_30, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.82/2.69  tff(c_26, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.82/2.69  tff(c_434, plain, (![A_87, B_88]: (k5_relat_1(k6_relat_1(A_87), B_88)=k7_relat_1(B_88, A_87) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.82/2.69  tff(c_42, plain, (![B_34, A_33]: (k5_relat_1(k6_relat_1(B_34), k6_relat_1(A_33))=k6_relat_1(k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.82/2.69  tff(c_441, plain, (![A_33, A_87]: (k7_relat_1(k6_relat_1(A_33), A_87)=k6_relat_1(k3_xboole_0(A_33, A_87)) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_434, c_42])).
% 7.82/2.69  tff(c_450, plain, (![A_33, A_87]: (k7_relat_1(k6_relat_1(A_33), A_87)=k6_relat_1(k3_xboole_0(A_33, A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_441])).
% 7.82/2.69  tff(c_611, plain, (![B_105, A_106]: (k2_relat_1(k7_relat_1(B_105, A_106))=k9_relat_1(B_105, A_106) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.82/2.69  tff(c_623, plain, (![A_33, A_87]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_33, A_87)))=k9_relat_1(k6_relat_1(A_33), A_87) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_450, c_611])).
% 7.82/2.69  tff(c_627, plain, (![A_33, A_87]: (k9_relat_1(k6_relat_1(A_33), A_87)=k3_xboole_0(A_33, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_623])).
% 7.82/2.69  tff(c_32, plain, (![A_22]: (v1_funct_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.82/2.69  tff(c_24, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.82/2.69  tff(c_140, plain, (![A_55]: (k10_relat_1(A_55, k2_relat_1(A_55))=k1_relat_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.82/2.69  tff(c_149, plain, (![A_19]: (k10_relat_1(k6_relat_1(A_19), A_19)=k1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_140])).
% 7.82/2.69  tff(c_153, plain, (![A_19]: (k10_relat_1(k6_relat_1(A_19), A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_149])).
% 7.82/2.69  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.82/2.69  tff(c_895, plain, (![B_128, A_129]: (k9_relat_1(B_128, k10_relat_1(B_128, A_129))=A_129 | ~r1_tarski(A_129, k2_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.82/2.69  tff(c_3591, plain, (![B_229]: (k9_relat_1(B_229, k10_relat_1(B_229, k2_relat_1(B_229)))=k2_relat_1(B_229) | ~v1_funct_1(B_229) | ~v1_relat_1(B_229))), inference(resolution, [status(thm)], [c_6, c_895])).
% 7.82/2.69  tff(c_3620, plain, (![A_19]: (k9_relat_1(k6_relat_1(A_19), k10_relat_1(k6_relat_1(A_19), A_19))=k2_relat_1(k6_relat_1(A_19)) | ~v1_funct_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3591])).
% 7.82/2.69  tff(c_3629, plain, (![A_19]: (k3_xboole_0(A_19, A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_627, c_153, c_26, c_3620])).
% 7.82/2.69  tff(c_932, plain, (![A_19, A_129]: (k9_relat_1(k6_relat_1(A_19), k10_relat_1(k6_relat_1(A_19), A_129))=A_129 | ~r1_tarski(A_129, A_19) | ~v1_funct_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_895])).
% 7.82/2.69  tff(c_6722, plain, (![A_345, A_346]: (k3_xboole_0(A_345, k10_relat_1(k6_relat_1(A_345), A_346))=A_346 | ~r1_tarski(A_346, A_345))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_627, c_932])).
% 7.82/2.69  tff(c_34, plain, (![A_23, C_25, B_24]: (k3_xboole_0(A_23, k10_relat_1(C_25, B_24))=k10_relat_1(k7_relat_1(C_25, A_23), B_24) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.82/2.69  tff(c_6959, plain, (![A_345, A_346]: (k10_relat_1(k7_relat_1(k6_relat_1(A_345), A_345), A_346)=A_346 | ~v1_relat_1(k6_relat_1(A_345)) | ~r1_tarski(A_346, A_345))), inference(superposition, [status(thm), theory('equality')], [c_6722, c_34])).
% 7.82/2.69  tff(c_7048, plain, (![A_347, A_348]: (k10_relat_1(k6_relat_1(A_347), A_348)=A_348 | ~r1_tarski(A_348, A_347))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3629, c_450, c_6959])).
% 7.82/2.69  tff(c_2000, plain, (![A_167, C_168, B_169]: (r1_tarski(A_167, k10_relat_1(C_168, B_169)) | ~r1_tarski(k9_relat_1(C_168, A_167), B_169) | ~r1_tarski(A_167, k1_relat_1(C_168)) | ~v1_funct_1(C_168) | ~v1_relat_1(C_168))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.82/2.69  tff(c_2020, plain, (![A_167, C_168]: (r1_tarski(A_167, k10_relat_1(C_168, k9_relat_1(C_168, A_167))) | ~r1_tarski(A_167, k1_relat_1(C_168)) | ~v1_funct_1(C_168) | ~v1_relat_1(C_168))), inference(resolution, [status(thm)], [c_6, c_2000])).
% 7.82/2.69  tff(c_7075, plain, (![A_167, A_347]: (r1_tarski(A_167, k9_relat_1(k6_relat_1(A_347), A_167)) | ~r1_tarski(A_167, k1_relat_1(k6_relat_1(A_347))) | ~v1_funct_1(k6_relat_1(A_347)) | ~v1_relat_1(k6_relat_1(A_347)) | ~r1_tarski(k9_relat_1(k6_relat_1(A_347), A_167), A_347))), inference(superposition, [status(thm), theory('equality')], [c_7048, c_2020])).
% 7.82/2.69  tff(c_8199, plain, (![A_358, A_359]: (r1_tarski(A_358, k3_xboole_0(A_359, A_358)) | ~r1_tarski(A_358, A_359))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_627, c_30, c_32, c_24, c_627, c_7075])).
% 7.82/2.69  tff(c_628, plain, (![A_107, C_108, B_109]: (k3_xboole_0(A_107, k10_relat_1(C_108, B_109))=k10_relat_1(k7_relat_1(C_108, A_107), B_109) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.82/2.69  tff(c_709, plain, (![C_114, A_115, B_116]: (r1_tarski(k10_relat_1(k7_relat_1(C_114, A_115), B_116), A_115) | ~v1_relat_1(C_114))), inference(superposition, [status(thm), theory('equality')], [c_628, c_12])).
% 7.82/2.69  tff(c_717, plain, (![A_33, A_87, B_116]: (r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_33, A_87)), B_116), A_87) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_450, c_709])).
% 7.82/2.69  tff(c_784, plain, (![A_118, A_119, B_120]: (r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_118, A_119)), B_120), A_119))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_717])).
% 7.82/2.69  tff(c_805, plain, (![A_121, A_122]: (r1_tarski(k3_xboole_0(A_121, A_122), A_122))), inference(superposition, [status(thm), theory('equality')], [c_153, c_784])).
% 7.82/2.69  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.82/2.69  tff(c_814, plain, (![A_121, A_122]: (k3_xboole_0(A_121, A_122)=A_122 | ~r1_tarski(A_122, k3_xboole_0(A_121, A_122)))), inference(resolution, [status(thm)], [c_805, c_2])).
% 7.82/2.69  tff(c_8273, plain, (![A_360, A_361]: (k3_xboole_0(A_360, A_361)=A_361 | ~r1_tarski(A_361, A_360))), inference(resolution, [status(thm)], [c_8199, c_814])).
% 7.82/2.69  tff(c_8551, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_8273])).
% 7.82/2.69  tff(c_9606, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8551, c_34])).
% 7.82/2.69  tff(c_9686, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_9606])).
% 7.82/2.69  tff(c_9688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_9686])).
% 7.82/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.69  
% 7.82/2.69  Inference rules
% 7.82/2.69  ----------------------
% 7.82/2.69  #Ref     : 0
% 7.82/2.69  #Sup     : 2375
% 7.82/2.69  #Fact    : 0
% 7.82/2.69  #Define  : 0
% 7.82/2.69  #Split   : 1
% 7.82/2.69  #Chain   : 0
% 7.82/2.69  #Close   : 0
% 7.82/2.69  
% 7.82/2.69  Ordering : KBO
% 7.82/2.69  
% 7.82/2.69  Simplification rules
% 7.82/2.69  ----------------------
% 7.82/2.69  #Subsume      : 84
% 7.82/2.69  #Demod        : 1315
% 7.82/2.69  #Tautology    : 1142
% 7.82/2.69  #SimpNegUnit  : 1
% 7.82/2.69  #BackRed      : 2
% 7.82/2.69  
% 7.82/2.69  #Partial instantiations: 0
% 7.82/2.69  #Strategies tried      : 1
% 7.82/2.69  
% 7.82/2.69  Timing (in seconds)
% 7.82/2.69  ----------------------
% 7.82/2.69  Preprocessing        : 0.34
% 7.82/2.69  Parsing              : 0.18
% 7.82/2.69  CNF conversion       : 0.02
% 7.82/2.69  Main loop            : 1.58
% 7.82/2.69  Inferencing          : 0.44
% 7.82/2.69  Reduction            : 0.70
% 7.82/2.69  Demodulation         : 0.58
% 7.82/2.69  BG Simplification    : 0.06
% 7.82/2.69  Subsumption          : 0.29
% 7.82/2.69  Abstraction          : 0.07
% 7.82/2.69  MUC search           : 0.00
% 7.82/2.69  Cooper               : 0.00
% 7.82/2.69  Total                : 1.96
% 7.82/2.69  Index Insertion      : 0.00
% 7.82/2.69  Index Deletion       : 0.00
% 7.82/2.69  Index Matching       : 0.00
% 7.82/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
