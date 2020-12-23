%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:27 EST 2020

% Result     : Theorem 6.76s
% Output     : CNFRefutation 6.76s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 152 expanded)
%              Number of leaves         :   35 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  119 ( 266 expanded)
%              Number of equality atoms :   32 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_58,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_60,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    ! [A_29] : v1_relat_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,(
    ! [A_53] :
      ( k10_relat_1(A_53,k2_relat_1(A_53)) = k1_relat_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,(
    ! [A_16] :
      ( k10_relat_1(k6_relat_1(A_16),A_16) = k1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_105])).

tff(c_118,plain,(
    ! [A_16] : k10_relat_1(k6_relat_1(A_16),A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22,c_114])).

tff(c_46,plain,(
    ! [A_29] : v1_funct_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_366,plain,(
    ! [B_92,A_93] :
      ( k9_relat_1(B_92,k10_relat_1(B_92,A_93)) = A_93
      | ~ r1_tarski(A_93,k2_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_379,plain,(
    ! [A_16,A_93] :
      ( k9_relat_1(k6_relat_1(A_16),k10_relat_1(k6_relat_1(A_16),A_93)) = A_93
      | ~ r1_tarski(A_93,A_16)
      | ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_366])).

tff(c_390,plain,(
    ! [A_94,A_95] :
      ( k9_relat_1(k6_relat_1(A_94),k10_relat_1(k6_relat_1(A_94),A_95)) = A_95
      | ~ r1_tarski(A_95,A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_379])).

tff(c_406,plain,(
    ! [A_16] :
      ( k9_relat_1(k6_relat_1(A_16),A_16) = A_16
      | ~ r1_tarski(A_16,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_390])).

tff(c_418,plain,(
    ! [A_16] : k9_relat_1(k6_relat_1(A_16),A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_406])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_296,plain,(
    ! [D_84,A_85,B_86] :
      ( r2_hidden(D_84,k1_relat_1(A_85))
      | ~ r2_hidden(D_84,k10_relat_1(A_85,B_86))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7190,plain,(
    ! [A_341,B_342,B_343] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_341,B_342),B_343),k1_relat_1(A_341))
      | ~ v1_funct_1(A_341)
      | ~ v1_relat_1(A_341)
      | r1_tarski(k10_relat_1(A_341,B_342),B_343) ) ),
    inference(resolution,[status(thm)],[c_6,c_296])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7228,plain,(
    ! [A_344,B_345] :
      ( ~ v1_funct_1(A_344)
      | ~ v1_relat_1(A_344)
      | r1_tarski(k10_relat_1(A_344,B_345),k1_relat_1(A_344)) ) ),
    inference(resolution,[status(thm)],[c_7190,c_4])).

tff(c_7263,plain,(
    ! [A_16,B_345] :
      ( ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16))
      | r1_tarski(k10_relat_1(k6_relat_1(A_16),B_345),A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_7228])).

tff(c_7273,plain,(
    ! [A_16,B_345] : r1_tarski(k10_relat_1(k6_relat_1(A_16),B_345),A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_7263])).

tff(c_1029,plain,(
    ! [A_134,C_135,B_136] :
      ( r1_tarski(A_134,k10_relat_1(C_135,B_136))
      | ~ r1_tarski(k9_relat_1(C_135,A_134),B_136)
      | ~ r1_tarski(A_134,k1_relat_1(C_135))
      | ~ v1_funct_1(C_135)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1041,plain,(
    ! [A_16,B_136] :
      ( r1_tarski(A_16,k10_relat_1(k6_relat_1(A_16),B_136))
      | ~ r1_tarski(A_16,B_136)
      | ~ r1_tarski(A_16,k1_relat_1(k6_relat_1(A_16)))
      | ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_1029])).

tff(c_1068,plain,(
    ! [A_137,B_138] :
      ( r1_tarski(A_137,k10_relat_1(k6_relat_1(A_137),B_138))
      | ~ r1_tarski(A_137,B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_12,c_22,c_1041])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1090,plain,(
    ! [A_137,B_138] :
      ( k10_relat_1(k6_relat_1(A_137),B_138) = A_137
      | ~ r1_tarski(k10_relat_1(k6_relat_1(A_137),B_138),A_137)
      | ~ r1_tarski(A_137,B_138) ) ),
    inference(resolution,[status(thm)],[c_1068,c_8])).

tff(c_7371,plain,(
    ! [A_348,B_349] :
      ( k10_relat_1(k6_relat_1(A_348),B_349) = A_348
      | ~ r1_tarski(A_348,B_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7273,c_1090])).

tff(c_567,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(A_106,k9_relat_1(B_107,k1_relat_1(B_107))) = k9_relat_1(B_107,k10_relat_1(B_107,A_106))
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_579,plain,(
    ! [A_16,A_106] :
      ( k9_relat_1(k6_relat_1(A_16),k10_relat_1(k6_relat_1(A_16),A_106)) = k3_xboole_0(A_106,k9_relat_1(k6_relat_1(A_16),A_16))
      | ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_567])).

tff(c_583,plain,(
    ! [A_16,A_106] : k9_relat_1(k6_relat_1(A_16),k10_relat_1(k6_relat_1(A_16),A_106)) = k3_xboole_0(A_106,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_418,c_579])).

tff(c_7461,plain,(
    ! [A_348,B_349] :
      ( k9_relat_1(k6_relat_1(A_348),A_348) = k3_xboole_0(B_349,A_348)
      | ~ r1_tarski(A_348,B_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7371,c_583])).

tff(c_7599,plain,(
    ! [B_351,A_352] :
      ( k3_xboole_0(B_351,A_352) = A_352
      | ~ r1_tarski(A_352,B_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_7461])).

tff(c_7774,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_7599])).

tff(c_48,plain,(
    ! [A_30,C_32,B_31] :
      ( k3_xboole_0(A_30,k10_relat_1(C_32,B_31)) = k10_relat_1(k7_relat_1(C_32,A_30),B_31)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8523,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7774,c_48])).

tff(c_8544,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8523])).

tff(c_8546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.76/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.75  
% 6.76/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.75  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.76/2.75  
% 6.76/2.75  %Foreground sorts:
% 6.76/2.75  
% 6.76/2.75  
% 6.76/2.75  %Background operators:
% 6.76/2.75  
% 6.76/2.75  
% 6.76/2.75  %Foreground operators:
% 6.76/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.76/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.76/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.76/2.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.76/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.76/2.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.76/2.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.76/2.75  tff('#skF_5', type, '#skF_5': $i).
% 6.76/2.75  tff('#skF_6', type, '#skF_6': $i).
% 6.76/2.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.76/2.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.76/2.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.76/2.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.76/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.76/2.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.76/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.76/2.75  tff('#skF_4', type, '#skF_4': $i).
% 6.76/2.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.76/2.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.76/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.76/2.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.76/2.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.76/2.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.76/2.75  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.76/2.75  
% 6.76/2.77  tff(f_118, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 6.76/2.77  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.76/2.77  tff(f_74, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.76/2.77  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.76/2.77  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 6.76/2.77  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 6.76/2.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.76/2.77  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 6.76/2.77  tff(f_108, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 6.76/2.77  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 6.76/2.77  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 6.76/2.77  tff(c_58, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.76/2.77  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.76/2.77  tff(c_60, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.76/2.77  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.76/2.77  tff(c_44, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.76/2.77  tff(c_22, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.76/2.77  tff(c_24, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.76/2.77  tff(c_105, plain, (![A_53]: (k10_relat_1(A_53, k2_relat_1(A_53))=k1_relat_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.76/2.77  tff(c_114, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=k1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_105])).
% 6.76/2.77  tff(c_118, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22, c_114])).
% 6.76/2.77  tff(c_46, plain, (![A_29]: (v1_funct_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.76/2.77  tff(c_366, plain, (![B_92, A_93]: (k9_relat_1(B_92, k10_relat_1(B_92, A_93))=A_93 | ~r1_tarski(A_93, k2_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.76/2.77  tff(c_379, plain, (![A_16, A_93]: (k9_relat_1(k6_relat_1(A_16), k10_relat_1(k6_relat_1(A_16), A_93))=A_93 | ~r1_tarski(A_93, A_16) | ~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_366])).
% 6.76/2.77  tff(c_390, plain, (![A_94, A_95]: (k9_relat_1(k6_relat_1(A_94), k10_relat_1(k6_relat_1(A_94), A_95))=A_95 | ~r1_tarski(A_95, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_379])).
% 6.76/2.77  tff(c_406, plain, (![A_16]: (k9_relat_1(k6_relat_1(A_16), A_16)=A_16 | ~r1_tarski(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_118, c_390])).
% 6.76/2.77  tff(c_418, plain, (![A_16]: (k9_relat_1(k6_relat_1(A_16), A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_406])).
% 6.76/2.77  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.76/2.77  tff(c_296, plain, (![D_84, A_85, B_86]: (r2_hidden(D_84, k1_relat_1(A_85)) | ~r2_hidden(D_84, k10_relat_1(A_85, B_86)) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.76/2.77  tff(c_7190, plain, (![A_341, B_342, B_343]: (r2_hidden('#skF_1'(k10_relat_1(A_341, B_342), B_343), k1_relat_1(A_341)) | ~v1_funct_1(A_341) | ~v1_relat_1(A_341) | r1_tarski(k10_relat_1(A_341, B_342), B_343))), inference(resolution, [status(thm)], [c_6, c_296])).
% 6.76/2.77  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.76/2.77  tff(c_7228, plain, (![A_344, B_345]: (~v1_funct_1(A_344) | ~v1_relat_1(A_344) | r1_tarski(k10_relat_1(A_344, B_345), k1_relat_1(A_344)))), inference(resolution, [status(thm)], [c_7190, c_4])).
% 6.76/2.77  tff(c_7263, plain, (![A_16, B_345]: (~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)) | r1_tarski(k10_relat_1(k6_relat_1(A_16), B_345), A_16))), inference(superposition, [status(thm), theory('equality')], [c_22, c_7228])).
% 6.76/2.77  tff(c_7273, plain, (![A_16, B_345]: (r1_tarski(k10_relat_1(k6_relat_1(A_16), B_345), A_16))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_7263])).
% 6.76/2.77  tff(c_1029, plain, (![A_134, C_135, B_136]: (r1_tarski(A_134, k10_relat_1(C_135, B_136)) | ~r1_tarski(k9_relat_1(C_135, A_134), B_136) | ~r1_tarski(A_134, k1_relat_1(C_135)) | ~v1_funct_1(C_135) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.76/2.77  tff(c_1041, plain, (![A_16, B_136]: (r1_tarski(A_16, k10_relat_1(k6_relat_1(A_16), B_136)) | ~r1_tarski(A_16, B_136) | ~r1_tarski(A_16, k1_relat_1(k6_relat_1(A_16))) | ~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_418, c_1029])).
% 6.76/2.77  tff(c_1068, plain, (![A_137, B_138]: (r1_tarski(A_137, k10_relat_1(k6_relat_1(A_137), B_138)) | ~r1_tarski(A_137, B_138))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_12, c_22, c_1041])).
% 6.76/2.77  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.76/2.77  tff(c_1090, plain, (![A_137, B_138]: (k10_relat_1(k6_relat_1(A_137), B_138)=A_137 | ~r1_tarski(k10_relat_1(k6_relat_1(A_137), B_138), A_137) | ~r1_tarski(A_137, B_138))), inference(resolution, [status(thm)], [c_1068, c_8])).
% 6.76/2.77  tff(c_7371, plain, (![A_348, B_349]: (k10_relat_1(k6_relat_1(A_348), B_349)=A_348 | ~r1_tarski(A_348, B_349))), inference(demodulation, [status(thm), theory('equality')], [c_7273, c_1090])).
% 6.76/2.77  tff(c_567, plain, (![A_106, B_107]: (k3_xboole_0(A_106, k9_relat_1(B_107, k1_relat_1(B_107)))=k9_relat_1(B_107, k10_relat_1(B_107, A_106)) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.76/2.77  tff(c_579, plain, (![A_16, A_106]: (k9_relat_1(k6_relat_1(A_16), k10_relat_1(k6_relat_1(A_16), A_106))=k3_xboole_0(A_106, k9_relat_1(k6_relat_1(A_16), A_16)) | ~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_567])).
% 6.76/2.77  tff(c_583, plain, (![A_16, A_106]: (k9_relat_1(k6_relat_1(A_16), k10_relat_1(k6_relat_1(A_16), A_106))=k3_xboole_0(A_106, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_418, c_579])).
% 6.76/2.77  tff(c_7461, plain, (![A_348, B_349]: (k9_relat_1(k6_relat_1(A_348), A_348)=k3_xboole_0(B_349, A_348) | ~r1_tarski(A_348, B_349))), inference(superposition, [status(thm), theory('equality')], [c_7371, c_583])).
% 6.76/2.77  tff(c_7599, plain, (![B_351, A_352]: (k3_xboole_0(B_351, A_352)=A_352 | ~r1_tarski(A_352, B_351))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_7461])).
% 6.76/2.77  tff(c_7774, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_7599])).
% 6.76/2.77  tff(c_48, plain, (![A_30, C_32, B_31]: (k3_xboole_0(A_30, k10_relat_1(C_32, B_31))=k10_relat_1(k7_relat_1(C_32, A_30), B_31) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.76/2.77  tff(c_8523, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7774, c_48])).
% 6.76/2.77  tff(c_8544, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8523])).
% 6.76/2.77  tff(c_8546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_8544])).
% 6.76/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.77  
% 6.76/2.77  Inference rules
% 6.76/2.77  ----------------------
% 6.76/2.77  #Ref     : 0
% 6.76/2.77  #Sup     : 2008
% 6.76/2.77  #Fact    : 0
% 6.76/2.77  #Define  : 0
% 6.76/2.77  #Split   : 2
% 6.76/2.77  #Chain   : 0
% 6.76/2.77  #Close   : 0
% 6.76/2.77  
% 6.76/2.77  Ordering : KBO
% 6.76/2.77  
% 6.76/2.77  Simplification rules
% 6.76/2.77  ----------------------
% 6.76/2.77  #Subsume      : 366
% 6.76/2.77  #Demod        : 1123
% 6.76/2.77  #Tautology    : 634
% 6.76/2.77  #SimpNegUnit  : 1
% 6.76/2.77  #BackRed      : 6
% 6.76/2.77  
% 6.76/2.77  #Partial instantiations: 0
% 6.76/2.77  #Strategies tried      : 1
% 6.76/2.77  
% 6.76/2.77  Timing (in seconds)
% 6.76/2.77  ----------------------
% 6.76/2.77  Preprocessing        : 0.48
% 6.76/2.77  Parsing              : 0.27
% 6.76/2.77  CNF conversion       : 0.03
% 6.76/2.77  Main loop            : 1.37
% 6.76/2.77  Inferencing          : 0.45
% 6.76/2.77  Reduction            : 0.48
% 6.76/2.77  Demodulation         : 0.37
% 6.76/2.77  BG Simplification    : 0.06
% 6.76/2.77  Subsumption          : 0.29
% 6.76/2.78  Abstraction          : 0.07
% 6.76/2.78  MUC search           : 0.00
% 6.76/2.78  Cooper               : 0.00
% 6.76/2.78  Total                : 1.89
% 6.76/2.78  Index Insertion      : 0.00
% 6.76/2.78  Index Deletion       : 0.00
% 6.76/2.78  Index Matching       : 0.00
% 6.76/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
