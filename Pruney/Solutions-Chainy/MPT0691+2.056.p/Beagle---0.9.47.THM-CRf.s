%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:46 EST 2020

% Result     : Theorem 6.30s
% Output     : CNFRefutation 6.50s
% Verified   : 
% Statistics : Number of formulae       :  113 (1329 expanded)
%              Number of leaves         :   42 ( 488 expanded)
%              Depth                    :   22
%              Number of atoms          :  181 (2700 expanded)
%              Number of equality atoms :   70 ( 977 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_63,axiom,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_91,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | k4_xboole_0(A_70,B_71) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_95,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_56])).

tff(c_60,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [A_40,B_41] :
      ( v1_relat_1(k7_relat_1(A_40,B_41))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_56,B_57] :
      ( k5_relat_1(k6_relat_1(A_56),B_57) = k7_relat_1(B_57,A_56)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    ! [A_58] : v1_relat_1(k6_relat_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    ! [A_50,B_52] :
      ( k10_relat_1(A_50,k1_relat_1(B_52)) = k1_relat_1(k5_relat_1(A_50,B_52))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    ! [A_53] : k1_relat_1(k6_relat_1(A_53)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    ! [A_53] : k2_relat_1(k6_relat_1(A_53)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_58,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_197,plain,(
    ! [A_88,C_89,B_90] :
      ( r1_tarski(A_88,C_89)
      | ~ r1_tarski(B_90,C_89)
      | ~ r1_tarski(A_88,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_205,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_88,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_58,c_197])).

tff(c_650,plain,(
    ! [B_132,A_133] :
      ( k5_relat_1(B_132,k6_relat_1(A_133)) = B_132
      | ~ r1_tarski(k2_relat_1(B_132),A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1249,plain,(
    ! [B_168] :
      ( k5_relat_1(B_168,k6_relat_1(k1_relat_1('#skF_2'))) = B_168
      | ~ v1_relat_1(B_168)
      | ~ r1_tarski(k2_relat_1(B_168),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_205,c_650])).

tff(c_1271,plain,(
    ! [A_56] :
      ( k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),A_56) = k6_relat_1(A_56)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))
      | ~ v1_relat_1(k6_relat_1(A_56))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(A_56)),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_48])).

tff(c_1296,plain,(
    ! [A_56] :
      ( k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),A_56) = k6_relat_1(A_56)
      | ~ r1_tarski(A_56,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50,c_50,c_1271])).

tff(c_670,plain,(
    ! [B_132] :
      ( k5_relat_1(B_132,k6_relat_1(k2_relat_1(B_132))) = B_132
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_6,c_650])).

tff(c_1118,plain,(
    ! [A_160,C_161,B_162] :
      ( k3_xboole_0(A_160,k10_relat_1(C_161,B_162)) = k10_relat_1(k7_relat_1(C_161,A_160),B_162)
      | ~ v1_relat_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4851,plain,(
    ! [A_301,A_302,B_303] :
      ( k3_xboole_0(A_301,k1_relat_1(k5_relat_1(A_302,B_303))) = k10_relat_1(k7_relat_1(A_302,A_301),k1_relat_1(B_303))
      | ~ v1_relat_1(A_302)
      | ~ v1_relat_1(B_303)
      | ~ v1_relat_1(A_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1118])).

tff(c_4906,plain,(
    ! [B_132,A_301] :
      ( k10_relat_1(k7_relat_1(B_132,A_301),k1_relat_1(k6_relat_1(k2_relat_1(B_132)))) = k3_xboole_0(A_301,k1_relat_1(B_132))
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(B_132)))
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_4851])).

tff(c_5215,plain,(
    ! [B_310,A_311] :
      ( k10_relat_1(k7_relat_1(B_310,A_311),k2_relat_1(B_310)) = k3_xboole_0(A_311,k1_relat_1(B_310))
      | ~ v1_relat_1(B_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_4906])).

tff(c_5241,plain,(
    ! [A_56] :
      ( k10_relat_1(k6_relat_1(A_56),k2_relat_1(k6_relat_1(k1_relat_1('#skF_2')))) = k3_xboole_0(A_56,k1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_56,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_5215])).

tff(c_5565,plain,(
    ! [A_317] :
      ( k10_relat_1(k6_relat_1(A_317),k1_relat_1('#skF_2')) = k3_xboole_0(A_317,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_317,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_44,c_5241])).

tff(c_5651,plain,(
    ! [A_317] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_317),'#skF_2')) = k3_xboole_0(A_317,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_317,'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k6_relat_1(A_317)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5565])).

tff(c_6403,plain,(
    ! [A_341] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_341),'#skF_2')) = k3_xboole_0(A_341,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_341,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_5651])).

tff(c_6482,plain,(
    ! [A_56] :
      ( k3_xboole_0(A_56,k1_relat_1('#skF_2')) = k1_relat_1(k7_relat_1('#skF_2',A_56))
      | ~ r1_tarski(A_56,'#skF_1')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_6403])).

tff(c_6497,plain,(
    ! [A_342] :
      ( k3_xboole_0(A_342,k1_relat_1('#skF_2')) = k1_relat_1(k7_relat_1('#skF_2',A_342))
      | ~ r1_tarski(A_342,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6482])).

tff(c_661,plain,(
    ! [A_53,A_133] :
      ( k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_133)) = k6_relat_1(A_53)
      | ~ r1_tarski(A_53,A_133)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_650])).

tff(c_741,plain,(
    ! [A_139,A_140] :
      ( k5_relat_1(k6_relat_1(A_139),k6_relat_1(A_140)) = k6_relat_1(A_139)
      | ~ r1_tarski(A_139,A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_661])).

tff(c_755,plain,(
    ! [A_140,A_139] :
      ( k7_relat_1(k6_relat_1(A_140),A_139) = k6_relat_1(A_139)
      | ~ v1_relat_1(k6_relat_1(A_140))
      | ~ r1_tarski(A_139,A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_48])).

tff(c_778,plain,(
    ! [A_140,A_139] :
      ( k7_relat_1(k6_relat_1(A_140),A_139) = k6_relat_1(A_139)
      | ~ r1_tarski(A_139,A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_755])).

tff(c_671,plain,(
    ! [B_134] :
      ( k5_relat_1(B_134,k6_relat_1(k2_relat_1(B_134))) = B_134
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_6,c_650])).

tff(c_688,plain,(
    ! [A_53] :
      ( k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_53)) = k6_relat_1(A_53)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_671])).

tff(c_696,plain,(
    ! [A_53] : k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_53)) = k6_relat_1(A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_688])).

tff(c_845,plain,(
    ! [A_145,B_146] :
      ( k10_relat_1(A_145,k1_relat_1(B_146)) = k1_relat_1(k5_relat_1(A_145,B_146))
      | ~ v1_relat_1(B_146)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_854,plain,(
    ! [A_145,A_53] :
      ( k1_relat_1(k5_relat_1(A_145,k6_relat_1(A_53))) = k10_relat_1(A_145,A_53)
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_845])).

tff(c_859,plain,(
    ! [A_147,A_148] :
      ( k1_relat_1(k5_relat_1(A_147,k6_relat_1(A_148))) = k10_relat_1(A_147,A_148)
      | ~ v1_relat_1(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_854])).

tff(c_880,plain,(
    ! [A_53] :
      ( k10_relat_1(k6_relat_1(A_53),A_53) = k1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_859])).

tff(c_893,plain,(
    ! [A_53] : k10_relat_1(k6_relat_1(A_53),A_53) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_880])).

tff(c_1136,plain,(
    ! [A_53,A_160] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_53),A_160),A_53) = k3_xboole_0(A_160,A_53)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_1118])).

tff(c_1146,plain,(
    ! [A_163,A_164] : k10_relat_1(k7_relat_1(k6_relat_1(A_163),A_164),A_163) = k3_xboole_0(A_164,A_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1136])).

tff(c_1194,plain,(
    ! [A_166,A_167] :
      ( k10_relat_1(k6_relat_1(A_166),A_167) = k3_xboole_0(A_166,A_167)
      | ~ r1_tarski(A_166,A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_1146])).

tff(c_669,plain,(
    ! [A_53,A_133] :
      ( k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_133)) = k6_relat_1(A_53)
      | ~ r1_tarski(A_53,A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_661])).

tff(c_877,plain,(
    ! [A_53,A_133] :
      ( k10_relat_1(k6_relat_1(A_53),A_133) = k1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ r1_tarski(A_53,A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_859])).

tff(c_891,plain,(
    ! [A_53,A_133] :
      ( k10_relat_1(k6_relat_1(A_53),A_133) = A_53
      | ~ r1_tarski(A_53,A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_877])).

tff(c_1460,plain,(
    ! [A_178,A_179] :
      ( k3_xboole_0(A_178,A_179) = A_178
      | ~ r1_tarski(A_178,A_179)
      | ~ r1_tarski(A_178,A_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_891])).

tff(c_1478,plain,
    ( k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_1460])).

tff(c_1495,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1478])).

tff(c_6516,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6497,c_1495])).

tff(c_6551,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6516])).

tff(c_34,plain,(
    ! [A_42] :
      ( k9_relat_1(A_42,k1_relat_1(A_42)) = k2_relat_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1744,plain,(
    ! [A_187,C_188,B_189] :
      ( k9_relat_1(k7_relat_1(A_187,C_188),B_189) = k9_relat_1(A_187,B_189)
      | ~ r1_tarski(B_189,C_188)
      | ~ v1_relat_1(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1791,plain,(
    ! [A_187,C_188] :
      ( k9_relat_1(A_187,k1_relat_1(k7_relat_1(A_187,C_188))) = k2_relat_1(k7_relat_1(A_187,C_188))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(A_187,C_188)),C_188)
      | ~ v1_relat_1(A_187)
      | ~ v1_relat_1(k7_relat_1(A_187,C_188)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1744])).

tff(c_6559,plain,
    ( k9_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6551,c_1791])).

tff(c_6617,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_6551,c_6559])).

tff(c_6771,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6617])).

tff(c_6774,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_6771])).

tff(c_6778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6774])).

tff(c_6780,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6617])).

tff(c_6779,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_6617])).

tff(c_883,plain,(
    ! [B_132] :
      ( k10_relat_1(B_132,k2_relat_1(B_132)) = k1_relat_1(B_132)
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_859])).

tff(c_6808,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6779,c_883])).

tff(c_6837,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_6780,c_6551,c_6808])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1124,plain,(
    ! [A_160,C_161,B_162] :
      ( k5_xboole_0(A_160,k10_relat_1(k7_relat_1(C_161,A_160),B_162)) = k4_xboole_0(A_160,k10_relat_1(C_161,B_162))
      | ~ v1_relat_1(C_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_12])).

tff(c_6977,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6837,c_1124])).

tff(c_6984,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_16,c_6977])).

tff(c_6986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_6984])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:38:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.30/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.28  
% 6.30/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.28  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.30/2.28  
% 6.30/2.28  %Foreground sorts:
% 6.30/2.28  
% 6.30/2.28  
% 6.30/2.28  %Background operators:
% 6.30/2.28  
% 6.30/2.28  
% 6.30/2.28  %Foreground operators:
% 6.30/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.30/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.30/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.30/2.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.30/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.30/2.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.30/2.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.30/2.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.30/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.30/2.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.30/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.30/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.30/2.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.30/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.30/2.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.30/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.30/2.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.30/2.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.30/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.30/2.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.30/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.30/2.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.30/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.30/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.30/2.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.30/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.30/2.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.30/2.28  
% 6.50/2.30  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.50/2.30  tff(f_114, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 6.50/2.30  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.50/2.30  tff(f_63, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.50/2.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.50/2.30  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 6.50/2.30  tff(f_103, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.50/2.30  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 6.50/2.30  tff(f_89, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.50/2.30  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.50/2.30  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 6.50/2.30  tff(f_107, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 6.50/2.30  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 6.50/2.30  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 6.50/2.30  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.50/2.30  tff(c_91, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | k4_xboole_0(A_70, B_71)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.50/2.30  tff(c_56, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.50/2.30  tff(c_95, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_56])).
% 6.50/2.30  tff(c_60, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.50/2.30  tff(c_16, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.50/2.30  tff(c_32, plain, (![A_40, B_41]: (v1_relat_1(k7_relat_1(A_40, B_41)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.50/2.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.50/2.30  tff(c_48, plain, (![A_56, B_57]: (k5_relat_1(k6_relat_1(A_56), B_57)=k7_relat_1(B_57, A_56) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.50/2.30  tff(c_50, plain, (![A_58]: (v1_relat_1(k6_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.50/2.30  tff(c_40, plain, (![A_50, B_52]: (k10_relat_1(A_50, k1_relat_1(B_52))=k1_relat_1(k5_relat_1(A_50, B_52)) | ~v1_relat_1(B_52) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.50/2.30  tff(c_42, plain, (![A_53]: (k1_relat_1(k6_relat_1(A_53))=A_53)), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.50/2.30  tff(c_44, plain, (![A_53]: (k2_relat_1(k6_relat_1(A_53))=A_53)), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.50/2.30  tff(c_58, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.50/2.30  tff(c_197, plain, (![A_88, C_89, B_90]: (r1_tarski(A_88, C_89) | ~r1_tarski(B_90, C_89) | ~r1_tarski(A_88, B_90))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.50/2.30  tff(c_205, plain, (![A_88]: (r1_tarski(A_88, k1_relat_1('#skF_2')) | ~r1_tarski(A_88, '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_197])).
% 6.50/2.30  tff(c_650, plain, (![B_132, A_133]: (k5_relat_1(B_132, k6_relat_1(A_133))=B_132 | ~r1_tarski(k2_relat_1(B_132), A_133) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.50/2.30  tff(c_1249, plain, (![B_168]: (k5_relat_1(B_168, k6_relat_1(k1_relat_1('#skF_2')))=B_168 | ~v1_relat_1(B_168) | ~r1_tarski(k2_relat_1(B_168), '#skF_1'))), inference(resolution, [status(thm)], [c_205, c_650])).
% 6.50/2.30  tff(c_1271, plain, (![A_56]: (k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), A_56)=k6_relat_1(A_56) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(A_56)) | ~r1_tarski(k2_relat_1(k6_relat_1(A_56)), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1249, c_48])).
% 6.50/2.30  tff(c_1296, plain, (![A_56]: (k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), A_56)=k6_relat_1(A_56) | ~r1_tarski(A_56, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_50, c_50, c_1271])).
% 6.50/2.30  tff(c_670, plain, (![B_132]: (k5_relat_1(B_132, k6_relat_1(k2_relat_1(B_132)))=B_132 | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_6, c_650])).
% 6.50/2.30  tff(c_1118, plain, (![A_160, C_161, B_162]: (k3_xboole_0(A_160, k10_relat_1(C_161, B_162))=k10_relat_1(k7_relat_1(C_161, A_160), B_162) | ~v1_relat_1(C_161))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.50/2.30  tff(c_4851, plain, (![A_301, A_302, B_303]: (k3_xboole_0(A_301, k1_relat_1(k5_relat_1(A_302, B_303)))=k10_relat_1(k7_relat_1(A_302, A_301), k1_relat_1(B_303)) | ~v1_relat_1(A_302) | ~v1_relat_1(B_303) | ~v1_relat_1(A_302))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1118])).
% 6.50/2.30  tff(c_4906, plain, (![B_132, A_301]: (k10_relat_1(k7_relat_1(B_132, A_301), k1_relat_1(k6_relat_1(k2_relat_1(B_132))))=k3_xboole_0(A_301, k1_relat_1(B_132)) | ~v1_relat_1(B_132) | ~v1_relat_1(k6_relat_1(k2_relat_1(B_132))) | ~v1_relat_1(B_132) | ~v1_relat_1(B_132))), inference(superposition, [status(thm), theory('equality')], [c_670, c_4851])).
% 6.50/2.30  tff(c_5215, plain, (![B_310, A_311]: (k10_relat_1(k7_relat_1(B_310, A_311), k2_relat_1(B_310))=k3_xboole_0(A_311, k1_relat_1(B_310)) | ~v1_relat_1(B_310))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_4906])).
% 6.50/2.30  tff(c_5241, plain, (![A_56]: (k10_relat_1(k6_relat_1(A_56), k2_relat_1(k6_relat_1(k1_relat_1('#skF_2'))))=k3_xboole_0(A_56, k1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~r1_tarski(A_56, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1296, c_5215])).
% 6.50/2.30  tff(c_5565, plain, (![A_317]: (k10_relat_1(k6_relat_1(A_317), k1_relat_1('#skF_2'))=k3_xboole_0(A_317, k1_relat_1('#skF_2')) | ~r1_tarski(A_317, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_44, c_5241])).
% 6.50/2.30  tff(c_5651, plain, (![A_317]: (k1_relat_1(k5_relat_1(k6_relat_1(A_317), '#skF_2'))=k3_xboole_0(A_317, k1_relat_1('#skF_2')) | ~r1_tarski(A_317, '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1(A_317)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5565])).
% 6.50/2.30  tff(c_6403, plain, (![A_341]: (k1_relat_1(k5_relat_1(k6_relat_1(A_341), '#skF_2'))=k3_xboole_0(A_341, k1_relat_1('#skF_2')) | ~r1_tarski(A_341, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_5651])).
% 6.50/2.30  tff(c_6482, plain, (![A_56]: (k3_xboole_0(A_56, k1_relat_1('#skF_2'))=k1_relat_1(k7_relat_1('#skF_2', A_56)) | ~r1_tarski(A_56, '#skF_1') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_6403])).
% 6.50/2.30  tff(c_6497, plain, (![A_342]: (k3_xboole_0(A_342, k1_relat_1('#skF_2'))=k1_relat_1(k7_relat_1('#skF_2', A_342)) | ~r1_tarski(A_342, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6482])).
% 6.50/2.30  tff(c_661, plain, (![A_53, A_133]: (k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_133))=k6_relat_1(A_53) | ~r1_tarski(A_53, A_133) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_650])).
% 6.50/2.30  tff(c_741, plain, (![A_139, A_140]: (k5_relat_1(k6_relat_1(A_139), k6_relat_1(A_140))=k6_relat_1(A_139) | ~r1_tarski(A_139, A_140))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_661])).
% 6.50/2.30  tff(c_755, plain, (![A_140, A_139]: (k7_relat_1(k6_relat_1(A_140), A_139)=k6_relat_1(A_139) | ~v1_relat_1(k6_relat_1(A_140)) | ~r1_tarski(A_139, A_140))), inference(superposition, [status(thm), theory('equality')], [c_741, c_48])).
% 6.50/2.30  tff(c_778, plain, (![A_140, A_139]: (k7_relat_1(k6_relat_1(A_140), A_139)=k6_relat_1(A_139) | ~r1_tarski(A_139, A_140))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_755])).
% 6.50/2.30  tff(c_671, plain, (![B_134]: (k5_relat_1(B_134, k6_relat_1(k2_relat_1(B_134)))=B_134 | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_6, c_650])).
% 6.50/2.30  tff(c_688, plain, (![A_53]: (k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_53))=k6_relat_1(A_53) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_671])).
% 6.50/2.30  tff(c_696, plain, (![A_53]: (k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_53))=k6_relat_1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_688])).
% 6.50/2.30  tff(c_845, plain, (![A_145, B_146]: (k10_relat_1(A_145, k1_relat_1(B_146))=k1_relat_1(k5_relat_1(A_145, B_146)) | ~v1_relat_1(B_146) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.50/2.30  tff(c_854, plain, (![A_145, A_53]: (k1_relat_1(k5_relat_1(A_145, k6_relat_1(A_53)))=k10_relat_1(A_145, A_53) | ~v1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(A_145))), inference(superposition, [status(thm), theory('equality')], [c_42, c_845])).
% 6.50/2.30  tff(c_859, plain, (![A_147, A_148]: (k1_relat_1(k5_relat_1(A_147, k6_relat_1(A_148)))=k10_relat_1(A_147, A_148) | ~v1_relat_1(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_854])).
% 6.50/2.30  tff(c_880, plain, (![A_53]: (k10_relat_1(k6_relat_1(A_53), A_53)=k1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_696, c_859])).
% 6.50/2.30  tff(c_893, plain, (![A_53]: (k10_relat_1(k6_relat_1(A_53), A_53)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_880])).
% 6.50/2.30  tff(c_1136, plain, (![A_53, A_160]: (k10_relat_1(k7_relat_1(k6_relat_1(A_53), A_160), A_53)=k3_xboole_0(A_160, A_53) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_893, c_1118])).
% 6.50/2.30  tff(c_1146, plain, (![A_163, A_164]: (k10_relat_1(k7_relat_1(k6_relat_1(A_163), A_164), A_163)=k3_xboole_0(A_164, A_163))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1136])).
% 6.50/2.30  tff(c_1194, plain, (![A_166, A_167]: (k10_relat_1(k6_relat_1(A_166), A_167)=k3_xboole_0(A_166, A_167) | ~r1_tarski(A_166, A_167))), inference(superposition, [status(thm), theory('equality')], [c_778, c_1146])).
% 6.50/2.30  tff(c_669, plain, (![A_53, A_133]: (k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_133))=k6_relat_1(A_53) | ~r1_tarski(A_53, A_133))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_661])).
% 6.50/2.30  tff(c_877, plain, (![A_53, A_133]: (k10_relat_1(k6_relat_1(A_53), A_133)=k1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_53)) | ~r1_tarski(A_53, A_133))), inference(superposition, [status(thm), theory('equality')], [c_669, c_859])).
% 6.50/2.30  tff(c_891, plain, (![A_53, A_133]: (k10_relat_1(k6_relat_1(A_53), A_133)=A_53 | ~r1_tarski(A_53, A_133))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_877])).
% 6.50/2.30  tff(c_1460, plain, (![A_178, A_179]: (k3_xboole_0(A_178, A_179)=A_178 | ~r1_tarski(A_178, A_179) | ~r1_tarski(A_178, A_179))), inference(superposition, [status(thm), theory('equality')], [c_1194, c_891])).
% 6.50/2.30  tff(c_1478, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_1460])).
% 6.50/2.30  tff(c_1495, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1478])).
% 6.50/2.30  tff(c_6516, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6497, c_1495])).
% 6.50/2.30  tff(c_6551, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6516])).
% 6.50/2.30  tff(c_34, plain, (![A_42]: (k9_relat_1(A_42, k1_relat_1(A_42))=k2_relat_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.50/2.30  tff(c_1744, plain, (![A_187, C_188, B_189]: (k9_relat_1(k7_relat_1(A_187, C_188), B_189)=k9_relat_1(A_187, B_189) | ~r1_tarski(B_189, C_188) | ~v1_relat_1(A_187))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.50/2.30  tff(c_1791, plain, (![A_187, C_188]: (k9_relat_1(A_187, k1_relat_1(k7_relat_1(A_187, C_188)))=k2_relat_1(k7_relat_1(A_187, C_188)) | ~r1_tarski(k1_relat_1(k7_relat_1(A_187, C_188)), C_188) | ~v1_relat_1(A_187) | ~v1_relat_1(k7_relat_1(A_187, C_188)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1744])).
% 6.50/2.30  tff(c_6559, plain, (k9_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6551, c_1791])).
% 6.50/2.30  tff(c_6617, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_6551, c_6559])).
% 6.50/2.30  tff(c_6771, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_6617])).
% 6.50/2.30  tff(c_6774, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_6771])).
% 6.50/2.30  tff(c_6778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_6774])).
% 6.50/2.30  tff(c_6780, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_6617])).
% 6.50/2.30  tff(c_6779, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_6617])).
% 6.50/2.30  tff(c_883, plain, (![B_132]: (k10_relat_1(B_132, k2_relat_1(B_132))=k1_relat_1(B_132) | ~v1_relat_1(B_132) | ~v1_relat_1(B_132))), inference(superposition, [status(thm), theory('equality')], [c_670, c_859])).
% 6.50/2.30  tff(c_6808, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6779, c_883])).
% 6.50/2.30  tff(c_6837, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6780, c_6780, c_6551, c_6808])).
% 6.50/2.30  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.50/2.30  tff(c_1124, plain, (![A_160, C_161, B_162]: (k5_xboole_0(A_160, k10_relat_1(k7_relat_1(C_161, A_160), B_162))=k4_xboole_0(A_160, k10_relat_1(C_161, B_162)) | ~v1_relat_1(C_161))), inference(superposition, [status(thm), theory('equality')], [c_1118, c_12])).
% 6.50/2.30  tff(c_6977, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6837, c_1124])).
% 6.50/2.30  tff(c_6984, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_16, c_6977])).
% 6.50/2.30  tff(c_6986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_6984])).
% 6.50/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.30  
% 6.50/2.30  Inference rules
% 6.50/2.30  ----------------------
% 6.50/2.30  #Ref     : 0
% 6.50/2.30  #Sup     : 1580
% 6.50/2.30  #Fact    : 0
% 6.50/2.30  #Define  : 0
% 6.50/2.30  #Split   : 2
% 6.50/2.30  #Chain   : 0
% 6.50/2.30  #Close   : 0
% 6.50/2.30  
% 6.50/2.30  Ordering : KBO
% 6.50/2.30  
% 6.50/2.30  Simplification rules
% 6.50/2.30  ----------------------
% 6.50/2.30  #Subsume      : 264
% 6.50/2.30  #Demod        : 1332
% 6.50/2.30  #Tautology    : 607
% 6.50/2.30  #SimpNegUnit  : 1
% 6.50/2.30  #BackRed      : 0
% 6.50/2.30  
% 6.50/2.30  #Partial instantiations: 0
% 6.50/2.30  #Strategies tried      : 1
% 6.50/2.30  
% 6.50/2.30  Timing (in seconds)
% 6.50/2.30  ----------------------
% 6.50/2.30  Preprocessing        : 0.34
% 6.50/2.30  Parsing              : 0.18
% 6.50/2.30  CNF conversion       : 0.02
% 6.50/2.30  Main loop            : 1.19
% 6.50/2.30  Inferencing          : 0.38
% 6.50/2.30  Reduction            : 0.40
% 6.50/2.30  Demodulation         : 0.29
% 6.50/2.30  BG Simplification    : 0.05
% 6.50/2.30  Subsumption          : 0.28
% 6.50/2.30  Abstraction          : 0.06
% 6.50/2.30  MUC search           : 0.00
% 6.50/2.30  Cooper               : 0.00
% 6.50/2.30  Total                : 1.57
% 6.50/2.30  Index Insertion      : 0.00
% 6.50/2.30  Index Deletion       : 0.00
% 6.50/2.30  Index Matching       : 0.00
% 6.50/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
