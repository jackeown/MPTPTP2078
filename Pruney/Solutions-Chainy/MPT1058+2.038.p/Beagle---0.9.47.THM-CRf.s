%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:27 EST 2020

% Result     : Theorem 6.31s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 248 expanded)
%              Number of leaves         :   42 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          :  143 ( 450 expanded)
%              Number of equality atoms :   29 ( 127 expanded)
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

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
          & r1_tarski(A,k2_relat_1(C)) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
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

tff(f_126,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_70,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_72,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54,plain,(
    ! [A_54] : v1_relat_1(k6_relat_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_41] : k1_relat_1(k6_relat_1(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,k10_relat_1(B_61,k9_relat_1(B_61,A_60)))
      | ~ r1_tarski(A_60,k1_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    ! [A_54] : v1_funct_1(k6_relat_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    ! [A_41] : k2_relat_1(k6_relat_1(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_118,plain,(
    ! [A_83] :
      ( k10_relat_1(A_83,k2_relat_1(A_83)) = k1_relat_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_127,plain,(
    ! [A_41] :
      ( k10_relat_1(k6_relat_1(A_41),A_41) = k1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_118])).

tff(c_131,plain,(
    ! [A_41] : k10_relat_1(k6_relat_1(A_41),A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32,c_127])).

tff(c_1623,plain,(
    ! [A_228,B_229,C_230] :
      ( r1_tarski(A_228,B_229)
      | ~ r1_tarski(A_228,k2_relat_1(C_230))
      | ~ r1_tarski(k10_relat_1(C_230,A_228),k10_relat_1(C_230,B_229))
      | ~ v1_funct_1(C_230)
      | ~ v1_relat_1(C_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1646,plain,(
    ! [A_41,B_229] :
      ( r1_tarski(A_41,B_229)
      | ~ r1_tarski(A_41,k2_relat_1(k6_relat_1(A_41)))
      | ~ r1_tarski(A_41,k10_relat_1(k6_relat_1(A_41),B_229))
      | ~ v1_funct_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_1623])).

tff(c_1670,plain,(
    ! [A_231,B_232] :
      ( r1_tarski(A_231,B_232)
      | ~ r1_tarski(A_231,k10_relat_1(k6_relat_1(A_231),B_232)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_12,c_34,c_1646])).

tff(c_1678,plain,(
    ! [A_60] :
      ( r1_tarski(A_60,k9_relat_1(k6_relat_1(A_60),A_60))
      | ~ r1_tarski(A_60,k1_relat_1(k6_relat_1(A_60)))
      | ~ v1_relat_1(k6_relat_1(A_60)) ) ),
    inference(resolution,[status(thm)],[c_62,c_1670])).

tff(c_1691,plain,(
    ! [A_60] : r1_tarski(A_60,k9_relat_1(k6_relat_1(A_60),A_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12,c_32,c_1678])).

tff(c_195,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(k9_relat_1(B_103,k10_relat_1(B_103,A_104)),A_104)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_206,plain,(
    ! [A_41] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_41),A_41),A_41)
      | ~ v1_funct_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_195])).

tff(c_215,plain,(
    ! [A_105] : r1_tarski(k9_relat_1(k6_relat_1(A_105),A_105),A_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_206])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_226,plain,(
    ! [A_105] :
      ( k9_relat_1(k6_relat_1(A_105),A_105) = A_105
      | ~ r1_tarski(A_105,k9_relat_1(k6_relat_1(A_105),A_105)) ) ),
    inference(resolution,[status(thm)],[c_215,c_8])).

tff(c_1697,plain,(
    ! [A_105] : k9_relat_1(k6_relat_1(A_105),A_105) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_226])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_326,plain,(
    ! [D_119,A_120,B_121] :
      ( r2_hidden(D_119,k1_relat_1(A_120))
      | ~ r2_hidden(D_119,k10_relat_1(A_120,B_121))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5296,plain,(
    ! [A_426,B_427,B_428] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_426,B_427),B_428),k1_relat_1(A_426))
      | ~ v1_funct_1(A_426)
      | ~ v1_relat_1(A_426)
      | r1_tarski(k10_relat_1(A_426,B_427),B_428) ) ),
    inference(resolution,[status(thm)],[c_6,c_326])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5328,plain,(
    ! [A_429,B_430] :
      ( ~ v1_funct_1(A_429)
      | ~ v1_relat_1(A_429)
      | r1_tarski(k10_relat_1(A_429,B_430),k1_relat_1(A_429)) ) ),
    inference(resolution,[status(thm)],[c_5296,c_4])).

tff(c_5354,plain,(
    ! [A_41,B_430] :
      ( ~ v1_funct_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_41))
      | r1_tarski(k10_relat_1(k6_relat_1(A_41),B_430),A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5328])).

tff(c_5363,plain,(
    ! [A_41,B_430] : r1_tarski(k10_relat_1(k6_relat_1(A_41),B_430),A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_5354])).

tff(c_1889,plain,(
    ! [A_240,C_241,B_242] :
      ( r1_tarski(A_240,k10_relat_1(C_241,B_242))
      | ~ r1_tarski(k9_relat_1(C_241,A_240),B_242)
      | ~ r1_tarski(A_240,k1_relat_1(C_241))
      | ~ v1_funct_1(C_241)
      | ~ v1_relat_1(C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1895,plain,(
    ! [A_105,B_242] :
      ( r1_tarski(A_105,k10_relat_1(k6_relat_1(A_105),B_242))
      | ~ r1_tarski(A_105,B_242)
      | ~ r1_tarski(A_105,k1_relat_1(k6_relat_1(A_105)))
      | ~ v1_funct_1(k6_relat_1(A_105))
      | ~ v1_relat_1(k6_relat_1(A_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_1889])).

tff(c_2260,plain,(
    ! [A_267,B_268] :
      ( r1_tarski(A_267,k10_relat_1(k6_relat_1(A_267),B_268))
      | ~ r1_tarski(A_267,B_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_12,c_32,c_1895])).

tff(c_2289,plain,(
    ! [A_267,B_268] :
      ( k10_relat_1(k6_relat_1(A_267),B_268) = A_267
      | ~ r1_tarski(k10_relat_1(k6_relat_1(A_267),B_268),A_267)
      | ~ r1_tarski(A_267,B_268) ) ),
    inference(resolution,[status(thm)],[c_2260,c_8])).

tff(c_5585,plain,(
    ! [A_437,B_438] :
      ( k10_relat_1(k6_relat_1(A_437),B_438) = A_437
      | ~ r1_tarski(A_437,B_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5363,c_2289])).

tff(c_542,plain,(
    ! [A_147,B_148] :
      ( k3_xboole_0(A_147,k9_relat_1(B_148,k1_relat_1(B_148))) = k9_relat_1(B_148,k10_relat_1(B_148,A_147))
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_551,plain,(
    ! [A_41,A_147] :
      ( k9_relat_1(k6_relat_1(A_41),k10_relat_1(k6_relat_1(A_41),A_147)) = k3_xboole_0(A_147,k9_relat_1(k6_relat_1(A_41),A_41))
      | ~ v1_funct_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_542])).

tff(c_555,plain,(
    ! [A_41,A_147] : k9_relat_1(k6_relat_1(A_41),k10_relat_1(k6_relat_1(A_41),A_147)) = k3_xboole_0(A_147,k9_relat_1(k6_relat_1(A_41),A_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_551])).

tff(c_1757,plain,(
    ! [A_41,A_147] : k9_relat_1(k6_relat_1(A_41),k10_relat_1(k6_relat_1(A_41),A_147)) = k3_xboole_0(A_147,A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_555])).

tff(c_5650,plain,(
    ! [A_437,B_438] :
      ( k9_relat_1(k6_relat_1(A_437),A_437) = k3_xboole_0(B_438,A_437)
      | ~ r1_tarski(A_437,B_438) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5585,c_1757])).

tff(c_5778,plain,(
    ! [B_439,A_440] :
      ( k3_xboole_0(B_439,A_440) = A_440
      | ~ r1_tarski(A_440,B_439) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_5650])).

tff(c_5961,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_5778])).

tff(c_58,plain,(
    ! [A_55,C_57,B_56] :
      ( k3_xboole_0(A_55,k10_relat_1(C_57,B_56)) = k10_relat_1(k7_relat_1(C_57,A_55),B_56)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6435,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5961,c_58])).

tff(c_6452,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6435])).

tff(c_6454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.31/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.26  
% 6.31/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.26  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.31/2.26  
% 6.31/2.26  %Foreground sorts:
% 6.31/2.26  
% 6.31/2.26  
% 6.31/2.26  %Background operators:
% 6.31/2.26  
% 6.31/2.26  
% 6.31/2.26  %Foreground operators:
% 6.31/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.31/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.31/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.31/2.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.31/2.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.31/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.31/2.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.31/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.31/2.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.31/2.26  tff('#skF_5', type, '#skF_5': $i).
% 6.31/2.26  tff('#skF_6', type, '#skF_6': $i).
% 6.31/2.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.31/2.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.31/2.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.31/2.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.31/2.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.31/2.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.31/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.31/2.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.31/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.31/2.26  tff('#skF_4', type, '#skF_4': $i).
% 6.31/2.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.31/2.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.31/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.31/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.31/2.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.31/2.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.31/2.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.31/2.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.31/2.26  
% 6.31/2.28  tff(f_136, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 6.31/2.28  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.31/2.28  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.31/2.28  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.31/2.28  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 6.31/2.28  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 6.31/2.28  tff(f_116, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 6.31/2.28  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 6.31/2.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.31/2.28  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 6.31/2.28  tff(f_126, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 6.31/2.28  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 6.31/2.28  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 6.31/2.28  tff(c_70, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.31/2.28  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.31/2.28  tff(c_72, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.31/2.28  tff(c_54, plain, (![A_54]: (v1_relat_1(k6_relat_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.31/2.28  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.31/2.28  tff(c_32, plain, (![A_41]: (k1_relat_1(k6_relat_1(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.31/2.28  tff(c_62, plain, (![A_60, B_61]: (r1_tarski(A_60, k10_relat_1(B_61, k9_relat_1(B_61, A_60))) | ~r1_tarski(A_60, k1_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.31/2.28  tff(c_56, plain, (![A_54]: (v1_funct_1(k6_relat_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.31/2.28  tff(c_34, plain, (![A_41]: (k2_relat_1(k6_relat_1(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.31/2.28  tff(c_118, plain, (![A_83]: (k10_relat_1(A_83, k2_relat_1(A_83))=k1_relat_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.31/2.28  tff(c_127, plain, (![A_41]: (k10_relat_1(k6_relat_1(A_41), A_41)=k1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_118])).
% 6.31/2.28  tff(c_131, plain, (![A_41]: (k10_relat_1(k6_relat_1(A_41), A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32, c_127])).
% 6.31/2.28  tff(c_1623, plain, (![A_228, B_229, C_230]: (r1_tarski(A_228, B_229) | ~r1_tarski(A_228, k2_relat_1(C_230)) | ~r1_tarski(k10_relat_1(C_230, A_228), k10_relat_1(C_230, B_229)) | ~v1_funct_1(C_230) | ~v1_relat_1(C_230))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.31/2.28  tff(c_1646, plain, (![A_41, B_229]: (r1_tarski(A_41, B_229) | ~r1_tarski(A_41, k2_relat_1(k6_relat_1(A_41))) | ~r1_tarski(A_41, k10_relat_1(k6_relat_1(A_41), B_229)) | ~v1_funct_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_1623])).
% 6.31/2.28  tff(c_1670, plain, (![A_231, B_232]: (r1_tarski(A_231, B_232) | ~r1_tarski(A_231, k10_relat_1(k6_relat_1(A_231), B_232)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_12, c_34, c_1646])).
% 6.31/2.28  tff(c_1678, plain, (![A_60]: (r1_tarski(A_60, k9_relat_1(k6_relat_1(A_60), A_60)) | ~r1_tarski(A_60, k1_relat_1(k6_relat_1(A_60))) | ~v1_relat_1(k6_relat_1(A_60)))), inference(resolution, [status(thm)], [c_62, c_1670])).
% 6.31/2.28  tff(c_1691, plain, (![A_60]: (r1_tarski(A_60, k9_relat_1(k6_relat_1(A_60), A_60)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_12, c_32, c_1678])).
% 6.31/2.28  tff(c_195, plain, (![B_103, A_104]: (r1_tarski(k9_relat_1(B_103, k10_relat_1(B_103, A_104)), A_104) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.31/2.28  tff(c_206, plain, (![A_41]: (r1_tarski(k9_relat_1(k6_relat_1(A_41), A_41), A_41) | ~v1_funct_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_195])).
% 6.31/2.28  tff(c_215, plain, (![A_105]: (r1_tarski(k9_relat_1(k6_relat_1(A_105), A_105), A_105))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_206])).
% 6.31/2.28  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.31/2.28  tff(c_226, plain, (![A_105]: (k9_relat_1(k6_relat_1(A_105), A_105)=A_105 | ~r1_tarski(A_105, k9_relat_1(k6_relat_1(A_105), A_105)))), inference(resolution, [status(thm)], [c_215, c_8])).
% 6.31/2.28  tff(c_1697, plain, (![A_105]: (k9_relat_1(k6_relat_1(A_105), A_105)=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_1691, c_226])).
% 6.31/2.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.31/2.28  tff(c_326, plain, (![D_119, A_120, B_121]: (r2_hidden(D_119, k1_relat_1(A_120)) | ~r2_hidden(D_119, k10_relat_1(A_120, B_121)) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.31/2.28  tff(c_5296, plain, (![A_426, B_427, B_428]: (r2_hidden('#skF_1'(k10_relat_1(A_426, B_427), B_428), k1_relat_1(A_426)) | ~v1_funct_1(A_426) | ~v1_relat_1(A_426) | r1_tarski(k10_relat_1(A_426, B_427), B_428))), inference(resolution, [status(thm)], [c_6, c_326])).
% 6.31/2.28  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.31/2.28  tff(c_5328, plain, (![A_429, B_430]: (~v1_funct_1(A_429) | ~v1_relat_1(A_429) | r1_tarski(k10_relat_1(A_429, B_430), k1_relat_1(A_429)))), inference(resolution, [status(thm)], [c_5296, c_4])).
% 6.31/2.28  tff(c_5354, plain, (![A_41, B_430]: (~v1_funct_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_41)) | r1_tarski(k10_relat_1(k6_relat_1(A_41), B_430), A_41))), inference(superposition, [status(thm), theory('equality')], [c_32, c_5328])).
% 6.31/2.28  tff(c_5363, plain, (![A_41, B_430]: (r1_tarski(k10_relat_1(k6_relat_1(A_41), B_430), A_41))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_5354])).
% 6.31/2.28  tff(c_1889, plain, (![A_240, C_241, B_242]: (r1_tarski(A_240, k10_relat_1(C_241, B_242)) | ~r1_tarski(k9_relat_1(C_241, A_240), B_242) | ~r1_tarski(A_240, k1_relat_1(C_241)) | ~v1_funct_1(C_241) | ~v1_relat_1(C_241))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.31/2.28  tff(c_1895, plain, (![A_105, B_242]: (r1_tarski(A_105, k10_relat_1(k6_relat_1(A_105), B_242)) | ~r1_tarski(A_105, B_242) | ~r1_tarski(A_105, k1_relat_1(k6_relat_1(A_105))) | ~v1_funct_1(k6_relat_1(A_105)) | ~v1_relat_1(k6_relat_1(A_105)))), inference(superposition, [status(thm), theory('equality')], [c_1697, c_1889])).
% 6.31/2.28  tff(c_2260, plain, (![A_267, B_268]: (r1_tarski(A_267, k10_relat_1(k6_relat_1(A_267), B_268)) | ~r1_tarski(A_267, B_268))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_12, c_32, c_1895])).
% 6.31/2.28  tff(c_2289, plain, (![A_267, B_268]: (k10_relat_1(k6_relat_1(A_267), B_268)=A_267 | ~r1_tarski(k10_relat_1(k6_relat_1(A_267), B_268), A_267) | ~r1_tarski(A_267, B_268))), inference(resolution, [status(thm)], [c_2260, c_8])).
% 6.31/2.28  tff(c_5585, plain, (![A_437, B_438]: (k10_relat_1(k6_relat_1(A_437), B_438)=A_437 | ~r1_tarski(A_437, B_438))), inference(demodulation, [status(thm), theory('equality')], [c_5363, c_2289])).
% 6.31/2.28  tff(c_542, plain, (![A_147, B_148]: (k3_xboole_0(A_147, k9_relat_1(B_148, k1_relat_1(B_148)))=k9_relat_1(B_148, k10_relat_1(B_148, A_147)) | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.31/2.28  tff(c_551, plain, (![A_41, A_147]: (k9_relat_1(k6_relat_1(A_41), k10_relat_1(k6_relat_1(A_41), A_147))=k3_xboole_0(A_147, k9_relat_1(k6_relat_1(A_41), A_41)) | ~v1_funct_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_542])).
% 6.31/2.28  tff(c_555, plain, (![A_41, A_147]: (k9_relat_1(k6_relat_1(A_41), k10_relat_1(k6_relat_1(A_41), A_147))=k3_xboole_0(A_147, k9_relat_1(k6_relat_1(A_41), A_41)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_551])).
% 6.31/2.28  tff(c_1757, plain, (![A_41, A_147]: (k9_relat_1(k6_relat_1(A_41), k10_relat_1(k6_relat_1(A_41), A_147))=k3_xboole_0(A_147, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_1697, c_555])).
% 6.31/2.28  tff(c_5650, plain, (![A_437, B_438]: (k9_relat_1(k6_relat_1(A_437), A_437)=k3_xboole_0(B_438, A_437) | ~r1_tarski(A_437, B_438))), inference(superposition, [status(thm), theory('equality')], [c_5585, c_1757])).
% 6.31/2.28  tff(c_5778, plain, (![B_439, A_440]: (k3_xboole_0(B_439, A_440)=A_440 | ~r1_tarski(A_440, B_439))), inference(demodulation, [status(thm), theory('equality')], [c_1697, c_5650])).
% 6.31/2.28  tff(c_5961, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_72, c_5778])).
% 6.31/2.28  tff(c_58, plain, (![A_55, C_57, B_56]: (k3_xboole_0(A_55, k10_relat_1(C_57, B_56))=k10_relat_1(k7_relat_1(C_57, A_55), B_56) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.31/2.28  tff(c_6435, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5961, c_58])).
% 6.31/2.28  tff(c_6452, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6435])).
% 6.31/2.28  tff(c_6454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_6452])).
% 6.31/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.28  
% 6.31/2.28  Inference rules
% 6.31/2.28  ----------------------
% 6.31/2.28  #Ref     : 0
% 6.31/2.28  #Sup     : 1445
% 6.31/2.28  #Fact    : 0
% 6.31/2.28  #Define  : 0
% 6.31/2.28  #Split   : 1
% 6.31/2.28  #Chain   : 0
% 6.31/2.28  #Close   : 0
% 6.31/2.28  
% 6.31/2.28  Ordering : KBO
% 6.31/2.28  
% 6.31/2.28  Simplification rules
% 6.31/2.28  ----------------------
% 6.31/2.28  #Subsume      : 183
% 6.31/2.28  #Demod        : 699
% 6.31/2.28  #Tautology    : 303
% 6.31/2.28  #SimpNegUnit  : 1
% 6.31/2.28  #BackRed      : 30
% 6.31/2.28  
% 6.31/2.28  #Partial instantiations: 0
% 6.31/2.28  #Strategies tried      : 1
% 6.31/2.28  
% 6.31/2.28  Timing (in seconds)
% 6.31/2.28  ----------------------
% 6.63/2.28  Preprocessing        : 0.35
% 6.63/2.28  Parsing              : 0.18
% 6.63/2.28  CNF conversion       : 0.03
% 6.63/2.28  Main loop            : 1.15
% 6.63/2.28  Inferencing          : 0.37
% 6.63/2.28  Reduction            : 0.37
% 6.63/2.28  Demodulation         : 0.28
% 6.63/2.28  BG Simplification    : 0.05
% 6.63/2.28  Subsumption          : 0.27
% 6.63/2.28  Abstraction          : 0.06
% 6.63/2.28  MUC search           : 0.00
% 6.63/2.28  Cooper               : 0.00
% 6.63/2.28  Total                : 1.54
% 6.63/2.28  Index Insertion      : 0.00
% 6.63/2.28  Index Deletion       : 0.00
% 6.63/2.28  Index Matching       : 0.00
% 6.63/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
