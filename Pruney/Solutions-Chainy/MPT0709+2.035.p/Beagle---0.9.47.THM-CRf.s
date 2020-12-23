%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:29 EST 2020

% Result     : Theorem 8.70s
% Output     : CNFRefutation 8.70s
% Verified   : 
% Statistics : Number of formulae       :  133 (4558 expanded)
%              Number of leaves         :   24 (1656 expanded)
%              Depth                    :   45
%              Number of atoms          :  355 (14455 expanded)
%              Number of equality atoms :   32 (1675 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_22,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_4] :
      ( k9_relat_1(A_4,k1_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(k2_funct_1(B_15),A_14) = k9_relat_1(B_15,A_14)
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [C_10,A_8,B_9] :
      ( r1_tarski(k10_relat_1(C_10,A_8),k10_relat_1(C_10,B_9))
      | ~ r1_tarski(A_8,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [C_34,A_35,B_36] :
      ( r1_tarski(k10_relat_1(C_34,A_35),k10_relat_1(C_34,B_36))
      | ~ r1_tarski(A_35,B_36)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [A_50,C_51,B_52,A_53] :
      ( r1_tarski(A_50,k10_relat_1(C_51,B_52))
      | ~ r1_tarski(A_50,k10_relat_1(C_51,A_53))
      | ~ r1_tarski(A_53,B_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_203,plain,(
    ! [C_57,A_58,B_59,B_60] :
      ( r1_tarski(k10_relat_1(C_57,A_58),k10_relat_1(C_57,B_59))
      | ~ r1_tarski(B_60,B_59)
      | ~ r1_tarski(A_58,B_60)
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_10,c_187])).

tff(c_241,plain,(
    ! [C_63,A_64] :
      ( r1_tarski(k10_relat_1(C_63,A_64),k10_relat_1(C_63,k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_64,'#skF_1')
      | ~ v1_relat_1(C_63) ) ),
    inference(resolution,[status(thm)],[c_26,c_203])).

tff(c_2119,plain,(
    ! [B_197,A_198] :
      ( r1_tarski(k10_relat_1(k2_funct_1(B_197),A_198),k9_relat_1(B_197,k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_198,'#skF_1')
      | ~ v1_relat_1(k2_funct_1(B_197))
      | ~ v2_funct_1(B_197)
      | ~ v1_funct_1(B_197)
      | ~ v1_relat_1(B_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_241])).

tff(c_2158,plain,(
    ! [A_198] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),A_198),k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_198,'#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2119])).

tff(c_2170,plain,(
    ! [A_198] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),A_198),k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_198,'#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_28,c_24,c_2158])).

tff(c_2171,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2170])).

tff(c_2174,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_2171])).

tff(c_2178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2174])).

tff(c_2180,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2170])).

tff(c_12,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [B_39,A_40] :
      ( k10_relat_1(k2_funct_1(B_39),A_40) = k9_relat_1(B_39,A_40)
      | ~ v2_funct_1(B_39)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k10_relat_1(B_6,A_5),k1_relat_1(B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_225,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k9_relat_1(B_61,A_62),k1_relat_1(k2_funct_1(B_61)))
      | ~ v1_relat_1(k2_funct_1(B_61))
      | ~ v2_funct_1(B_61)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_6])).

tff(c_237,plain,(
    ! [A_4] :
      ( r1_tarski(k2_relat_1(A_4),k1_relat_1(k2_funct_1(A_4)))
      | ~ v1_relat_1(k2_funct_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_225])).

tff(c_147,plain,(
    ! [B_41,A_42] :
      ( k9_relat_1(k2_funct_1(B_41),A_42) = k10_relat_1(B_41,A_42)
      | ~ v2_funct_1(B_41)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_566,plain,(
    ! [B_92] :
      ( k10_relat_1(B_92,k1_relat_1(k2_funct_1(B_92))) = k2_relat_1(k2_funct_1(B_92))
      | ~ v2_funct_1(B_92)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(k2_funct_1(B_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_147])).

tff(c_616,plain,(
    ! [B_92] :
      ( r1_tarski(k2_relat_1(k2_funct_1(B_92)),k1_relat_1(B_92))
      | ~ v1_relat_1(B_92)
      | ~ v2_funct_1(B_92)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(k2_funct_1(B_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_6])).

tff(c_98,plain,(
    ! [A_7,B_36] :
      ( r1_tarski(k1_relat_1(A_7),k10_relat_1(A_7,B_36))
      | ~ r1_tarski(k2_relat_1(A_7),B_36)
      | ~ v1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_607,plain,(
    ! [B_92,B_9] :
      ( r1_tarski(k2_relat_1(k2_funct_1(B_92)),k10_relat_1(B_92,B_9))
      | ~ r1_tarski(k1_relat_1(k2_funct_1(B_92)),B_9)
      | ~ v1_relat_1(B_92)
      | ~ v2_funct_1(B_92)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(k2_funct_1(B_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_10])).

tff(c_2181,plain,(
    ! [A_199] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),A_199),k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_199,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_2170])).

tff(c_2408,plain,(
    ! [A_207,A_208] :
      ( r1_tarski(A_207,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_207,k10_relat_1(k2_funct_1('#skF_2'),A_208))
      | ~ r1_tarski(A_208,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2181,c_2])).

tff(c_2480,plain,(
    ! [B_36] :
      ( r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),k2_relat_1('#skF_2'))
      | ~ r1_tarski(B_36,'#skF_1')
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),B_36)
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_98,c_2408])).

tff(c_2545,plain,(
    ! [B_36] :
      ( r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),k2_relat_1('#skF_2'))
      | ~ r1_tarski(B_36,'#skF_1')
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_2480])).

tff(c_2859,plain,(
    ! [B_225] :
      ( ~ r1_tarski(B_225,'#skF_1')
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),B_225) ) ),
    inference(splitLeft,[status(thm)],[c_2545])).

tff(c_2863,plain,(
    ! [B_9] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',B_9),'#skF_1')
      | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),B_9)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_607,c_2859])).

tff(c_2915,plain,(
    ! [B_226] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',B_226),'#skF_1')
      | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_30,c_28,c_24,c_2863])).

tff(c_2943,plain,(
    ! [B_36] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),B_36)),'#skF_1')
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),B_36)
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_98,c_2915])).

tff(c_2977,plain,(
    ! [B_227] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),B_227)),'#skF_1')
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),B_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_2943])).

tff(c_2985,plain,(
    ! [A_14] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_14)),'#skF_1')
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),A_14)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2977])).

tff(c_2996,plain,(
    ! [A_228] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_228)),'#skF_1')
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_2985])).

tff(c_3007,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_2',k2_relat_1('#skF_2')),'#skF_1')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2996])).

tff(c_3011,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_2',k2_relat_1('#skF_2')),'#skF_1')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3007])).

tff(c_3012,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3011])).

tff(c_3100,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_616,c_3012])).

tff(c_3110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_30,c_28,c_24,c_3100])).

tff(c_3112,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3011])).

tff(c_170,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_relat_1(A_48),k10_relat_1(A_48,B_49))
      | ~ r1_tarski(k2_relat_1(A_48),B_49)
      | ~ v1_relat_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_186,plain,(
    ! [A_1,A_48,B_49] :
      ( r1_tarski(A_1,k10_relat_1(A_48,B_49))
      | ~ r1_tarski(A_1,k1_relat_1(A_48))
      | ~ r1_tarski(k2_relat_1(A_48),B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_3139,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_1,k1_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3112,c_186])).

tff(c_3260,plain,(
    ! [A_237] :
      ( r1_tarski(A_237,k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_237,k1_relat_1(k2_funct_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_3139])).

tff(c_3329,plain,(
    ! [A_237] :
      ( r1_tarski(A_237,k9_relat_1('#skF_2',k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_237,k1_relat_1(k2_funct_1('#skF_2')))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3260])).

tff(c_3372,plain,(
    ! [A_238] :
      ( r1_tarski(A_238,k9_relat_1('#skF_2',k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_238,k1_relat_1(k2_funct_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_3329])).

tff(c_3431,plain,(
    ! [A_238] :
      ( r1_tarski(A_238,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_238,k1_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3372])).

tff(c_3460,plain,(
    ! [A_239] :
      ( r1_tarski(A_239,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_239,k1_relat_1(k2_funct_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3431])).

tff(c_3475,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_237,c_3460])).

tff(c_3497,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_2180,c_3475])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k9_relat_1(B_13,k10_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k2_relat_1(B_13))
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3532,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) = k2_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3497,c_16])).

tff(c_3559,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_3532])).

tff(c_3873,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3559])).

tff(c_3891,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3873])).

tff(c_137,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k9_relat_1(B_39,A_40),k1_relat_1(k2_funct_1(B_39)))
      | ~ v1_relat_1(k2_funct_1(B_39))
      | ~ v2_funct_1(B_39)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_6])).

tff(c_3479,plain,(
    ! [A_40] :
      ( r1_tarski(k9_relat_1('#skF_2',A_40),k2_relat_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_137,c_3460])).

tff(c_3618,plain,(
    ! [A_242] : r1_tarski(k9_relat_1('#skF_2',A_242),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_2180,c_3479])).

tff(c_3636,plain,(
    ! [A_242] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_242))) = k9_relat_1('#skF_2',A_242)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3618,c_16])).

tff(c_3661,plain,(
    ! [A_242] : k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_242))) = k9_relat_1('#skF_2',A_242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_3636])).

tff(c_3487,plain,(
    ! [A_5] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),A_5),k2_relat_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3460])).

tff(c_3783,plain,(
    ! [A_247] : r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),A_247),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_3487])).

tff(c_3801,plain,(
    ! [A_247] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),A_247))) = k10_relat_1(k2_funct_1('#skF_2'),A_247)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3783,c_16])).

tff(c_6607,plain,(
    ! [A_287] : k9_relat_1('#skF_2',k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),A_287))) = k10_relat_1(k2_funct_1('#skF_2'),A_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_3801])).

tff(c_6664,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_14))) = k10_relat_1(k2_funct_1('#skF_2'),A_14)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6607])).

tff(c_6695,plain,(
    ! [A_14] : k10_relat_1(k2_funct_1('#skF_2'),A_14) = k9_relat_1('#skF_2',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_3661,c_6664])).

tff(c_240,plain,(
    ! [A_1,B_61,A_62] :
      ( r1_tarski(A_1,k1_relat_1(k2_funct_1(B_61)))
      | ~ r1_tarski(A_1,k9_relat_1(B_61,A_62))
      | ~ v1_relat_1(k2_funct_1(B_61))
      | ~ v2_funct_1(B_61)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_225,c_2])).

tff(c_3860,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k1_relat_1(k2_funct_1('#skF_2')))
      | ~ r1_tarski(A_1,k2_relat_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3559,c_240])).

tff(c_3882,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k1_relat_1(k2_funct_1('#skF_2')))
      | ~ r1_tarski(A_1,k2_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_2180,c_3860])).

tff(c_7332,plain,(
    ! [B_289] :
      ( r1_tarski(k1_relat_1(B_289),k2_relat_1(k2_funct_1(B_289)))
      | ~ r1_tarski(k2_relat_1(B_289),k1_relat_1(k2_funct_1(B_289)))
      | ~ v1_relat_1(B_289)
      | ~ v1_relat_1(B_289)
      | ~ v2_funct_1(B_289)
      | ~ v1_funct_1(B_289)
      | ~ v1_relat_1(B_289)
      | ~ v1_relat_1(k2_funct_1(B_289)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_98])).

tff(c_7336,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3882,c_7332])).

tff(c_7349,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3497,c_2180,c_30,c_28,c_24,c_7336])).

tff(c_7383,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1('#skF_2'))) = k1_relat_1('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7349,c_16])).

tff(c_7409,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k2_relat_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_3891,c_6695,c_7383])).

tff(c_7523,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7409])).

tff(c_7526,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_7523])).

tff(c_7530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_7526])).

tff(c_7532,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7409])).

tff(c_3869,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3559,c_137])).

tff(c_3888,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_2180,c_3869])).

tff(c_3562,plain,(
    ! [B_240,A_241] :
      ( r1_tarski(k10_relat_1(B_240,A_241),k2_relat_1(k2_funct_1(B_240)))
      | ~ r1_tarski(A_241,k1_relat_1(k2_funct_1(B_240)))
      | ~ v1_relat_1(B_240)
      | ~ v2_funct_1(B_240)
      | ~ v1_funct_1(B_240)
      | ~ v1_relat_1(B_240)
      | ~ v1_relat_1(k2_funct_1(B_240)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_10])).

tff(c_3167,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_1,k2_relat_1(k2_funct_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_3112,c_2])).

tff(c_3566,plain,(
    ! [A_241] :
      ( r1_tarski(k10_relat_1('#skF_2',A_241),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_241,k1_relat_1(k2_funct_1('#skF_2')))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3562,c_3167])).

tff(c_4964,plain,(
    ! [A_267] :
      ( r1_tarski(k10_relat_1('#skF_2',A_267),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_267,k1_relat_1(k2_funct_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_30,c_28,c_24,c_3566])).

tff(c_4992,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4964])).

tff(c_5006,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3888,c_4992])).

tff(c_161,plain,(
    ! [B_41] :
      ( k10_relat_1(B_41,k1_relat_1(k2_funct_1(B_41))) = k2_relat_1(k2_funct_1(B_41))
      | ~ v2_funct_1(B_41)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(k2_funct_1(B_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_147])).

tff(c_3918,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k10_relat_1('#skF_2',k1_relat_1(k2_funct_1('#skF_2'))))
      | ~ r1_tarski(A_1,k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3888,c_186])).

tff(c_6098,plain,(
    ! [A_278] :
      ( r1_tarski(A_278,k10_relat_1('#skF_2',k1_relat_1(k2_funct_1('#skF_2'))))
      | ~ r1_tarski(A_278,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3918])).

tff(c_6171,plain,(
    ! [A_278] :
      ( r1_tarski(A_278,k2_relat_1(k2_funct_1('#skF_2')))
      | ~ r1_tarski(A_278,k1_relat_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_6098])).

tff(c_6226,plain,(
    ! [A_279] :
      ( r1_tarski(A_279,k2_relat_1(k2_funct_1('#skF_2')))
      | ~ r1_tarski(A_279,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_30,c_28,c_24,c_6171])).

tff(c_8952,plain,(
    ! [A_307,A_308] :
      ( r1_tarski(A_307,k2_relat_1(k2_funct_1('#skF_2')))
      | ~ r1_tarski(A_307,A_308)
      | ~ r1_tarski(A_308,k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6226,c_2])).

tff(c_9076,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_2')))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_8952])).

tff(c_9162,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5006,c_9076])).

tff(c_9192,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_9162,c_16])).

tff(c_9219,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_7532,c_6695,c_9192])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k9_relat_1(k2_funct_1(B_17),A_16) = k10_relat_1(B_17,A_16)
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9446,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9219,c_20])).

tff(c_9471,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_9446])).

tff(c_9473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_9471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.70/2.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.70/2.99  
% 8.70/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.70/3.00  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.70/3.00  
% 8.70/3.00  %Foreground sorts:
% 8.70/3.00  
% 8.70/3.00  
% 8.70/3.00  %Background operators:
% 8.70/3.00  
% 8.70/3.00  
% 8.70/3.00  %Foreground operators:
% 8.70/3.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.70/3.00  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.70/3.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.70/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.70/3.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.70/3.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.70/3.00  tff('#skF_2', type, '#skF_2': $i).
% 8.70/3.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.70/3.00  tff('#skF_1', type, '#skF_1': $i).
% 8.70/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.70/3.00  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.70/3.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.70/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.70/3.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.70/3.00  
% 8.70/3.02  tff(f_92, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 8.70/3.02  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.70/3.02  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.70/3.02  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 8.70/3.02  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 8.70/3.02  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.70/3.02  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 8.70/3.02  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 8.70/3.02  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 8.70/3.02  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 8.70/3.02  tff(c_22, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.70/3.02  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.70/3.02  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.70/3.02  tff(c_24, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.70/3.02  tff(c_14, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.70/3.02  tff(c_4, plain, (![A_4]: (k9_relat_1(A_4, k1_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.70/3.02  tff(c_18, plain, (![B_15, A_14]: (k10_relat_1(k2_funct_1(B_15), A_14)=k9_relat_1(B_15, A_14) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.70/3.02  tff(c_26, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.70/3.02  tff(c_10, plain, (![C_10, A_8, B_9]: (r1_tarski(k10_relat_1(C_10, A_8), k10_relat_1(C_10, B_9)) | ~r1_tarski(A_8, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.70/3.02  tff(c_88, plain, (![C_34, A_35, B_36]: (r1_tarski(k10_relat_1(C_34, A_35), k10_relat_1(C_34, B_36)) | ~r1_tarski(A_35, B_36) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.70/3.02  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.70/3.02  tff(c_187, plain, (![A_50, C_51, B_52, A_53]: (r1_tarski(A_50, k10_relat_1(C_51, B_52)) | ~r1_tarski(A_50, k10_relat_1(C_51, A_53)) | ~r1_tarski(A_53, B_52) | ~v1_relat_1(C_51))), inference(resolution, [status(thm)], [c_88, c_2])).
% 8.70/3.02  tff(c_203, plain, (![C_57, A_58, B_59, B_60]: (r1_tarski(k10_relat_1(C_57, A_58), k10_relat_1(C_57, B_59)) | ~r1_tarski(B_60, B_59) | ~r1_tarski(A_58, B_60) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_10, c_187])).
% 8.70/3.02  tff(c_241, plain, (![C_63, A_64]: (r1_tarski(k10_relat_1(C_63, A_64), k10_relat_1(C_63, k1_relat_1('#skF_2'))) | ~r1_tarski(A_64, '#skF_1') | ~v1_relat_1(C_63))), inference(resolution, [status(thm)], [c_26, c_203])).
% 8.70/3.02  tff(c_2119, plain, (![B_197, A_198]: (r1_tarski(k10_relat_1(k2_funct_1(B_197), A_198), k9_relat_1(B_197, k1_relat_1('#skF_2'))) | ~r1_tarski(A_198, '#skF_1') | ~v1_relat_1(k2_funct_1(B_197)) | ~v2_funct_1(B_197) | ~v1_funct_1(B_197) | ~v1_relat_1(B_197))), inference(superposition, [status(thm), theory('equality')], [c_18, c_241])).
% 8.70/3.02  tff(c_2158, plain, (![A_198]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), A_198), k2_relat_1('#skF_2')) | ~r1_tarski(A_198, '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2119])).
% 8.70/3.02  tff(c_2170, plain, (![A_198]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), A_198), k2_relat_1('#skF_2')) | ~r1_tarski(A_198, '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_28, c_24, c_2158])).
% 8.70/3.02  tff(c_2171, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2170])).
% 8.70/3.02  tff(c_2174, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_2171])).
% 8.70/3.02  tff(c_2178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2174])).
% 8.70/3.02  tff(c_2180, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2170])).
% 8.70/3.02  tff(c_12, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.70/3.02  tff(c_8, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.70/3.02  tff(c_115, plain, (![B_39, A_40]: (k10_relat_1(k2_funct_1(B_39), A_40)=k9_relat_1(B_39, A_40) | ~v2_funct_1(B_39) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.70/3.02  tff(c_6, plain, (![B_6, A_5]: (r1_tarski(k10_relat_1(B_6, A_5), k1_relat_1(B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.70/3.02  tff(c_225, plain, (![B_61, A_62]: (r1_tarski(k9_relat_1(B_61, A_62), k1_relat_1(k2_funct_1(B_61))) | ~v1_relat_1(k2_funct_1(B_61)) | ~v2_funct_1(B_61) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(superposition, [status(thm), theory('equality')], [c_115, c_6])).
% 8.70/3.02  tff(c_237, plain, (![A_4]: (r1_tarski(k2_relat_1(A_4), k1_relat_1(k2_funct_1(A_4))) | ~v1_relat_1(k2_funct_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_225])).
% 8.70/3.02  tff(c_147, plain, (![B_41, A_42]: (k9_relat_1(k2_funct_1(B_41), A_42)=k10_relat_1(B_41, A_42) | ~v2_funct_1(B_41) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.70/3.02  tff(c_566, plain, (![B_92]: (k10_relat_1(B_92, k1_relat_1(k2_funct_1(B_92)))=k2_relat_1(k2_funct_1(B_92)) | ~v2_funct_1(B_92) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_relat_1(k2_funct_1(B_92)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_147])).
% 8.70/3.02  tff(c_616, plain, (![B_92]: (r1_tarski(k2_relat_1(k2_funct_1(B_92)), k1_relat_1(B_92)) | ~v1_relat_1(B_92) | ~v2_funct_1(B_92) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_relat_1(k2_funct_1(B_92)))), inference(superposition, [status(thm), theory('equality')], [c_566, c_6])).
% 8.70/3.02  tff(c_98, plain, (![A_7, B_36]: (r1_tarski(k1_relat_1(A_7), k10_relat_1(A_7, B_36)) | ~r1_tarski(k2_relat_1(A_7), B_36) | ~v1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_88])).
% 8.70/3.02  tff(c_607, plain, (![B_92, B_9]: (r1_tarski(k2_relat_1(k2_funct_1(B_92)), k10_relat_1(B_92, B_9)) | ~r1_tarski(k1_relat_1(k2_funct_1(B_92)), B_9) | ~v1_relat_1(B_92) | ~v2_funct_1(B_92) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_relat_1(k2_funct_1(B_92)))), inference(superposition, [status(thm), theory('equality')], [c_566, c_10])).
% 8.70/3.02  tff(c_2181, plain, (![A_199]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), A_199), k2_relat_1('#skF_2')) | ~r1_tarski(A_199, '#skF_1'))), inference(splitRight, [status(thm)], [c_2170])).
% 8.70/3.02  tff(c_2408, plain, (![A_207, A_208]: (r1_tarski(A_207, k2_relat_1('#skF_2')) | ~r1_tarski(A_207, k10_relat_1(k2_funct_1('#skF_2'), A_208)) | ~r1_tarski(A_208, '#skF_1'))), inference(resolution, [status(thm)], [c_2181, c_2])).
% 8.70/3.02  tff(c_2480, plain, (![B_36]: (r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(B_36, '#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), B_36) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_98, c_2408])).
% 8.70/3.02  tff(c_2545, plain, (![B_36]: (r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(B_36, '#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), B_36))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_2480])).
% 8.70/3.02  tff(c_2859, plain, (![B_225]: (~r1_tarski(B_225, '#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), B_225))), inference(splitLeft, [status(thm)], [c_2545])).
% 8.70/3.02  tff(c_2863, plain, (![B_9]: (~r1_tarski(k10_relat_1('#skF_2', B_9), '#skF_1') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), B_9) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_607, c_2859])).
% 8.70/3.02  tff(c_2915, plain, (![B_226]: (~r1_tarski(k10_relat_1('#skF_2', B_226), '#skF_1') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), B_226))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_30, c_28, c_24, c_2863])).
% 8.70/3.02  tff(c_2943, plain, (![B_36]: (~r1_tarski(k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), B_36)), '#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), B_36) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_98, c_2915])).
% 8.70/3.02  tff(c_2977, plain, (![B_227]: (~r1_tarski(k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), B_227)), '#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), B_227))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_2943])).
% 8.70/3.02  tff(c_2985, plain, (![A_14]: (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_14)), '#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), A_14) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2977])).
% 8.70/3.02  tff(c_2996, plain, (![A_228]: (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_228)), '#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), A_228))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_2985])).
% 8.70/3.02  tff(c_3007, plain, (~r1_tarski(k10_relat_1('#skF_2', k2_relat_1('#skF_2')), '#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_2996])).
% 8.70/3.02  tff(c_3011, plain, (~r1_tarski(k10_relat_1('#skF_2', k2_relat_1('#skF_2')), '#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3007])).
% 8.70/3.02  tff(c_3012, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3011])).
% 8.70/3.02  tff(c_3100, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_616, c_3012])).
% 8.70/3.02  tff(c_3110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2180, c_30, c_28, c_24, c_3100])).
% 8.70/3.02  tff(c_3112, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_3011])).
% 8.70/3.02  tff(c_170, plain, (![A_48, B_49]: (r1_tarski(k1_relat_1(A_48), k10_relat_1(A_48, B_49)) | ~r1_tarski(k2_relat_1(A_48), B_49) | ~v1_relat_1(A_48) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_8, c_88])).
% 8.70/3.02  tff(c_186, plain, (![A_1, A_48, B_49]: (r1_tarski(A_1, k10_relat_1(A_48, B_49)) | ~r1_tarski(A_1, k1_relat_1(A_48)) | ~r1_tarski(k2_relat_1(A_48), B_49) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_170, c_2])).
% 8.70/3.02  tff(c_3139, plain, (![A_1]: (r1_tarski(A_1, k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1('#skF_2'))) | ~r1_tarski(A_1, k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_3112, c_186])).
% 8.70/3.02  tff(c_3260, plain, (![A_237]: (r1_tarski(A_237, k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1('#skF_2'))) | ~r1_tarski(A_237, k1_relat_1(k2_funct_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_3139])).
% 8.70/3.02  tff(c_3329, plain, (![A_237]: (r1_tarski(A_237, k9_relat_1('#skF_2', k1_relat_1('#skF_2'))) | ~r1_tarski(A_237, k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3260])).
% 8.70/3.02  tff(c_3372, plain, (![A_238]: (r1_tarski(A_238, k9_relat_1('#skF_2', k1_relat_1('#skF_2'))) | ~r1_tarski(A_238, k1_relat_1(k2_funct_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_3329])).
% 8.70/3.02  tff(c_3431, plain, (![A_238]: (r1_tarski(A_238, k2_relat_1('#skF_2')) | ~r1_tarski(A_238, k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3372])).
% 8.70/3.02  tff(c_3460, plain, (![A_239]: (r1_tarski(A_239, k2_relat_1('#skF_2')) | ~r1_tarski(A_239, k1_relat_1(k2_funct_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3431])).
% 8.70/3.02  tff(c_3475, plain, (r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_237, c_3460])).
% 8.70/3.02  tff(c_3497, plain, (r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_2180, c_3475])).
% 8.70/3.02  tff(c_16, plain, (![B_13, A_12]: (k9_relat_1(B_13, k10_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k2_relat_1(B_13)) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.70/3.02  tff(c_3532, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))=k2_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3497, c_16])).
% 8.70/3.02  tff(c_3559, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_3532])).
% 8.70/3.02  tff(c_3873, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_3559])).
% 8.70/3.02  tff(c_3891, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3873])).
% 8.70/3.02  tff(c_137, plain, (![B_39, A_40]: (r1_tarski(k9_relat_1(B_39, A_40), k1_relat_1(k2_funct_1(B_39))) | ~v1_relat_1(k2_funct_1(B_39)) | ~v2_funct_1(B_39) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_115, c_6])).
% 8.70/3.02  tff(c_3479, plain, (![A_40]: (r1_tarski(k9_relat_1('#skF_2', A_40), k2_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_137, c_3460])).
% 8.70/3.02  tff(c_3618, plain, (![A_242]: (r1_tarski(k9_relat_1('#skF_2', A_242), k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_2180, c_3479])).
% 8.70/3.02  tff(c_3636, plain, (![A_242]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_242)))=k9_relat_1('#skF_2', A_242) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3618, c_16])).
% 8.70/3.02  tff(c_3661, plain, (![A_242]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_242)))=k9_relat_1('#skF_2', A_242))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_3636])).
% 8.70/3.02  tff(c_3487, plain, (![A_5]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), A_5), k2_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_3460])).
% 8.70/3.02  tff(c_3783, plain, (![A_247]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), A_247), k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_3487])).
% 8.70/3.02  tff(c_3801, plain, (![A_247]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), A_247)))=k10_relat_1(k2_funct_1('#skF_2'), A_247) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3783, c_16])).
% 8.70/3.02  tff(c_6607, plain, (![A_287]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), A_287)))=k10_relat_1(k2_funct_1('#skF_2'), A_287))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_3801])).
% 8.70/3.02  tff(c_6664, plain, (![A_14]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_14)))=k10_relat_1(k2_funct_1('#skF_2'), A_14) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6607])).
% 8.70/3.02  tff(c_6695, plain, (![A_14]: (k10_relat_1(k2_funct_1('#skF_2'), A_14)=k9_relat_1('#skF_2', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_3661, c_6664])).
% 8.70/3.02  tff(c_240, plain, (![A_1, B_61, A_62]: (r1_tarski(A_1, k1_relat_1(k2_funct_1(B_61))) | ~r1_tarski(A_1, k9_relat_1(B_61, A_62)) | ~v1_relat_1(k2_funct_1(B_61)) | ~v2_funct_1(B_61) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_225, c_2])).
% 8.70/3.02  tff(c_3860, plain, (![A_1]: (r1_tarski(A_1, k1_relat_1(k2_funct_1('#skF_2'))) | ~r1_tarski(A_1, k2_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3559, c_240])).
% 8.70/3.02  tff(c_3882, plain, (![A_1]: (r1_tarski(A_1, k1_relat_1(k2_funct_1('#skF_2'))) | ~r1_tarski(A_1, k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_2180, c_3860])).
% 8.70/3.02  tff(c_7332, plain, (![B_289]: (r1_tarski(k1_relat_1(B_289), k2_relat_1(k2_funct_1(B_289))) | ~r1_tarski(k2_relat_1(B_289), k1_relat_1(k2_funct_1(B_289))) | ~v1_relat_1(B_289) | ~v1_relat_1(B_289) | ~v2_funct_1(B_289) | ~v1_funct_1(B_289) | ~v1_relat_1(B_289) | ~v1_relat_1(k2_funct_1(B_289)))), inference(superposition, [status(thm), theory('equality')], [c_566, c_98])).
% 8.70/3.02  tff(c_7336, plain, (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3882, c_7332])).
% 8.70/3.02  tff(c_7349, plain, (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3497, c_2180, c_30, c_28, c_24, c_7336])).
% 8.70/3.02  tff(c_7383, plain, (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1('#skF_2')))=k1_relat_1('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7349, c_16])).
% 8.70/3.02  tff(c_7409, plain, (k9_relat_1(k2_funct_1('#skF_2'), k2_relat_1('#skF_2'))=k1_relat_1('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_3891, c_6695, c_7383])).
% 8.70/3.02  tff(c_7523, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_7409])).
% 8.70/3.02  tff(c_7526, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_7523])).
% 8.70/3.02  tff(c_7530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_7526])).
% 8.70/3.02  tff(c_7532, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_7409])).
% 8.70/3.02  tff(c_3869, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3559, c_137])).
% 8.70/3.02  tff(c_3888, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_2180, c_3869])).
% 8.70/3.02  tff(c_3562, plain, (![B_240, A_241]: (r1_tarski(k10_relat_1(B_240, A_241), k2_relat_1(k2_funct_1(B_240))) | ~r1_tarski(A_241, k1_relat_1(k2_funct_1(B_240))) | ~v1_relat_1(B_240) | ~v2_funct_1(B_240) | ~v1_funct_1(B_240) | ~v1_relat_1(B_240) | ~v1_relat_1(k2_funct_1(B_240)))), inference(superposition, [status(thm), theory('equality')], [c_566, c_10])).
% 8.70/3.02  tff(c_3167, plain, (![A_1]: (r1_tarski(A_1, k1_relat_1('#skF_2')) | ~r1_tarski(A_1, k2_relat_1(k2_funct_1('#skF_2'))))), inference(resolution, [status(thm)], [c_3112, c_2])).
% 8.70/3.02  tff(c_3566, plain, (![A_241]: (r1_tarski(k10_relat_1('#skF_2', A_241), k1_relat_1('#skF_2')) | ~r1_tarski(A_241, k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_3562, c_3167])).
% 8.70/3.02  tff(c_4964, plain, (![A_267]: (r1_tarski(k10_relat_1('#skF_2', A_267), k1_relat_1('#skF_2')) | ~r1_tarski(A_267, k1_relat_1(k2_funct_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_30, c_28, c_24, c_3566])).
% 8.70/3.02  tff(c_4992, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_4964])).
% 8.70/3.02  tff(c_5006, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3888, c_4992])).
% 8.70/3.02  tff(c_161, plain, (![B_41]: (k10_relat_1(B_41, k1_relat_1(k2_funct_1(B_41)))=k2_relat_1(k2_funct_1(B_41)) | ~v2_funct_1(B_41) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41) | ~v1_relat_1(k2_funct_1(B_41)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_147])).
% 8.70/3.02  tff(c_3918, plain, (![A_1]: (r1_tarski(A_1, k10_relat_1('#skF_2', k1_relat_1(k2_funct_1('#skF_2')))) | ~r1_tarski(A_1, k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3888, c_186])).
% 8.70/3.02  tff(c_6098, plain, (![A_278]: (r1_tarski(A_278, k10_relat_1('#skF_2', k1_relat_1(k2_funct_1('#skF_2')))) | ~r1_tarski(A_278, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3918])).
% 8.70/3.02  tff(c_6171, plain, (![A_278]: (r1_tarski(A_278, k2_relat_1(k2_funct_1('#skF_2'))) | ~r1_tarski(A_278, k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_161, c_6098])).
% 8.70/3.02  tff(c_6226, plain, (![A_279]: (r1_tarski(A_279, k2_relat_1(k2_funct_1('#skF_2'))) | ~r1_tarski(A_279, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_30, c_28, c_24, c_6171])).
% 8.70/3.02  tff(c_8952, plain, (![A_307, A_308]: (r1_tarski(A_307, k2_relat_1(k2_funct_1('#skF_2'))) | ~r1_tarski(A_307, A_308) | ~r1_tarski(A_308, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_6226, c_2])).
% 8.70/3.02  tff(c_9076, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_8952])).
% 8.70/3.02  tff(c_9162, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5006, c_9076])).
% 8.70/3.02  tff(c_9192, plain, (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_9162, c_16])).
% 8.70/3.02  tff(c_9219, plain, (k9_relat_1(k2_funct_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_7532, c_6695, c_9192])).
% 8.70/3.02  tff(c_20, plain, (![B_17, A_16]: (k9_relat_1(k2_funct_1(B_17), A_16)=k10_relat_1(B_17, A_16) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.70/3.02  tff(c_9446, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9219, c_20])).
% 8.70/3.02  tff(c_9471, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_9446])).
% 8.70/3.02  tff(c_9473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_9471])).
% 8.70/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.70/3.02  
% 8.70/3.02  Inference rules
% 8.70/3.02  ----------------------
% 8.70/3.02  #Ref     : 0
% 8.70/3.02  #Sup     : 2433
% 8.70/3.02  #Fact    : 0
% 8.70/3.02  #Define  : 0
% 8.70/3.02  #Split   : 11
% 8.70/3.02  #Chain   : 0
% 8.70/3.02  #Close   : 0
% 8.70/3.02  
% 8.70/3.02  Ordering : KBO
% 8.70/3.02  
% 8.70/3.02  Simplification rules
% 8.70/3.02  ----------------------
% 8.70/3.02  #Subsume      : 641
% 8.70/3.02  #Demod        : 1778
% 8.70/3.02  #Tautology    : 328
% 8.70/3.02  #SimpNegUnit  : 1
% 8.70/3.02  #BackRed      : 20
% 8.70/3.02  
% 8.70/3.02  #Partial instantiations: 0
% 8.70/3.02  #Strategies tried      : 1
% 8.70/3.02  
% 8.70/3.02  Timing (in seconds)
% 8.70/3.02  ----------------------
% 8.70/3.03  Preprocessing        : 0.28
% 8.70/3.03  Parsing              : 0.16
% 8.70/3.03  CNF conversion       : 0.02
% 8.70/3.03  Main loop            : 1.94
% 8.70/3.03  Inferencing          : 0.54
% 8.70/3.03  Reduction            : 0.53
% 8.70/3.03  Demodulation         : 0.37
% 8.70/3.03  BG Simplification    : 0.06
% 8.70/3.03  Subsumption          : 0.67
% 8.70/3.03  Abstraction          : 0.08
% 8.70/3.03  MUC search           : 0.00
% 8.70/3.03  Cooper               : 0.00
% 8.70/3.03  Total                : 2.28
% 8.70/3.03  Index Insertion      : 0.00
% 8.70/3.03  Index Deletion       : 0.00
% 8.70/3.03  Index Matching       : 0.00
% 8.70/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
