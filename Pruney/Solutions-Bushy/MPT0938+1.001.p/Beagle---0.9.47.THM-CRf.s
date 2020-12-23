%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0938+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:06 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 100 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   19
%              Number of atoms          :  148 ( 264 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r8_relat_2 > r2_hidden > r1_tarski > v8_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_relat_2(A,B)
        <=> ! [C,D,E] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(E,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,E),A) )
             => r2_hidden(k4_tarski(C,E),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> r8_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).

tff(f_74,negated_conjecture,(
    ~ ! [A] : v8_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

tff(c_38,plain,(
    ! [A_34] : v1_relat_1(k1_wellord2(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [A_10,B_24] :
      ( r2_hidden('#skF_4'(A_10,B_24),B_24)
      | r8_relat_2(A_10,B_24)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_10,B_24] :
      ( r2_hidden('#skF_5'(A_10,B_24),B_24)
      | r8_relat_2(A_10,B_24)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ! [A_10,B_24] :
      ( r2_hidden('#skF_3'(A_10,B_24),B_24)
      | r8_relat_2(A_10,B_24)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ! [A_10,B_24] :
      ( r2_hidden(k4_tarski('#skF_3'(A_10,B_24),'#skF_4'(A_10,B_24)),A_10)
      | r8_relat_2(A_10,B_24)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [C_8,D_9,A_2] :
      ( r1_tarski(C_8,D_9)
      | ~ r2_hidden(k4_tarski(C_8,D_9),k1_wellord2(A_2))
      | ~ r2_hidden(D_9,A_2)
      | ~ r2_hidden(C_8,A_2)
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,(
    ! [C_64,D_65,A_66] :
      ( r1_tarski(C_64,D_65)
      | ~ r2_hidden(k4_tarski(C_64,D_65),k1_wellord2(A_66))
      | ~ r2_hidden(D_65,A_66)
      | ~ r2_hidden(C_64,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_125,plain,(
    ! [A_66,B_24] :
      ( r1_tarski('#skF_3'(k1_wellord2(A_66),B_24),'#skF_4'(k1_wellord2(A_66),B_24))
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_66),B_24),A_66)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_66),B_24),A_66)
      | r8_relat_2(k1_wellord2(A_66),B_24)
      | ~ v1_relat_1(k1_wellord2(A_66)) ) ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_133,plain,(
    ! [A_66,B_24] :
      ( r1_tarski('#skF_3'(k1_wellord2(A_66),B_24),'#skF_4'(k1_wellord2(A_66),B_24))
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_66),B_24),A_66)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_66),B_24),A_66)
      | r8_relat_2(k1_wellord2(A_66),B_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_125])).

tff(c_28,plain,(
    ! [A_10,B_24] :
      ( r2_hidden(k4_tarski('#skF_4'(A_10,B_24),'#skF_5'(A_10,B_24)),A_10)
      | r8_relat_2(A_10,B_24)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_129,plain,(
    ! [A_66,B_24] :
      ( r1_tarski('#skF_4'(k1_wellord2(A_66),B_24),'#skF_5'(k1_wellord2(A_66),B_24))
      | ~ r2_hidden('#skF_5'(k1_wellord2(A_66),B_24),A_66)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_66),B_24),A_66)
      | r8_relat_2(k1_wellord2(A_66),B_24)
      | ~ v1_relat_1(k1_wellord2(A_66)) ) ),
    inference(resolution,[status(thm)],[c_28,c_118])).

tff(c_160,plain,(
    ! [A_72,B_73] :
      ( r1_tarski('#skF_4'(k1_wellord2(A_72),B_73),'#skF_5'(k1_wellord2(A_72),B_73))
      | ~ r2_hidden('#skF_5'(k1_wellord2(A_72),B_73),A_72)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_72),B_73),A_72)
      | r8_relat_2(k1_wellord2(A_72),B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_129])).

tff(c_40,plain,(
    ! [A_35,C_37,B_36] :
      ( r1_tarski(A_35,C_37)
      | ~ r1_tarski(B_36,C_37)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_186,plain,(
    ! [A_75,A_76,B_77] :
      ( r1_tarski(A_75,'#skF_5'(k1_wellord2(A_76),B_77))
      | ~ r1_tarski(A_75,'#skF_4'(k1_wellord2(A_76),B_77))
      | ~ r2_hidden('#skF_5'(k1_wellord2(A_76),B_77),A_76)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_76),B_77),A_76)
      | r8_relat_2(k1_wellord2(A_76),B_77) ) ),
    inference(resolution,[status(thm)],[c_160,c_40])).

tff(c_189,plain,(
    ! [A_75,B_24] :
      ( r1_tarski(A_75,'#skF_5'(k1_wellord2(B_24),B_24))
      | ~ r1_tarski(A_75,'#skF_4'(k1_wellord2(B_24),B_24))
      | ~ r2_hidden('#skF_4'(k1_wellord2(B_24),B_24),B_24)
      | r8_relat_2(k1_wellord2(B_24),B_24)
      | ~ v1_relat_1(k1_wellord2(B_24)) ) ),
    inference(resolution,[status(thm)],[c_32,c_186])).

tff(c_193,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,'#skF_5'(k1_wellord2(B_79),B_79))
      | ~ r1_tarski(A_78,'#skF_4'(k1_wellord2(B_79),B_79))
      | ~ r2_hidden('#skF_4'(k1_wellord2(B_79),B_79),B_79)
      | r8_relat_2(k1_wellord2(B_79),B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_189])).

tff(c_196,plain,(
    ! [A_78,B_24] :
      ( r1_tarski(A_78,'#skF_5'(k1_wellord2(B_24),B_24))
      | ~ r1_tarski(A_78,'#skF_4'(k1_wellord2(B_24),B_24))
      | r8_relat_2(k1_wellord2(B_24),B_24)
      | ~ v1_relat_1(k1_wellord2(B_24)) ) ),
    inference(resolution,[status(thm)],[c_34,c_193])).

tff(c_215,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(A_85,'#skF_5'(k1_wellord2(B_86),B_86))
      | ~ r1_tarski(A_85,'#skF_4'(k1_wellord2(B_86),B_86))
      | r8_relat_2(k1_wellord2(B_86),B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_196])).

tff(c_20,plain,(
    ! [C_8,D_9,A_2] :
      ( r2_hidden(k4_tarski(C_8,D_9),k1_wellord2(A_2))
      | ~ r1_tarski(C_8,D_9)
      | ~ r2_hidden(D_9,A_2)
      | ~ r2_hidden(C_8,A_2)
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    ! [C_61,D_62,A_63] :
      ( r2_hidden(k4_tarski(C_61,D_62),k1_wellord2(A_63))
      | ~ r1_tarski(C_61,D_62)
      | ~ r2_hidden(D_62,A_63)
      | ~ r2_hidden(C_61,A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_26,plain,(
    ! [A_10,B_24] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_10,B_24),'#skF_5'(A_10,B_24)),A_10)
      | r8_relat_2(A_10,B_24)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    ! [A_63,B_24] :
      ( r8_relat_2(k1_wellord2(A_63),B_24)
      | ~ v1_relat_1(k1_wellord2(A_63))
      | ~ r1_tarski('#skF_3'(k1_wellord2(A_63),B_24),'#skF_5'(k1_wellord2(A_63),B_24))
      | ~ r2_hidden('#skF_5'(k1_wellord2(A_63),B_24),A_63)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_63),B_24),A_63) ) ),
    inference(resolution,[status(thm)],[c_110,c_26])).

tff(c_117,plain,(
    ! [A_63,B_24] :
      ( r8_relat_2(k1_wellord2(A_63),B_24)
      | ~ r1_tarski('#skF_3'(k1_wellord2(A_63),B_24),'#skF_5'(k1_wellord2(A_63),B_24))
      | ~ r2_hidden('#skF_5'(k1_wellord2(A_63),B_24),A_63)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_63),B_24),A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_114])).

tff(c_234,plain,(
    ! [B_90] :
      ( ~ r2_hidden('#skF_5'(k1_wellord2(B_90),B_90),B_90)
      | ~ r2_hidden('#skF_3'(k1_wellord2(B_90),B_90),B_90)
      | ~ r1_tarski('#skF_3'(k1_wellord2(B_90),B_90),'#skF_4'(k1_wellord2(B_90),B_90))
      | r8_relat_2(k1_wellord2(B_90),B_90) ) ),
    inference(resolution,[status(thm)],[c_215,c_117])).

tff(c_241,plain,(
    ! [B_94] :
      ( ~ r2_hidden('#skF_5'(k1_wellord2(B_94),B_94),B_94)
      | ~ r2_hidden('#skF_4'(k1_wellord2(B_94),B_94),B_94)
      | ~ r2_hidden('#skF_3'(k1_wellord2(B_94),B_94),B_94)
      | r8_relat_2(k1_wellord2(B_94),B_94) ) ),
    inference(resolution,[status(thm)],[c_133,c_234])).

tff(c_245,plain,(
    ! [B_24] :
      ( ~ r2_hidden('#skF_5'(k1_wellord2(B_24),B_24),B_24)
      | ~ r2_hidden('#skF_4'(k1_wellord2(B_24),B_24),B_24)
      | r8_relat_2(k1_wellord2(B_24),B_24)
      | ~ v1_relat_1(k1_wellord2(B_24)) ) ),
    inference(resolution,[status(thm)],[c_36,c_241])).

tff(c_249,plain,(
    ! [B_95] :
      ( ~ r2_hidden('#skF_5'(k1_wellord2(B_95),B_95),B_95)
      | ~ r2_hidden('#skF_4'(k1_wellord2(B_95),B_95),B_95)
      | r8_relat_2(k1_wellord2(B_95),B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_245])).

tff(c_253,plain,(
    ! [B_24] :
      ( ~ r2_hidden('#skF_4'(k1_wellord2(B_24),B_24),B_24)
      | r8_relat_2(k1_wellord2(B_24),B_24)
      | ~ v1_relat_1(k1_wellord2(B_24)) ) ),
    inference(resolution,[status(thm)],[c_32,c_249])).

tff(c_257,plain,(
    ! [B_96] :
      ( ~ r2_hidden('#skF_4'(k1_wellord2(B_96),B_96),B_96)
      | r8_relat_2(k1_wellord2(B_96),B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_253])).

tff(c_261,plain,(
    ! [B_24] :
      ( r8_relat_2(k1_wellord2(B_24),B_24)
      | ~ v1_relat_1(k1_wellord2(B_24)) ) ),
    inference(resolution,[status(thm)],[c_34,c_257])).

tff(c_264,plain,(
    ! [B_24] : r8_relat_2(k1_wellord2(B_24),B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_261])).

tff(c_18,plain,(
    ! [A_2] :
      ( k3_relat_1(k1_wellord2(A_2)) = A_2
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    ! [A_2] : k3_relat_1(k1_wellord2(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_18])).

tff(c_66,plain,(
    ! [A_42] :
      ( v8_relat_2(A_42)
      | ~ r8_relat_2(A_42,k3_relat_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,(
    ! [A_2] :
      ( v8_relat_2(k1_wellord2(A_2))
      | ~ r8_relat_2(k1_wellord2(A_2),A_2)
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_66])).

tff(c_75,plain,(
    ! [A_2] :
      ( v8_relat_2(k1_wellord2(A_2))
      | ~ r8_relat_2(k1_wellord2(A_2),A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_72])).

tff(c_270,plain,(
    ! [A_2] : v8_relat_2(k1_wellord2(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_75])).

tff(c_42,plain,(
    ~ v8_relat_2(k1_wellord2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_42])).

%------------------------------------------------------------------------------
