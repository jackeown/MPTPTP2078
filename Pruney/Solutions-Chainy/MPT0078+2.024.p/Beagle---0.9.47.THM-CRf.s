%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:42 EST 2020

% Result     : Theorem 18.21s
% Output     : CNFRefutation 18.33s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 236 expanded)
%              Number of leaves         :   28 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  164 ( 365 expanded)
%              Number of equality atoms :   59 ( 168 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_101,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(c_34,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(k4_xboole_0(A_17,B_18),C_19)
      | ~ r1_tarski(A_17,k2_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_122,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_131,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,k4_xboole_0(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_122])).

tff(c_140,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_131])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_81,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_81])).

tff(c_265,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_xboole_0(A_63,C_64)
      | ~ r1_xboole_0(B_65,C_64)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_281,plain,(
    ! [A_63] :
      ( r1_xboole_0(A_63,'#skF_3')
      | ~ r1_tarski(A_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_91,c_265])).

tff(c_137,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,k3_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_122])).

tff(c_1168,plain,(
    ! [A_110,B_111] : k3_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k3_xboole_0(A_110,B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_137])).

tff(c_1236,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1168])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_950,plain,(
    ! [A_102,B_103,B_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | r1_xboole_0(k3_xboole_0(A_102,B_103),B_104) ) ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_1692,plain,(
    ! [B_138,A_139,B_140] :
      ( ~ r1_xboole_0(B_138,A_139)
      | r1_xboole_0(k3_xboole_0(A_139,B_138),B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_950])).

tff(c_30555,plain,(
    ! [A_649,B_650,B_651] :
      ( ~ r1_xboole_0(k3_xboole_0(A_649,B_650),B_650)
      | r1_xboole_0(k3_xboole_0(B_650,A_649),B_651) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1236,c_1692])).

tff(c_57972,plain,(
    ! [A_950,B_951] :
      ( r1_xboole_0(k3_xboole_0('#skF_3',A_950),B_951)
      | ~ r1_tarski(k3_xboole_0(A_950,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_281,c_30555])).

tff(c_30,plain,(
    ! [A_31] :
      ( ~ r1_xboole_0(A_31,A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58227,plain,(
    ! [A_958] :
      ( k3_xboole_0('#skF_3',A_958) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0(A_958,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_57972,c_30])).

tff(c_58347,plain,(
    ! [A_960] :
      ( k3_xboole_0('#skF_3',A_960) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0('#skF_3',A_960),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58227])).

tff(c_58421,plain,(
    ! [B_23] :
      ( k3_xboole_0('#skF_3',k4_xboole_0('#skF_3',B_23)) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0('#skF_3',B_23),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_58347])).

tff(c_58456,plain,(
    ! [B_961] :
      ( k4_xboole_0('#skF_3',B_961) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0('#skF_3',B_961),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_58421])).

tff(c_63290,plain,(
    ! [B_986] :
      ( k4_xboole_0('#skF_3',B_986) = k1_xboole_0
      | ~ r1_tarski('#skF_3',k2_xboole_0(B_986,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18,c_58456])).

tff(c_63296,plain,
    ( k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_63290])).

tff(c_63303,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_63296])).

tff(c_358,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(k4_xboole_0(A_71,B_72),C_73)
      | ~ r1_tarski(A_71,k2_xboole_0(B_72,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1916,plain,(
    ! [A_149,B_150,C_151] :
      ( r1_tarski(k4_xboole_0(A_149,B_150),C_151)
      | ~ r1_tarski(A_149,k2_xboole_0(k3_xboole_0(A_149,B_150),C_151)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_358])).

tff(c_5655,plain,(
    ! [B_300,A_301,C_302] :
      ( r1_tarski(k4_xboole_0(B_300,A_301),C_302)
      | ~ r1_tarski(B_300,k2_xboole_0(k3_xboole_0(A_301,B_300),C_302)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1916])).

tff(c_5706,plain,(
    ! [A_22,B_23,C_302] :
      ( r1_tarski(k4_xboole_0(k4_xboole_0(A_22,B_23),A_22),C_302)
      | ~ r1_tarski(k4_xboole_0(A_22,B_23),k2_xboole_0(k4_xboole_0(A_22,B_23),C_302)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_5655])).

tff(c_5727,plain,(
    ! [A_22,B_23,C_302] : r1_tarski(k4_xboole_0(k4_xboole_0(A_22,B_23),A_22),C_302) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5706])).

tff(c_6754,plain,(
    ! [A_315,B_316,C_317] : r1_tarski(k4_xboole_0(k4_xboole_0(A_315,B_316),A_315),C_317) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5706])).

tff(c_635,plain,(
    ! [A_96,C_97,B_98,D_99] :
      ( r1_xboole_0(A_96,C_97)
      | ~ r1_xboole_0(B_98,D_99)
      | ~ r1_tarski(C_97,D_99)
      | ~ r1_tarski(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1098,plain,(
    ! [A_108,C_109] :
      ( r1_xboole_0(A_108,C_109)
      | ~ r1_tarski(C_109,'#skF_4')
      | ~ r1_tarski(A_108,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_635])).

tff(c_1119,plain,(
    ! [C_109] :
      ( k1_xboole_0 = C_109
      | ~ r1_tarski(C_109,'#skF_4')
      | ~ r1_tarski(C_109,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1098,c_30])).

tff(c_6806,plain,(
    ! [A_315,B_316] :
      ( k4_xboole_0(k4_xboole_0(A_315,B_316),A_315) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(k4_xboole_0(A_315,B_316),A_315),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6754,c_1119])).

tff(c_7090,plain,(
    ! [A_320,B_321] : k4_xboole_0(k4_xboole_0(A_320,B_321),A_320) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5727,c_6806])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | k4_xboole_0(B_16,A_15) != k4_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7132,plain,(
    ! [A_320,B_321] :
      ( k4_xboole_0(A_320,B_321) = A_320
      | k4_xboole_0(A_320,k4_xboole_0(A_320,B_321)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7090,c_16])).

tff(c_7693,plain,(
    ! [A_333,B_334] :
      ( k4_xboole_0(A_333,B_334) = A_333
      | k3_xboole_0(A_333,B_334) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7132])).

tff(c_7819,plain,(
    ! [A_333,B_23] :
      ( k3_xboole_0(A_333,B_23) = A_333
      | k3_xboole_0(A_333,k4_xboole_0(A_333,B_23)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7693,c_22])).

tff(c_7906,plain,(
    ! [A_333,B_23] :
      ( k3_xboole_0(A_333,B_23) = A_333
      | k4_xboole_0(A_333,B_23) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_7819])).

tff(c_63550,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_63303,c_7906])).

tff(c_99,plain,(
    r1_tarski('#skF_5',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_32])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_90,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_282,plain,(
    ! [A_63] :
      ( r1_xboole_0(A_63,'#skF_5')
      | ~ r1_tarski(A_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_265])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_484,plain,(
    ! [B_86,A_87,C_88] :
      ( ~ r1_xboole_0(B_86,A_87)
      | ~ r2_hidden(C_88,k3_xboole_0(A_87,B_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_150])).

tff(c_1460,plain,(
    ! [B_128,A_129,A_130] :
      ( ~ r1_xboole_0(B_128,A_129)
      | r1_xboole_0(A_130,k3_xboole_0(A_129,B_128)) ) ),
    inference(resolution,[status(thm)],[c_8,c_484])).

tff(c_16549,plain,(
    ! [A_481,B_482,A_483] :
      ( ~ r1_xboole_0(k4_xboole_0(A_481,B_482),A_481)
      | r1_xboole_0(A_483,k4_xboole_0(A_481,B_482)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_1460])).

tff(c_65126,plain,(
    ! [A_995,B_996] :
      ( r1_xboole_0(A_995,k4_xboole_0('#skF_5',B_996))
      | ~ r1_tarski(k4_xboole_0('#skF_5',B_996),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_282,c_16549])).

tff(c_66233,plain,(
    ! [B_1010] :
      ( k4_xboole_0('#skF_5',B_1010) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0('#skF_5',B_1010),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65126,c_30])).

tff(c_66673,plain,(
    ! [B_1014] :
      ( k4_xboole_0('#skF_5',B_1014) = k1_xboole_0
      | ~ r1_tarski('#skF_5',k2_xboole_0(B_1014,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18,c_66233])).

tff(c_66688,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_66673])).

tff(c_107,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_119,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_28,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_198,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_214,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_198])).

tff(c_223,plain,(
    ! [B_6] : r1_xboole_0(k1_xboole_0,B_6) ),
    inference(resolution,[status(thm)],[c_10,c_214])).

tff(c_400,plain,(
    ! [A_76,B_77] :
      ( r1_xboole_0(A_76,B_77)
      | ~ r1_tarski(A_76,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_223,c_265])).

tff(c_426,plain,(
    ! [B_80] :
      ( k1_xboole_0 = B_80
      | ~ r1_tarski(B_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_400,c_30])).

tff(c_5628,plain,(
    ! [A_298,B_299] :
      ( k4_xboole_0(A_298,B_299) = k1_xboole_0
      | ~ r1_tarski(A_298,k2_xboole_0(B_299,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_18,c_426])).

tff(c_5654,plain,(
    ! [A_32] : k4_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_5628])).

tff(c_1193,plain,(
    ! [A_110,B_111] : k4_xboole_0(k3_xboole_0(A_110,B_111),k3_xboole_0(A_110,B_111)) = k4_xboole_0(k3_xboole_0(A_110,B_111),A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_119])).

tff(c_6938,plain,(
    ! [A_318,B_319] : k4_xboole_0(k3_xboole_0(A_318,B_319),A_318) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5654,c_1193])).

tff(c_7306,plain,(
    ! [B_325,A_326] : k4_xboole_0(k3_xboole_0(B_325,A_326),A_326) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6938])).

tff(c_7363,plain,(
    ! [B_325,A_326] :
      ( k3_xboole_0(B_325,A_326) = A_326
      | k4_xboole_0(A_326,k3_xboole_0(B_325,A_326)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7306,c_16])).

tff(c_7452,plain,(
    ! [B_325,A_326] :
      ( k3_xboole_0(B_325,A_326) = A_326
      | k4_xboole_0(A_326,B_325) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_7363])).

tff(c_66797,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_66688,c_7452])).

tff(c_66945,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63550,c_66797])).

tff(c_66947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_66945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.21/9.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.33/9.47  
% 18.33/9.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.33/9.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 18.33/9.47  
% 18.33/9.47  %Foreground sorts:
% 18.33/9.47  
% 18.33/9.47  
% 18.33/9.47  %Background operators:
% 18.33/9.47  
% 18.33/9.47  
% 18.33/9.47  %Foreground operators:
% 18.33/9.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.33/9.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.33/9.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.33/9.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.33/9.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.33/9.47  tff('#skF_5', type, '#skF_5': $i).
% 18.33/9.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 18.33/9.47  tff('#skF_3', type, '#skF_3': $i).
% 18.33/9.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.33/9.47  tff('#skF_4', type, '#skF_4': $i).
% 18.33/9.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.33/9.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 18.33/9.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.33/9.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.33/9.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.33/9.47  
% 18.33/9.49  tff(f_112, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 18.33/9.49  tff(f_103, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.33/9.49  tff(f_71, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 18.33/9.49  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 18.33/9.49  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.33/9.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.33/9.49  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 18.33/9.49  tff(f_81, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 18.33/9.49  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 18.33/9.49  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 18.33/9.49  tff(f_101, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 18.33/9.49  tff(f_89, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 18.33/9.49  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 18.33/9.49  tff(c_34, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_112])).
% 18.33/9.49  tff(c_32, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.33/9.49  tff(c_40, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 18.33/9.49  tff(c_18, plain, (![A_17, B_18, C_19]: (r1_tarski(k4_xboole_0(A_17, B_18), C_19) | ~r1_tarski(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.33/9.49  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 18.33/9.49  tff(c_22, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.33/9.49  tff(c_122, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.33/9.49  tff(c_131, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k3_xboole_0(A_22, k4_xboole_0(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_122])).
% 18.33/9.49  tff(c_140, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_131])).
% 18.33/9.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.33/9.49  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 18.33/9.49  tff(c_81, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.33/9.49  tff(c_91, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_81])).
% 18.33/9.49  tff(c_265, plain, (![A_63, C_64, B_65]: (r1_xboole_0(A_63, C_64) | ~r1_xboole_0(B_65, C_64) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.33/9.49  tff(c_281, plain, (![A_63]: (r1_xboole_0(A_63, '#skF_3') | ~r1_tarski(A_63, '#skF_4'))), inference(resolution, [status(thm)], [c_91, c_265])).
% 18.33/9.49  tff(c_137, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, k3_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_122])).
% 18.33/9.49  tff(c_1168, plain, (![A_110, B_111]: (k3_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k3_xboole_0(A_110, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_137])).
% 18.33/9.49  tff(c_1236, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1168])).
% 18.33/9.49  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.33/9.49  tff(c_150, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.33/9.49  tff(c_950, plain, (![A_102, B_103, B_104]: (~r1_xboole_0(A_102, B_103) | r1_xboole_0(k3_xboole_0(A_102, B_103), B_104))), inference(resolution, [status(thm)], [c_10, c_150])).
% 18.33/9.49  tff(c_1692, plain, (![B_138, A_139, B_140]: (~r1_xboole_0(B_138, A_139) | r1_xboole_0(k3_xboole_0(A_139, B_138), B_140))), inference(superposition, [status(thm), theory('equality')], [c_2, c_950])).
% 18.33/9.49  tff(c_30555, plain, (![A_649, B_650, B_651]: (~r1_xboole_0(k3_xboole_0(A_649, B_650), B_650) | r1_xboole_0(k3_xboole_0(B_650, A_649), B_651))), inference(superposition, [status(thm), theory('equality')], [c_1236, c_1692])).
% 18.33/9.49  tff(c_57972, plain, (![A_950, B_951]: (r1_xboole_0(k3_xboole_0('#skF_3', A_950), B_951) | ~r1_tarski(k3_xboole_0(A_950, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_281, c_30555])).
% 18.33/9.49  tff(c_30, plain, (![A_31]: (~r1_xboole_0(A_31, A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.33/9.49  tff(c_58227, plain, (![A_958]: (k3_xboole_0('#skF_3', A_958)=k1_xboole_0 | ~r1_tarski(k3_xboole_0(A_958, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_57972, c_30])).
% 18.33/9.49  tff(c_58347, plain, (![A_960]: (k3_xboole_0('#skF_3', A_960)=k1_xboole_0 | ~r1_tarski(k3_xboole_0('#skF_3', A_960), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_58227])).
% 18.33/9.49  tff(c_58421, plain, (![B_23]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', B_23))=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_3', B_23), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_58347])).
% 18.33/9.49  tff(c_58456, plain, (![B_961]: (k4_xboole_0('#skF_3', B_961)=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_3', B_961), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_58421])).
% 18.33/9.49  tff(c_63290, plain, (![B_986]: (k4_xboole_0('#skF_3', B_986)=k1_xboole_0 | ~r1_tarski('#skF_3', k2_xboole_0(B_986, '#skF_4')))), inference(resolution, [status(thm)], [c_18, c_58456])).
% 18.33/9.49  tff(c_63296, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0 | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_63290])).
% 18.33/9.49  tff(c_63303, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_63296])).
% 18.33/9.49  tff(c_358, plain, (![A_71, B_72, C_73]: (r1_tarski(k4_xboole_0(A_71, B_72), C_73) | ~r1_tarski(A_71, k2_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.33/9.49  tff(c_1916, plain, (![A_149, B_150, C_151]: (r1_tarski(k4_xboole_0(A_149, B_150), C_151) | ~r1_tarski(A_149, k2_xboole_0(k3_xboole_0(A_149, B_150), C_151)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_358])).
% 18.33/9.49  tff(c_5655, plain, (![B_300, A_301, C_302]: (r1_tarski(k4_xboole_0(B_300, A_301), C_302) | ~r1_tarski(B_300, k2_xboole_0(k3_xboole_0(A_301, B_300), C_302)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1916])).
% 18.33/9.49  tff(c_5706, plain, (![A_22, B_23, C_302]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_22, B_23), A_22), C_302) | ~r1_tarski(k4_xboole_0(A_22, B_23), k2_xboole_0(k4_xboole_0(A_22, B_23), C_302)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_5655])).
% 18.33/9.49  tff(c_5727, plain, (![A_22, B_23, C_302]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_22, B_23), A_22), C_302))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5706])).
% 18.33/9.49  tff(c_6754, plain, (![A_315, B_316, C_317]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_315, B_316), A_315), C_317))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5706])).
% 18.33/9.49  tff(c_635, plain, (![A_96, C_97, B_98, D_99]: (r1_xboole_0(A_96, C_97) | ~r1_xboole_0(B_98, D_99) | ~r1_tarski(C_97, D_99) | ~r1_tarski(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.33/9.49  tff(c_1098, plain, (![A_108, C_109]: (r1_xboole_0(A_108, C_109) | ~r1_tarski(C_109, '#skF_4') | ~r1_tarski(A_108, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_635])).
% 18.33/9.49  tff(c_1119, plain, (![C_109]: (k1_xboole_0=C_109 | ~r1_tarski(C_109, '#skF_4') | ~r1_tarski(C_109, '#skF_3'))), inference(resolution, [status(thm)], [c_1098, c_30])).
% 18.33/9.49  tff(c_6806, plain, (![A_315, B_316]: (k4_xboole_0(k4_xboole_0(A_315, B_316), A_315)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(k4_xboole_0(A_315, B_316), A_315), '#skF_4'))), inference(resolution, [status(thm)], [c_6754, c_1119])).
% 18.33/9.49  tff(c_7090, plain, (![A_320, B_321]: (k4_xboole_0(k4_xboole_0(A_320, B_321), A_320)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5727, c_6806])).
% 18.33/9.49  tff(c_16, plain, (![B_16, A_15]: (B_16=A_15 | k4_xboole_0(B_16, A_15)!=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.33/9.49  tff(c_7132, plain, (![A_320, B_321]: (k4_xboole_0(A_320, B_321)=A_320 | k4_xboole_0(A_320, k4_xboole_0(A_320, B_321))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7090, c_16])).
% 18.33/9.49  tff(c_7693, plain, (![A_333, B_334]: (k4_xboole_0(A_333, B_334)=A_333 | k3_xboole_0(A_333, B_334)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7132])).
% 18.33/9.49  tff(c_7819, plain, (![A_333, B_23]: (k3_xboole_0(A_333, B_23)=A_333 | k3_xboole_0(A_333, k4_xboole_0(A_333, B_23))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7693, c_22])).
% 18.33/9.49  tff(c_7906, plain, (![A_333, B_23]: (k3_xboole_0(A_333, B_23)=A_333 | k4_xboole_0(A_333, B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_7819])).
% 18.33/9.49  tff(c_63550, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_63303, c_7906])).
% 18.33/9.49  tff(c_99, plain, (r1_tarski('#skF_5', k2_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_32])).
% 18.33/9.49  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 18.33/9.49  tff(c_90, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_81])).
% 18.33/9.49  tff(c_282, plain, (![A_63]: (r1_xboole_0(A_63, '#skF_5') | ~r1_tarski(A_63, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_265])).
% 18.33/9.49  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.33/9.49  tff(c_484, plain, (![B_86, A_87, C_88]: (~r1_xboole_0(B_86, A_87) | ~r2_hidden(C_88, k3_xboole_0(A_87, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_150])).
% 18.33/9.49  tff(c_1460, plain, (![B_128, A_129, A_130]: (~r1_xboole_0(B_128, A_129) | r1_xboole_0(A_130, k3_xboole_0(A_129, B_128)))), inference(resolution, [status(thm)], [c_8, c_484])).
% 18.33/9.49  tff(c_16549, plain, (![A_481, B_482, A_483]: (~r1_xboole_0(k4_xboole_0(A_481, B_482), A_481) | r1_xboole_0(A_483, k4_xboole_0(A_481, B_482)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_1460])).
% 18.33/9.49  tff(c_65126, plain, (![A_995, B_996]: (r1_xboole_0(A_995, k4_xboole_0('#skF_5', B_996)) | ~r1_tarski(k4_xboole_0('#skF_5', B_996), '#skF_4'))), inference(resolution, [status(thm)], [c_282, c_16549])).
% 18.33/9.49  tff(c_66233, plain, (![B_1010]: (k4_xboole_0('#skF_5', B_1010)=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_5', B_1010), '#skF_4'))), inference(resolution, [status(thm)], [c_65126, c_30])).
% 18.33/9.49  tff(c_66673, plain, (![B_1014]: (k4_xboole_0('#skF_5', B_1014)=k1_xboole_0 | ~r1_tarski('#skF_5', k2_xboole_0(B_1014, '#skF_4')))), inference(resolution, [status(thm)], [c_18, c_66233])).
% 18.33/9.49  tff(c_66688, plain, (k4_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_66673])).
% 18.33/9.49  tff(c_107, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_73])).
% 18.33/9.49  tff(c_119, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 18.33/9.49  tff(c_28, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.33/9.49  tff(c_198, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.33/9.49  tff(c_214, plain, (![C_59]: (~r2_hidden(C_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_198])).
% 18.33/9.49  tff(c_223, plain, (![B_6]: (r1_xboole_0(k1_xboole_0, B_6))), inference(resolution, [status(thm)], [c_10, c_214])).
% 18.33/9.49  tff(c_400, plain, (![A_76, B_77]: (r1_xboole_0(A_76, B_77) | ~r1_tarski(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_223, c_265])).
% 18.33/9.49  tff(c_426, plain, (![B_80]: (k1_xboole_0=B_80 | ~r1_tarski(B_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_400, c_30])).
% 18.33/9.49  tff(c_5628, plain, (![A_298, B_299]: (k4_xboole_0(A_298, B_299)=k1_xboole_0 | ~r1_tarski(A_298, k2_xboole_0(B_299, k1_xboole_0)))), inference(resolution, [status(thm)], [c_18, c_426])).
% 18.33/9.49  tff(c_5654, plain, (![A_32]: (k4_xboole_0(A_32, A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_5628])).
% 18.33/9.49  tff(c_1193, plain, (![A_110, B_111]: (k4_xboole_0(k3_xboole_0(A_110, B_111), k3_xboole_0(A_110, B_111))=k4_xboole_0(k3_xboole_0(A_110, B_111), A_110))), inference(superposition, [status(thm), theory('equality')], [c_1168, c_119])).
% 18.33/9.49  tff(c_6938, plain, (![A_318, B_319]: (k4_xboole_0(k3_xboole_0(A_318, B_319), A_318)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5654, c_1193])).
% 18.33/9.49  tff(c_7306, plain, (![B_325, A_326]: (k4_xboole_0(k3_xboole_0(B_325, A_326), A_326)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6938])).
% 18.33/9.49  tff(c_7363, plain, (![B_325, A_326]: (k3_xboole_0(B_325, A_326)=A_326 | k4_xboole_0(A_326, k3_xboole_0(B_325, A_326))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7306, c_16])).
% 18.33/9.49  tff(c_7452, plain, (![B_325, A_326]: (k3_xboole_0(B_325, A_326)=A_326 | k4_xboole_0(A_326, B_325)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_7363])).
% 18.33/9.49  tff(c_66797, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_66688, c_7452])).
% 18.33/9.49  tff(c_66945, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63550, c_66797])).
% 18.33/9.49  tff(c_66947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_66945])).
% 18.33/9.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.33/9.49  
% 18.33/9.49  Inference rules
% 18.33/9.49  ----------------------
% 18.33/9.49  #Ref     : 5
% 18.33/9.49  #Sup     : 17191
% 18.33/9.49  #Fact    : 0
% 18.33/9.49  #Define  : 0
% 18.33/9.49  #Split   : 14
% 18.33/9.49  #Chain   : 0
% 18.33/9.49  #Close   : 0
% 18.33/9.49  
% 18.33/9.49  Ordering : KBO
% 18.33/9.49  
% 18.33/9.49  Simplification rules
% 18.33/9.49  ----------------------
% 18.33/9.49  #Subsume      : 7939
% 18.33/9.49  #Demod        : 9407
% 18.33/9.49  #Tautology    : 4138
% 18.33/9.49  #SimpNegUnit  : 425
% 18.33/9.49  #BackRed      : 21
% 18.33/9.49  
% 18.33/9.49  #Partial instantiations: 0
% 18.33/9.49  #Strategies tried      : 1
% 18.33/9.49  
% 18.33/9.49  Timing (in seconds)
% 18.33/9.49  ----------------------
% 18.48/9.49  Preprocessing        : 0.30
% 18.48/9.49  Parsing              : 0.16
% 18.48/9.49  CNF conversion       : 0.02
% 18.48/9.49  Main loop            : 8.41
% 18.48/9.49  Inferencing          : 1.18
% 18.48/9.49  Reduction            : 3.47
% 18.48/9.49  Demodulation         : 2.75
% 18.48/9.49  BG Simplification    : 0.12
% 18.48/9.49  Subsumption          : 3.13
% 18.48/9.49  Abstraction          : 0.18
% 18.48/9.49  MUC search           : 0.00
% 18.48/9.49  Cooper               : 0.00
% 18.48/9.49  Total                : 8.75
% 18.48/9.49  Index Insertion      : 0.00
% 18.48/9.49  Index Deletion       : 0.00
% 18.48/9.49  Index Matching       : 0.00
% 18.48/9.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
