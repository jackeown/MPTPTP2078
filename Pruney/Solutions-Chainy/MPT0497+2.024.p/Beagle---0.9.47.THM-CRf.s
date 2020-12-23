%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:42 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 137 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 248 expanded)
%              Number of equality atoms :   37 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_51,axiom,(
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

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_52,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_85,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_180,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_805,plain,(
    ! [A_90,B_91,C_92] :
      ( r2_hidden(A_90,B_91)
      | ~ r2_hidden(A_90,k1_relat_1(k7_relat_1(C_92,B_91)))
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_815,plain,(
    ! [C_92,B_91,B_6] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_92,B_91)),B_6),B_91)
      | ~ v1_relat_1(C_92)
      | r1_xboole_0(k1_relat_1(k7_relat_1(C_92,B_91)),B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_805])).

tff(c_1385,plain,(
    ! [A_112,C_113,B_114] :
      ( r2_hidden(A_112,k1_relat_1(C_113))
      | ~ r2_hidden(A_112,k1_relat_1(k7_relat_1(C_113,B_114)))
      | ~ v1_relat_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4046,plain,(
    ! [C_206,B_207,B_208] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_206,B_207)),B_208),k1_relat_1(C_206))
      | ~ v1_relat_1(C_206)
      | r1_xboole_0(k1_relat_1(k7_relat_1(C_206,B_207)),B_208) ) ),
    inference(resolution,[status(thm)],[c_12,c_1385])).

tff(c_459,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_hidden(C_74,B_73)
      | ~ r2_hidden(C_74,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_486,plain,(
    ! [C_74] :
      ( ~ r2_hidden(C_74,'#skF_2')
      | ~ r2_hidden(C_74,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_85,c_459])).

tff(c_4065,plain,(
    ! [B_207,B_208] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_3',B_207)),B_208),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3',B_207)),B_208) ) ),
    inference(resolution,[status(thm)],[c_4046,c_486])).

tff(c_4298,plain,(
    ! [B_215,B_216] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_3',B_215)),B_216),'#skF_2')
      | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3',B_215)),B_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4065])).

tff(c_4313,plain,(
    ! [B_6] :
      ( ~ v1_relat_1('#skF_3')
      | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),B_6) ) ),
    inference(resolution,[status(thm)],[c_815,c_4298])).

tff(c_4589,plain,(
    ! [B_219] : r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),B_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4313])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4807,plain,(
    ! [B_226] : k3_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),B_226) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4589,c_2])).

tff(c_304,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [B_13,A_12] : r1_xboole_0(B_13,k4_xboole_0(A_12,B_13)) ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_93,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = A_41
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_112,plain,(
    ! [B_13,A_12] : k4_xboole_0(B_13,k4_xboole_0(A_12,B_13)) = B_13 ),
    inference(resolution,[status(thm)],[c_66,c_93])).

tff(c_323,plain,(
    ! [B_64] : k3_xboole_0(B_64,B_64) = B_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_112])).

tff(c_4881,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4807,c_323])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k7_relat_1(A_23,B_24))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_247,plain,(
    ! [A_52] :
      ( k1_relat_1(A_52) != k1_xboole_0
      | k1_xboole_0 = A_52
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_254,plain,(
    ! [A_23,B_24] :
      ( k1_relat_1(k7_relat_1(A_23,B_24)) != k1_xboole_0
      | k7_relat_1(A_23,B_24) = k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(resolution,[status(thm)],[c_28,c_247])).

tff(c_4988,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4881,c_254])).

tff(c_5021,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4988])).

tff(c_5023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_5021])).

tff(c_5025,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5205,plain,(
    ! [A_251,B_252] : k4_xboole_0(A_251,k4_xboole_0(A_251,B_252)) = k3_xboole_0(A_251,B_252) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5058,plain,(
    ! [A_228,B_229] :
      ( k4_xboole_0(A_228,B_229) = A_228
      | ~ r1_xboole_0(A_228,B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5069,plain,(
    ! [B_13,A_12] : k4_xboole_0(B_13,k4_xboole_0(A_12,B_13)) = B_13 ),
    inference(resolution,[status(thm)],[c_66,c_5058])).

tff(c_5224,plain,(
    ! [B_252] : k3_xboole_0(B_252,B_252) = B_252 ),
    inference(superposition,[status(thm),theory(equality)],[c_5205,c_5069])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5841,plain,(
    ! [A_293,B_294] :
      ( k4_xboole_0(A_293,B_294) = A_293
      | k3_xboole_0(A_293,B_294) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_5058])).

tff(c_5230,plain,(
    ! [A_251,B_252] : r1_xboole_0(k3_xboole_0(A_251,B_252),k4_xboole_0(A_251,B_252)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5205,c_16])).

tff(c_6553,plain,(
    ! [A_322,B_323] :
      ( r1_xboole_0(k3_xboole_0(A_322,B_323),A_322)
      | k3_xboole_0(A_322,B_323) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5841,c_5230])).

tff(c_6578,plain,(
    ! [B_252] :
      ( r1_xboole_0(B_252,B_252)
      | k3_xboole_0(B_252,B_252) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5224,c_6553])).

tff(c_6603,plain,(
    ! [B_324] :
      ( r1_xboole_0(B_324,B_324)
      | k1_xboole_0 != B_324 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5224,c_6578])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6620,plain,(
    ! [C_9] : ~ r2_hidden(C_9,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6603,c_8])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5024,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5740,plain,(
    ! [A_288,C_289,B_290] :
      ( r2_hidden(A_288,k1_relat_1(k7_relat_1(C_289,B_290)))
      | ~ r2_hidden(A_288,k1_relat_1(C_289))
      | ~ r2_hidden(A_288,B_290)
      | ~ v1_relat_1(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5749,plain,(
    ! [A_288] :
      ( r2_hidden(A_288,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_288,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_288,'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5024,c_5740])).

tff(c_6295,plain,(
    ! [A_311] :
      ( r2_hidden(A_311,k1_xboole_0)
      | ~ r2_hidden(A_311,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_311,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32,c_5749])).

tff(c_6309,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_6),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_6),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_6295])).

tff(c_7142,plain,(
    ! [B_340] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_340),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_340) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6620,c_6309])).

tff(c_7146,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_7142])).

tff(c_7150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5025,c_5025,c_7146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:17:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.52/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.08  
% 5.52/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.09  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.52/2.09  
% 5.52/2.09  %Foreground sorts:
% 5.52/2.09  
% 5.52/2.09  
% 5.52/2.09  %Background operators:
% 5.52/2.09  
% 5.52/2.09  
% 5.52/2.09  %Foreground operators:
% 5.52/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.52/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.52/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.52/2.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.52/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.52/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.52/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.52/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.52/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.52/2.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.52/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.52/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.52/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.52/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.52/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.52/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.52/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.52/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.52/2.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.52/2.09  
% 5.52/2.10  tff(f_95, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 5.52/2.10  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.52/2.10  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 5.52/2.10  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.52/2.10  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.52/2.10  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.52/2.10  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.52/2.10  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.52/2.10  tff(f_69, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.52/2.10  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.52/2.10  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.52/2.10  tff(c_52, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.52/2.10  tff(c_85, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 5.52/2.10  tff(c_46, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.52/2.10  tff(c_180, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46])).
% 5.52/2.10  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.52/2.10  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.52/2.10  tff(c_805, plain, (![A_90, B_91, C_92]: (r2_hidden(A_90, B_91) | ~r2_hidden(A_90, k1_relat_1(k7_relat_1(C_92, B_91))) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.52/2.10  tff(c_815, plain, (![C_92, B_91, B_6]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_92, B_91)), B_6), B_91) | ~v1_relat_1(C_92) | r1_xboole_0(k1_relat_1(k7_relat_1(C_92, B_91)), B_6))), inference(resolution, [status(thm)], [c_12, c_805])).
% 5.52/2.10  tff(c_1385, plain, (![A_112, C_113, B_114]: (r2_hidden(A_112, k1_relat_1(C_113)) | ~r2_hidden(A_112, k1_relat_1(k7_relat_1(C_113, B_114))) | ~v1_relat_1(C_113))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.52/2.10  tff(c_4046, plain, (![C_206, B_207, B_208]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_206, B_207)), B_208), k1_relat_1(C_206)) | ~v1_relat_1(C_206) | r1_xboole_0(k1_relat_1(k7_relat_1(C_206, B_207)), B_208))), inference(resolution, [status(thm)], [c_12, c_1385])).
% 5.52/2.10  tff(c_459, plain, (![A_72, B_73, C_74]: (~r1_xboole_0(A_72, B_73) | ~r2_hidden(C_74, B_73) | ~r2_hidden(C_74, A_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.52/2.10  tff(c_486, plain, (![C_74]: (~r2_hidden(C_74, '#skF_2') | ~r2_hidden(C_74, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_85, c_459])).
% 5.52/2.10  tff(c_4065, plain, (![B_207, B_208]: (~r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_3', B_207)), B_208), '#skF_2') | ~v1_relat_1('#skF_3') | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', B_207)), B_208))), inference(resolution, [status(thm)], [c_4046, c_486])).
% 5.52/2.10  tff(c_4298, plain, (![B_215, B_216]: (~r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_3', B_215)), B_216), '#skF_2') | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', B_215)), B_216))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4065])).
% 5.52/2.10  tff(c_4313, plain, (![B_6]: (~v1_relat_1('#skF_3') | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), B_6))), inference(resolution, [status(thm)], [c_815, c_4298])).
% 5.52/2.10  tff(c_4589, plain, (![B_219]: (r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), B_219))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4313])).
% 5.52/2.10  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.52/2.10  tff(c_4807, plain, (![B_226]: (k3_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), B_226)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4589, c_2])).
% 5.52/2.10  tff(c_304, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.52/2.10  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.52/2.10  tff(c_63, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.52/2.10  tff(c_66, plain, (![B_13, A_12]: (r1_xboole_0(B_13, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_16, c_63])).
% 5.52/2.10  tff(c_93, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=A_41 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/2.10  tff(c_112, plain, (![B_13, A_12]: (k4_xboole_0(B_13, k4_xboole_0(A_12, B_13))=B_13)), inference(resolution, [status(thm)], [c_66, c_93])).
% 5.52/2.10  tff(c_323, plain, (![B_64]: (k3_xboole_0(B_64, B_64)=B_64)), inference(superposition, [status(thm), theory('equality')], [c_304, c_112])).
% 5.52/2.10  tff(c_4881, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4807, c_323])).
% 5.52/2.10  tff(c_28, plain, (![A_23, B_24]: (v1_relat_1(k7_relat_1(A_23, B_24)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.52/2.10  tff(c_247, plain, (![A_52]: (k1_relat_1(A_52)!=k1_xboole_0 | k1_xboole_0=A_52 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.52/2.10  tff(c_254, plain, (![A_23, B_24]: (k1_relat_1(k7_relat_1(A_23, B_24))!=k1_xboole_0 | k7_relat_1(A_23, B_24)=k1_xboole_0 | ~v1_relat_1(A_23))), inference(resolution, [status(thm)], [c_28, c_247])).
% 5.52/2.10  tff(c_4988, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4881, c_254])).
% 5.52/2.10  tff(c_5021, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4988])).
% 5.52/2.10  tff(c_5023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_5021])).
% 5.52/2.10  tff(c_5025, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 5.52/2.10  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.52/2.10  tff(c_5205, plain, (![A_251, B_252]: (k4_xboole_0(A_251, k4_xboole_0(A_251, B_252))=k3_xboole_0(A_251, B_252))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.52/2.10  tff(c_5058, plain, (![A_228, B_229]: (k4_xboole_0(A_228, B_229)=A_228 | ~r1_xboole_0(A_228, B_229))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/2.10  tff(c_5069, plain, (![B_13, A_12]: (k4_xboole_0(B_13, k4_xboole_0(A_12, B_13))=B_13)), inference(resolution, [status(thm)], [c_66, c_5058])).
% 5.52/2.10  tff(c_5224, plain, (![B_252]: (k3_xboole_0(B_252, B_252)=B_252)), inference(superposition, [status(thm), theory('equality')], [c_5205, c_5069])).
% 5.52/2.10  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.52/2.10  tff(c_5841, plain, (![A_293, B_294]: (k4_xboole_0(A_293, B_294)=A_293 | k3_xboole_0(A_293, B_294)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_5058])).
% 5.52/2.10  tff(c_5230, plain, (![A_251, B_252]: (r1_xboole_0(k3_xboole_0(A_251, B_252), k4_xboole_0(A_251, B_252)))), inference(superposition, [status(thm), theory('equality')], [c_5205, c_16])).
% 5.52/2.10  tff(c_6553, plain, (![A_322, B_323]: (r1_xboole_0(k3_xboole_0(A_322, B_323), A_322) | k3_xboole_0(A_322, B_323)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5841, c_5230])).
% 5.52/2.10  tff(c_6578, plain, (![B_252]: (r1_xboole_0(B_252, B_252) | k3_xboole_0(B_252, B_252)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5224, c_6553])).
% 5.52/2.10  tff(c_6603, plain, (![B_324]: (r1_xboole_0(B_324, B_324) | k1_xboole_0!=B_324)), inference(demodulation, [status(thm), theory('equality')], [c_5224, c_6578])).
% 5.52/2.10  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.52/2.10  tff(c_6620, plain, (![C_9]: (~r2_hidden(C_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_6603, c_8])).
% 5.52/2.10  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.52/2.10  tff(c_5024, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 5.52/2.10  tff(c_5740, plain, (![A_288, C_289, B_290]: (r2_hidden(A_288, k1_relat_1(k7_relat_1(C_289, B_290))) | ~r2_hidden(A_288, k1_relat_1(C_289)) | ~r2_hidden(A_288, B_290) | ~v1_relat_1(C_289))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.52/2.10  tff(c_5749, plain, (![A_288]: (r2_hidden(A_288, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_288, k1_relat_1('#skF_3')) | ~r2_hidden(A_288, '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5024, c_5740])).
% 5.52/2.10  tff(c_6295, plain, (![A_311]: (r2_hidden(A_311, k1_xboole_0) | ~r2_hidden(A_311, k1_relat_1('#skF_3')) | ~r2_hidden(A_311, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_32, c_5749])).
% 5.52/2.10  tff(c_6309, plain, (![B_6]: (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_6), k1_xboole_0) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_6), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_6))), inference(resolution, [status(thm)], [c_12, c_6295])).
% 5.52/2.10  tff(c_7142, plain, (![B_340]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_340), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_340))), inference(negUnitSimplification, [status(thm)], [c_6620, c_6309])).
% 5.52/2.10  tff(c_7146, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_10, c_7142])).
% 5.52/2.10  tff(c_7150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5025, c_5025, c_7146])).
% 5.52/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.10  
% 5.52/2.10  Inference rules
% 5.52/2.10  ----------------------
% 5.52/2.10  #Ref     : 0
% 5.52/2.10  #Sup     : 1717
% 5.52/2.10  #Fact    : 0
% 5.52/2.10  #Define  : 0
% 5.52/2.10  #Split   : 5
% 5.52/2.10  #Chain   : 0
% 5.52/2.10  #Close   : 0
% 5.52/2.10  
% 5.52/2.10  Ordering : KBO
% 5.52/2.10  
% 5.52/2.10  Simplification rules
% 5.52/2.10  ----------------------
% 5.52/2.10  #Subsume      : 243
% 5.52/2.10  #Demod        : 1158
% 5.52/2.10  #Tautology    : 1072
% 5.52/2.10  #SimpNegUnit  : 40
% 5.52/2.10  #BackRed      : 9
% 5.52/2.10  
% 5.52/2.10  #Partial instantiations: 0
% 5.52/2.10  #Strategies tried      : 1
% 5.52/2.10  
% 5.52/2.10  Timing (in seconds)
% 5.52/2.10  ----------------------
% 5.52/2.10  Preprocessing        : 0.33
% 5.52/2.10  Parsing              : 0.18
% 5.52/2.10  CNF conversion       : 0.02
% 5.52/2.10  Main loop            : 1.00
% 5.52/2.10  Inferencing          : 0.35
% 5.52/2.11  Reduction            : 0.35
% 5.52/2.11  Demodulation         : 0.26
% 5.52/2.11  BG Simplification    : 0.04
% 5.52/2.11  Subsumption          : 0.18
% 5.52/2.11  Abstraction          : 0.05
% 5.52/2.11  MUC search           : 0.00
% 5.52/2.11  Cooper               : 0.00
% 5.52/2.11  Total                : 1.37
% 5.52/2.11  Index Insertion      : 0.00
% 5.52/2.11  Index Deletion       : 0.00
% 5.52/2.11  Index Matching       : 0.00
% 5.52/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
