%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:16 EST 2020

% Result     : Theorem 15.77s
% Output     : CNFRefutation 15.91s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 397 expanded)
%              Number of leaves         :   29 ( 145 expanded)
%              Depth                    :   17
%              Number of atoms          :  162 ( 769 expanded)
%              Number of equality atoms :   54 ( 231 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_68,axiom,(
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

tff(f_70,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(c_48,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_5'(A_17,B_18),A_17)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_5'(A_17,B_18),B_18)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_170,plain,(
    ! [D_55,B_56,A_57] :
      ( ~ r2_hidden(D_55,B_56)
      | ~ r2_hidden(D_55,k4_xboole_0(A_57,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_203,plain,(
    ! [D_60,A_61] :
      ( ~ r2_hidden(D_60,k1_xboole_0)
      | ~ r2_hidden(D_60,A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_170])).

tff(c_529,plain,(
    ! [A_84,A_85] :
      ( ~ r2_hidden('#skF_5'(A_84,k1_xboole_0),A_85)
      | r1_xboole_0(A_84,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_46,c_203])).

tff(c_573,plain,(
    ! [A_89] : r1_xboole_0(A_89,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_529])).

tff(c_40,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = k1_xboole_0
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_580,plain,(
    ! [A_89] : k3_xboole_0(A_89,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_573,c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_584,plain,(
    ! [A_90] : k3_xboole_0(A_90,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_573,c_40])).

tff(c_631,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_584])).

tff(c_54,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_241,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_247,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,k3_xboole_0(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_54])).

tff(c_311,plain,(
    ! [A_70,B_71] : k3_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_247])).

tff(c_338,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_311])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k3_xboole_0(A_3,B_4))
      | ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_139,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(k1_tarski(A_45),B_46)
      | r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_66,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_147,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_139,c_66])).

tff(c_42,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k3_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_403,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,B_78)
      | ~ r2_hidden(C_79,A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1495,plain,(
    ! [C_140,B_141,A_142] :
      ( ~ r2_hidden(C_140,B_141)
      | ~ r2_hidden(C_140,A_142)
      | k3_xboole_0(A_142,B_141) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_403])).

tff(c_1538,plain,(
    ! [A_143] :
      ( ~ r2_hidden('#skF_6',A_143)
      | k3_xboole_0(A_143,'#skF_7') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_147,c_1495])).

tff(c_1550,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(k3_xboole_0(A_3,B_4),'#skF_7') != k1_xboole_0
      | ~ r2_hidden('#skF_6',B_4)
      | ~ r2_hidden('#skF_6',A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_1538])).

tff(c_2313,plain,(
    ! [A_167,B_168] :
      ( k3_xboole_0('#skF_7',k3_xboole_0(A_167,B_168)) != k1_xboole_0
      | ~ r2_hidden('#skF_6',B_168)
      | ~ r2_hidden('#skF_6',A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1550])).

tff(c_52420,plain,(
    ! [A_968,B_969] :
      ( k3_xboole_0('#skF_7',k3_xboole_0(A_968,B_969)) != k1_xboole_0
      | ~ r2_hidden('#skF_6',k3_xboole_0(B_969,A_968))
      | ~ r2_hidden('#skF_6',A_968) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_2313])).

tff(c_52459,plain,(
    ! [A_89] :
      ( k3_xboole_0('#skF_7',k3_xboole_0(k1_xboole_0,A_89)) != k1_xboole_0
      | ~ r2_hidden('#skF_6',k1_xboole_0)
      | ~ r2_hidden('#skF_6',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_52420])).

tff(c_52492,plain,(
    ~ r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_631,c_52459])).

tff(c_64,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_67,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_410,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(k1_tarski(A_80),B_81) = k1_xboole_0
      | r2_hidden(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_139,c_40])).

tff(c_267,plain,(
    ! [A_63,B_64] : k3_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_247])).

tff(c_50917,plain,(
    ! [A_965,B_966] :
      ( k3_xboole_0(k1_tarski(A_965),B_966) = k1_xboole_0
      | r2_hidden(A_965,k3_xboole_0(k1_tarski(A_965),B_966)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_267])).

tff(c_52,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_179,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_182,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,k4_xboole_0(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_54])).

tff(c_1576,plain,(
    ! [A_58,B_59] : k3_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_182])).

tff(c_22,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,k4_xboole_0(A_9,B_10))
      | r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1546,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(k4_xboole_0(A_9,B_10),'#skF_7') != k1_xboole_0
      | r2_hidden('#skF_6',B_10)
      | ~ r2_hidden('#skF_6',A_9) ) ),
    inference(resolution,[status(thm)],[c_22,c_1538])).

tff(c_1742,plain,(
    ! [A_151,B_152] :
      ( k3_xboole_0('#skF_7',k4_xboole_0(A_151,B_152)) != k1_xboole_0
      | r2_hidden('#skF_6',B_152)
      | ~ r2_hidden('#skF_6',A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1546])).

tff(c_1749,plain,(
    ! [B_59] :
      ( k4_xboole_0('#skF_7',B_59) != k1_xboole_0
      | r2_hidden('#skF_6',B_59)
      | ~ r2_hidden('#skF_6','#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1576,c_1742])).

tff(c_1970,plain,(
    ! [B_157] :
      ( k4_xboole_0('#skF_7',B_157) != k1_xboole_0
      | r2_hidden('#skF_6',B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1749])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3675,plain,(
    ! [B_195,A_196] :
      ( ~ r2_hidden('#skF_6',B_195)
      | k4_xboole_0('#skF_7',k4_xboole_0(A_196,B_195)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1970,c_24])).

tff(c_3715,plain,(
    ! [A_22] :
      ( ~ r2_hidden('#skF_6',k1_xboole_0)
      | k4_xboole_0('#skF_7',A_22) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_3675])).

tff(c_3722,plain,(
    ~ r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3715])).

tff(c_4019,plain,(
    ! [A_206,A_207,B_208] :
      ( ~ r2_hidden('#skF_5'(A_206,k4_xboole_0(A_207,B_208)),B_208)
      | r1_xboole_0(A_206,k4_xboole_0(A_207,B_208)) ) ),
    inference(resolution,[status(thm)],[c_46,c_170])).

tff(c_4081,plain,(
    ! [A_209,A_210] : r1_xboole_0(A_209,k4_xboole_0(A_210,A_209)) ),
    inference(resolution,[status(thm)],[c_48,c_4019])).

tff(c_4132,plain,(
    ! [A_211,A_212] : k3_xboole_0(A_211,k4_xboole_0(A_212,A_211)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4081,c_40])).

tff(c_4206,plain,(
    ! [A_211,A_212] : k4_xboole_0(A_211,k4_xboole_0(A_212,A_211)) = k4_xboole_0(A_211,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4132,c_52])).

tff(c_4282,plain,(
    ! [A_211,A_212] : k4_xboole_0(A_211,k4_xboole_0(A_212,A_211)) = A_211 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4206])).

tff(c_155,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_5'(A_50,B_51),B_51)
      | r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_160,plain,(
    ! [A_50,A_3,B_4] :
      ( r2_hidden('#skF_5'(A_50,k3_xboole_0(A_3,B_4)),B_4)
      | r1_xboole_0(A_50,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_155,c_6])).

tff(c_286,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_5'(A_68,B_69),A_68)
      | r1_xboole_0(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6623,plain,(
    ! [A_265,B_266,B_267] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_265,B_266),B_267),B_266)
      | r1_xboole_0(k4_xboole_0(A_265,B_266),B_267) ) ),
    inference(resolution,[status(thm)],[c_286,c_24])).

tff(c_6836,plain,(
    ! [A_271,B_272,A_273] : r1_xboole_0(k4_xboole_0(A_271,B_272),k3_xboole_0(A_273,B_272)) ),
    inference(resolution,[status(thm)],[c_160,c_6623])).

tff(c_8581,plain,(
    ! [A_307,B_308,A_309] : k3_xboole_0(k4_xboole_0(A_307,B_308),k3_xboole_0(A_309,B_308)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6836,c_40])).

tff(c_9975,plain,(
    ! [A_321,B_322,A_323] : k3_xboole_0(k3_xboole_0(A_321,B_322),k4_xboole_0(A_323,B_322)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8581,c_2])).

tff(c_10141,plain,(
    ! [A_321,A_212,A_211] : k3_xboole_0(k3_xboole_0(A_321,k4_xboole_0(A_212,A_211)),A_211) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4282,c_9975])).

tff(c_640,plain,(
    ! [D_91,A_92,B_93] :
      ( r2_hidden(D_91,k4_xboole_0(A_92,B_93))
      | r2_hidden(D_91,B_93)
      | ~ r2_hidden(D_91,A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_652,plain,(
    ! [D_91,A_23,B_24] :
      ( r2_hidden(D_91,k4_xboole_0(A_23,B_24))
      | r2_hidden(D_91,k3_xboole_0(A_23,B_24))
      | ~ r2_hidden(D_91,A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_640])).

tff(c_161,plain,(
    ! [D_52,A_53,B_54] :
      ( r2_hidden(D_52,A_53)
      | ~ r2_hidden(D_52,k4_xboole_0(A_53,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_169,plain,(
    ! [A_17,A_53,B_54] :
      ( r2_hidden('#skF_5'(A_17,k4_xboole_0(A_53,B_54)),A_53)
      | r1_xboole_0(A_17,k4_xboole_0(A_53,B_54)) ) ),
    inference(resolution,[status(thm)],[c_46,c_161])).

tff(c_6963,plain,(
    ! [A_274,A_275,B_276] : r1_xboole_0(k4_xboole_0(A_274,A_275),k4_xboole_0(A_275,B_276)) ),
    inference(resolution,[status(thm)],[c_169,c_6623])).

tff(c_9052,plain,(
    ! [A_313,A_314,B_315] : k3_xboole_0(k4_xboole_0(A_313,A_314),k4_xboole_0(A_314,B_315)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6963,c_40])).

tff(c_10897,plain,(
    ! [A_333,A_334,B_335] : k3_xboole_0(A_333,k4_xboole_0(k4_xboole_0(A_334,A_333),B_335)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4282,c_9052])).

tff(c_1557,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0('#skF_7',k4_xboole_0(A_9,B_10)) != k1_xboole_0
      | r2_hidden('#skF_6',B_10)
      | ~ r2_hidden('#skF_6',A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1546])).

tff(c_11190,plain,(
    ! [B_335,A_334] :
      ( r2_hidden('#skF_6',B_335)
      | ~ r2_hidden('#skF_6',k4_xboole_0(A_334,'#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10897,c_1557])).

tff(c_11664,plain,(
    ! [A_341] : ~ r2_hidden('#skF_6',k4_xboole_0(A_341,'#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_11190])).

tff(c_15175,plain,(
    ! [A_390] :
      ( r2_hidden('#skF_6',k3_xboole_0(A_390,'#skF_7'))
      | ~ r2_hidden('#skF_6',A_390) ) ),
    inference(resolution,[status(thm)],[c_652,c_11664])).

tff(c_15207,plain,(
    ! [A_321,A_212] :
      ( r2_hidden('#skF_6',k1_xboole_0)
      | ~ r2_hidden('#skF_6',k3_xboole_0(A_321,k4_xboole_0(A_212,'#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10141,c_15175])).

tff(c_15272,plain,(
    ! [A_321,A_212] : ~ r2_hidden('#skF_6',k3_xboole_0(A_321,k4_xboole_0(A_212,'#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3722,c_15207])).

tff(c_51047,plain,(
    ! [A_967] : k3_xboole_0(k1_tarski('#skF_6'),k4_xboole_0(A_967,'#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50917,c_15272])).

tff(c_51463,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_51047,c_1576])).

tff(c_52194,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_51463,c_54])).

tff(c_52380,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2,c_52194])).

tff(c_52382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_52380])).

tff(c_52383,plain,(
    ! [B_335] : r2_hidden('#skF_6',B_335) ),
    inference(splitRight,[status(thm)],[c_11190])).

tff(c_52417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52383,c_3722])).

tff(c_52419,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3715])).

tff(c_52501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52492,c_52419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.77/8.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.77/8.01  
% 15.77/8.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.77/8.01  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5
% 15.77/8.01  
% 15.77/8.01  %Foreground sorts:
% 15.77/8.01  
% 15.77/8.01  
% 15.77/8.01  %Background operators:
% 15.77/8.01  
% 15.77/8.01  
% 15.77/8.01  %Foreground operators:
% 15.77/8.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.77/8.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.77/8.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.77/8.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.77/8.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.77/8.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.77/8.01  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 15.77/8.01  tff('#skF_7', type, '#skF_7': $i).
% 15.77/8.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.77/8.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.77/8.01  tff('#skF_6', type, '#skF_6': $i).
% 15.77/8.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.77/8.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.77/8.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.77/8.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.77/8.01  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.77/8.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.77/8.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.77/8.01  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 15.77/8.01  
% 15.91/8.03  tff(f_68, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 15.91/8.03  tff(f_70, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 15.91/8.03  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 15.91/8.03  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.91/8.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.91/8.03  tff(f_74, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.91/8.03  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 15.91/8.03  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 15.91/8.03  tff(f_85, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 15.91/8.03  tff(f_90, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 15.91/8.03  tff(c_48, plain, (![A_17, B_18]: (r2_hidden('#skF_5'(A_17, B_18), A_17) | r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.91/8.03  tff(c_46, plain, (![A_17, B_18]: (r2_hidden('#skF_5'(A_17, B_18), B_18) | r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.91/8.03  tff(c_50, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.91/8.03  tff(c_170, plain, (![D_55, B_56, A_57]: (~r2_hidden(D_55, B_56) | ~r2_hidden(D_55, k4_xboole_0(A_57, B_56)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.91/8.03  tff(c_203, plain, (![D_60, A_61]: (~r2_hidden(D_60, k1_xboole_0) | ~r2_hidden(D_60, A_61))), inference(superposition, [status(thm), theory('equality')], [c_50, c_170])).
% 15.91/8.03  tff(c_529, plain, (![A_84, A_85]: (~r2_hidden('#skF_5'(A_84, k1_xboole_0), A_85) | r1_xboole_0(A_84, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_203])).
% 15.91/8.03  tff(c_573, plain, (![A_89]: (r1_xboole_0(A_89, k1_xboole_0))), inference(resolution, [status(thm)], [c_48, c_529])).
% 15.91/8.03  tff(c_40, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=k1_xboole_0 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.91/8.03  tff(c_580, plain, (![A_89]: (k3_xboole_0(A_89, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_573, c_40])).
% 15.91/8.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.91/8.03  tff(c_584, plain, (![A_90]: (k3_xboole_0(A_90, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_573, c_40])).
% 15.91/8.03  tff(c_631, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_584])).
% 15.91/8.03  tff(c_54, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.91/8.03  tff(c_241, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.91/8.03  tff(c_247, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, k3_xboole_0(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_241, c_54])).
% 15.91/8.03  tff(c_311, plain, (![A_70, B_71]: (k3_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_247])).
% 15.91/8.03  tff(c_338, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k3_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_311])).
% 15.91/8.03  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k3_xboole_0(A_3, B_4)) | ~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.91/8.03  tff(c_139, plain, (![A_45, B_46]: (r1_xboole_0(k1_tarski(A_45), B_46) | r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.91/8.03  tff(c_66, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.91/8.03  tff(c_147, plain, (r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_139, c_66])).
% 15.91/8.03  tff(c_42, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k3_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.91/8.03  tff(c_403, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, B_78) | ~r2_hidden(C_79, A_77))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.91/8.03  tff(c_1495, plain, (![C_140, B_141, A_142]: (~r2_hidden(C_140, B_141) | ~r2_hidden(C_140, A_142) | k3_xboole_0(A_142, B_141)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_403])).
% 15.91/8.03  tff(c_1538, plain, (![A_143]: (~r2_hidden('#skF_6', A_143) | k3_xboole_0(A_143, '#skF_7')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_147, c_1495])).
% 15.91/8.03  tff(c_1550, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), '#skF_7')!=k1_xboole_0 | ~r2_hidden('#skF_6', B_4) | ~r2_hidden('#skF_6', A_3))), inference(resolution, [status(thm)], [c_4, c_1538])).
% 15.91/8.03  tff(c_2313, plain, (![A_167, B_168]: (k3_xboole_0('#skF_7', k3_xboole_0(A_167, B_168))!=k1_xboole_0 | ~r2_hidden('#skF_6', B_168) | ~r2_hidden('#skF_6', A_167))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1550])).
% 15.91/8.03  tff(c_52420, plain, (![A_968, B_969]: (k3_xboole_0('#skF_7', k3_xboole_0(A_968, B_969))!=k1_xboole_0 | ~r2_hidden('#skF_6', k3_xboole_0(B_969, A_968)) | ~r2_hidden('#skF_6', A_968))), inference(superposition, [status(thm), theory('equality')], [c_338, c_2313])).
% 15.91/8.03  tff(c_52459, plain, (![A_89]: (k3_xboole_0('#skF_7', k3_xboole_0(k1_xboole_0, A_89))!=k1_xboole_0 | ~r2_hidden('#skF_6', k1_xboole_0) | ~r2_hidden('#skF_6', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_580, c_52420])).
% 15.91/8.03  tff(c_52492, plain, (~r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_580, c_631, c_52459])).
% 15.91/8.03  tff(c_64, plain, (k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.91/8.03  tff(c_67, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_64])).
% 15.91/8.03  tff(c_410, plain, (![A_80, B_81]: (k3_xboole_0(k1_tarski(A_80), B_81)=k1_xboole_0 | r2_hidden(A_80, B_81))), inference(resolution, [status(thm)], [c_139, c_40])).
% 15.91/8.03  tff(c_267, plain, (![A_63, B_64]: (k3_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_247])).
% 15.91/8.03  tff(c_50917, plain, (![A_965, B_966]: (k3_xboole_0(k1_tarski(A_965), B_966)=k1_xboole_0 | r2_hidden(A_965, k3_xboole_0(k1_tarski(A_965), B_966)))), inference(superposition, [status(thm), theory('equality')], [c_410, c_267])).
% 15.91/8.03  tff(c_52, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.91/8.03  tff(c_179, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.91/8.03  tff(c_182, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k3_xboole_0(A_58, k4_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_54])).
% 15.91/8.03  tff(c_1576, plain, (![A_58, B_59]: (k3_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_182])).
% 15.91/8.03  tff(c_22, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, k4_xboole_0(A_9, B_10)) | r2_hidden(D_14, B_10) | ~r2_hidden(D_14, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.91/8.03  tff(c_1546, plain, (![A_9, B_10]: (k3_xboole_0(k4_xboole_0(A_9, B_10), '#skF_7')!=k1_xboole_0 | r2_hidden('#skF_6', B_10) | ~r2_hidden('#skF_6', A_9))), inference(resolution, [status(thm)], [c_22, c_1538])).
% 15.91/8.03  tff(c_1742, plain, (![A_151, B_152]: (k3_xboole_0('#skF_7', k4_xboole_0(A_151, B_152))!=k1_xboole_0 | r2_hidden('#skF_6', B_152) | ~r2_hidden('#skF_6', A_151))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1546])).
% 15.91/8.03  tff(c_1749, plain, (![B_59]: (k4_xboole_0('#skF_7', B_59)!=k1_xboole_0 | r2_hidden('#skF_6', B_59) | ~r2_hidden('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1576, c_1742])).
% 15.91/8.03  tff(c_1970, plain, (![B_157]: (k4_xboole_0('#skF_7', B_157)!=k1_xboole_0 | r2_hidden('#skF_6', B_157))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1749])).
% 15.91/8.03  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.91/8.03  tff(c_3675, plain, (![B_195, A_196]: (~r2_hidden('#skF_6', B_195) | k4_xboole_0('#skF_7', k4_xboole_0(A_196, B_195))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1970, c_24])).
% 15.91/8.03  tff(c_3715, plain, (![A_22]: (~r2_hidden('#skF_6', k1_xboole_0) | k4_xboole_0('#skF_7', A_22)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_3675])).
% 15.91/8.03  tff(c_3722, plain, (~r2_hidden('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3715])).
% 15.91/8.03  tff(c_4019, plain, (![A_206, A_207, B_208]: (~r2_hidden('#skF_5'(A_206, k4_xboole_0(A_207, B_208)), B_208) | r1_xboole_0(A_206, k4_xboole_0(A_207, B_208)))), inference(resolution, [status(thm)], [c_46, c_170])).
% 15.91/8.03  tff(c_4081, plain, (![A_209, A_210]: (r1_xboole_0(A_209, k4_xboole_0(A_210, A_209)))), inference(resolution, [status(thm)], [c_48, c_4019])).
% 15.91/8.03  tff(c_4132, plain, (![A_211, A_212]: (k3_xboole_0(A_211, k4_xboole_0(A_212, A_211))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4081, c_40])).
% 15.91/8.03  tff(c_4206, plain, (![A_211, A_212]: (k4_xboole_0(A_211, k4_xboole_0(A_212, A_211))=k4_xboole_0(A_211, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4132, c_52])).
% 15.91/8.03  tff(c_4282, plain, (![A_211, A_212]: (k4_xboole_0(A_211, k4_xboole_0(A_212, A_211))=A_211)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4206])).
% 15.91/8.03  tff(c_155, plain, (![A_50, B_51]: (r2_hidden('#skF_5'(A_50, B_51), B_51) | r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.91/8.03  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.91/8.03  tff(c_160, plain, (![A_50, A_3, B_4]: (r2_hidden('#skF_5'(A_50, k3_xboole_0(A_3, B_4)), B_4) | r1_xboole_0(A_50, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_155, c_6])).
% 15.91/8.03  tff(c_286, plain, (![A_68, B_69]: (r2_hidden('#skF_5'(A_68, B_69), A_68) | r1_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.91/8.03  tff(c_6623, plain, (![A_265, B_266, B_267]: (~r2_hidden('#skF_5'(k4_xboole_0(A_265, B_266), B_267), B_266) | r1_xboole_0(k4_xboole_0(A_265, B_266), B_267))), inference(resolution, [status(thm)], [c_286, c_24])).
% 15.91/8.03  tff(c_6836, plain, (![A_271, B_272, A_273]: (r1_xboole_0(k4_xboole_0(A_271, B_272), k3_xboole_0(A_273, B_272)))), inference(resolution, [status(thm)], [c_160, c_6623])).
% 15.91/8.03  tff(c_8581, plain, (![A_307, B_308, A_309]: (k3_xboole_0(k4_xboole_0(A_307, B_308), k3_xboole_0(A_309, B_308))=k1_xboole_0)), inference(resolution, [status(thm)], [c_6836, c_40])).
% 15.91/8.03  tff(c_9975, plain, (![A_321, B_322, A_323]: (k3_xboole_0(k3_xboole_0(A_321, B_322), k4_xboole_0(A_323, B_322))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8581, c_2])).
% 15.91/8.03  tff(c_10141, plain, (![A_321, A_212, A_211]: (k3_xboole_0(k3_xboole_0(A_321, k4_xboole_0(A_212, A_211)), A_211)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4282, c_9975])).
% 15.91/8.03  tff(c_640, plain, (![D_91, A_92, B_93]: (r2_hidden(D_91, k4_xboole_0(A_92, B_93)) | r2_hidden(D_91, B_93) | ~r2_hidden(D_91, A_92))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.91/8.03  tff(c_652, plain, (![D_91, A_23, B_24]: (r2_hidden(D_91, k4_xboole_0(A_23, B_24)) | r2_hidden(D_91, k3_xboole_0(A_23, B_24)) | ~r2_hidden(D_91, A_23))), inference(superposition, [status(thm), theory('equality')], [c_52, c_640])).
% 15.91/8.03  tff(c_161, plain, (![D_52, A_53, B_54]: (r2_hidden(D_52, A_53) | ~r2_hidden(D_52, k4_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.91/8.03  tff(c_169, plain, (![A_17, A_53, B_54]: (r2_hidden('#skF_5'(A_17, k4_xboole_0(A_53, B_54)), A_53) | r1_xboole_0(A_17, k4_xboole_0(A_53, B_54)))), inference(resolution, [status(thm)], [c_46, c_161])).
% 15.91/8.03  tff(c_6963, plain, (![A_274, A_275, B_276]: (r1_xboole_0(k4_xboole_0(A_274, A_275), k4_xboole_0(A_275, B_276)))), inference(resolution, [status(thm)], [c_169, c_6623])).
% 15.91/8.03  tff(c_9052, plain, (![A_313, A_314, B_315]: (k3_xboole_0(k4_xboole_0(A_313, A_314), k4_xboole_0(A_314, B_315))=k1_xboole_0)), inference(resolution, [status(thm)], [c_6963, c_40])).
% 15.91/8.03  tff(c_10897, plain, (![A_333, A_334, B_335]: (k3_xboole_0(A_333, k4_xboole_0(k4_xboole_0(A_334, A_333), B_335))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4282, c_9052])).
% 15.91/8.03  tff(c_1557, plain, (![A_9, B_10]: (k3_xboole_0('#skF_7', k4_xboole_0(A_9, B_10))!=k1_xboole_0 | r2_hidden('#skF_6', B_10) | ~r2_hidden('#skF_6', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1546])).
% 15.91/8.03  tff(c_11190, plain, (![B_335, A_334]: (r2_hidden('#skF_6', B_335) | ~r2_hidden('#skF_6', k4_xboole_0(A_334, '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_10897, c_1557])).
% 15.91/8.03  tff(c_11664, plain, (![A_341]: (~r2_hidden('#skF_6', k4_xboole_0(A_341, '#skF_7')))), inference(splitLeft, [status(thm)], [c_11190])).
% 15.91/8.03  tff(c_15175, plain, (![A_390]: (r2_hidden('#skF_6', k3_xboole_0(A_390, '#skF_7')) | ~r2_hidden('#skF_6', A_390))), inference(resolution, [status(thm)], [c_652, c_11664])).
% 15.91/8.03  tff(c_15207, plain, (![A_321, A_212]: (r2_hidden('#skF_6', k1_xboole_0) | ~r2_hidden('#skF_6', k3_xboole_0(A_321, k4_xboole_0(A_212, '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_10141, c_15175])).
% 15.91/8.03  tff(c_15272, plain, (![A_321, A_212]: (~r2_hidden('#skF_6', k3_xboole_0(A_321, k4_xboole_0(A_212, '#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_3722, c_15207])).
% 15.91/8.03  tff(c_51047, plain, (![A_967]: (k3_xboole_0(k1_tarski('#skF_6'), k4_xboole_0(A_967, '#skF_7'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_50917, c_15272])).
% 15.91/8.03  tff(c_51463, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_51047, c_1576])).
% 15.91/8.03  tff(c_52194, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_51463, c_54])).
% 15.91/8.03  tff(c_52380, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2, c_52194])).
% 15.91/8.03  tff(c_52382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_52380])).
% 15.91/8.03  tff(c_52383, plain, (![B_335]: (r2_hidden('#skF_6', B_335))), inference(splitRight, [status(thm)], [c_11190])).
% 15.91/8.03  tff(c_52417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52383, c_3722])).
% 15.91/8.03  tff(c_52419, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3715])).
% 15.91/8.03  tff(c_52501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52492, c_52419])).
% 15.91/8.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.91/8.03  
% 15.91/8.03  Inference rules
% 15.91/8.03  ----------------------
% 15.91/8.03  #Ref     : 0
% 15.91/8.03  #Sup     : 13102
% 15.91/8.03  #Fact    : 0
% 15.91/8.03  #Define  : 0
% 15.91/8.03  #Split   : 3
% 15.91/8.03  #Chain   : 0
% 15.91/8.03  #Close   : 0
% 15.91/8.03  
% 15.91/8.03  Ordering : KBO
% 15.91/8.03  
% 15.91/8.03  Simplification rules
% 15.91/8.03  ----------------------
% 15.91/8.03  #Subsume      : 2341
% 15.91/8.03  #Demod        : 16687
% 15.91/8.03  #Tautology    : 6715
% 15.91/8.03  #SimpNegUnit  : 104
% 15.91/8.03  #BackRed      : 16
% 15.91/8.03  
% 15.91/8.03  #Partial instantiations: 0
% 15.91/8.03  #Strategies tried      : 1
% 15.91/8.03  
% 15.91/8.03  Timing (in seconds)
% 15.91/8.03  ----------------------
% 15.91/8.03  Preprocessing        : 0.30
% 15.91/8.03  Parsing              : 0.15
% 15.91/8.03  CNF conversion       : 0.02
% 15.91/8.03  Main loop            : 6.90
% 15.91/8.03  Inferencing          : 1.11
% 15.91/8.03  Reduction            : 3.58
% 15.91/8.03  Demodulation         : 3.15
% 15.91/8.03  BG Simplification    : 0.12
% 15.91/8.03  Subsumption          : 1.73
% 15.91/8.03  Abstraction          : 0.21
% 15.91/8.03  MUC search           : 0.00
% 15.91/8.03  Cooper               : 0.00
% 15.91/8.03  Total                : 7.24
% 15.91/8.03  Index Insertion      : 0.00
% 15.91/8.03  Index Deletion       : 0.00
% 15.91/8.03  Index Matching       : 0.00
% 15.91/8.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
