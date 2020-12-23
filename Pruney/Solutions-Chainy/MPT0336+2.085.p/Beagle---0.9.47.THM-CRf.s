%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:11 EST 2020

% Result     : Theorem 13.38s
% Output     : CNFRefutation 13.52s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 155 expanded)
%              Number of leaves         :   29 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  124 ( 241 expanded)
%              Number of equality atoms :   28 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k4_xboole_0(A_20,B_21) != A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(B_36,A_37)
      | ~ r1_xboole_0(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_60])).

tff(c_1905,plain,(
    ! [A_150,C_151,B_152] :
      ( ~ r1_xboole_0(A_150,C_151)
      | ~ r1_xboole_0(A_150,B_152)
      | r1_xboole_0(A_150,k2_xboole_0(B_152,C_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6552,plain,(
    ! [B_293,C_294,A_295] :
      ( r1_xboole_0(k2_xboole_0(B_293,C_294),A_295)
      | ~ r1_xboole_0(A_295,C_294)
      | ~ r1_xboole_0(A_295,B_293) ) ),
    inference(resolution,[status(thm)],[c_1905,c_4])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6570,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6552,c_42])).

tff(c_6578,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_6570])).

tff(c_6590,plain,(
    k4_xboole_0('#skF_3','#skF_2') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_6578])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_384,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_xboole_0(A_71,k4_xboole_0(C_72,B_73))
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2623,plain,(
    ! [A_188,C_189,B_190] :
      ( k4_xboole_0(A_188,k4_xboole_0(C_189,B_190)) = A_188
      | ~ r1_tarski(A_188,B_190) ) ),
    inference(resolution,[status(thm)],[c_384,c_26])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2875,plain,(
    ! [C_193,B_194] :
      ( k3_xboole_0(C_193,B_194) = C_193
      | ~ r1_tarski(C_193,B_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_18])).

tff(c_15845,plain,(
    ! [A_523,B_524] : k3_xboole_0(k4_xboole_0(A_523,B_524),A_523) = k4_xboole_0(A_523,B_524) ),
    inference(resolution,[status(thm)],[c_16,c_2875])).

tff(c_16238,plain,(
    ! [A_1,B_524] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_524)) = k4_xboole_0(A_1,B_524) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15845])).

tff(c_168,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_171,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,k4_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_18])).

tff(c_19191,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16238,c_171])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_40,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,k1_tarski(B_32)) = A_31
      | r2_hidden(B_32,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28509,plain,(
    ! [A_636,A_637,B_638] :
      ( k4_xboole_0(A_636,A_637) = A_636
      | ~ r1_tarski(A_636,k1_tarski(B_638))
      | r2_hidden(B_638,A_637) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2623])).

tff(c_28580,plain,(
    ! [A_637] :
      ( k4_xboole_0(k3_xboole_0('#skF_3','#skF_2'),A_637) = k3_xboole_0('#skF_3','#skF_2')
      | r2_hidden('#skF_5',A_637) ) ),
    inference(resolution,[status(thm)],[c_49,c_28509])).

tff(c_2824,plain,(
    ! [A_191,B_192] :
      ( r1_tarski(A_191,A_191)
      | ~ r1_tarski(A_191,B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_16])).

tff(c_3294,plain,(
    ! [A_199,B_200] : r1_tarski(k4_xboole_0(A_199,B_200),k4_xboole_0(A_199,B_200)) ),
    inference(resolution,[status(thm)],[c_16,c_2824])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,C_12)
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3415,plain,(
    ! [A_204,B_205] : r1_xboole_0(k4_xboole_0(A_204,B_205),B_205) ),
    inference(resolution,[status(thm)],[c_3294,c_12])).

tff(c_3485,plain,(
    ! [B_206,A_207] : r1_xboole_0(B_206,k4_xboole_0(A_207,B_206)) ),
    inference(resolution,[status(thm)],[c_3415,c_4])).

tff(c_3546,plain,(
    ! [B_208,A_209] : k4_xboole_0(B_208,k4_xboole_0(A_209,B_208)) = B_208 ),
    inference(resolution,[status(thm)],[c_3485,c_26])).

tff(c_3691,plain,(
    ! [B_208] : r1_tarski(B_208,B_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_3546,c_16])).

tff(c_32005,plain,(
    ! [A_659,C_660,B_661] :
      ( k4_xboole_0(A_659,A_659) = k3_xboole_0(A_659,k4_xboole_0(C_660,B_661))
      | ~ r1_tarski(A_659,B_661) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_18])).

tff(c_177,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_16])).

tff(c_702,plain,(
    ! [A_92,B_93,C_94] :
      ( r1_tarski(A_92,B_93)
      | ~ r1_tarski(A_92,k4_xboole_0(B_93,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1267,plain,(
    ! [B_114,C_115,B_116] : r1_tarski(k3_xboole_0(k4_xboole_0(B_114,C_115),B_116),B_114) ),
    inference(resolution,[status(thm)],[c_177,c_702])).

tff(c_1323,plain,(
    ! [B_2,B_114,C_115] : r1_tarski(k3_xboole_0(B_2,k4_xboole_0(B_114,C_115)),B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1267])).

tff(c_33192,plain,(
    ! [A_664,C_665,B_666] :
      ( r1_tarski(k4_xboole_0(A_664,A_664),C_665)
      | ~ r1_tarski(A_664,B_666) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32005,c_1323])).

tff(c_33254,plain,(
    ! [B_667,C_668] : r1_tarski(k4_xboole_0(B_667,B_667),C_668) ),
    inference(resolution,[status(thm)],[c_3691,c_33192])).

tff(c_118,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_130,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_118])).

tff(c_243,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_xboole_0(A_60,C_61)
      | ~ r1_tarski(A_60,k4_xboole_0(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_274,plain,(
    ! [A_63] :
      ( r1_xboole_0(A_63,'#skF_3')
      | ~ r1_tarski(A_63,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_243])).

tff(c_286,plain,(
    ! [A_64] :
      ( r1_xboole_0('#skF_3',A_64)
      | ~ r1_tarski(A_64,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_274,c_4])).

tff(c_302,plain,(
    ! [A_64] :
      ( k4_xboole_0('#skF_3',A_64) = '#skF_3'
      | ~ r1_tarski(A_64,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_286,c_26])).

tff(c_34282,plain,(
    ! [B_688] : k4_xboole_0('#skF_3',k4_xboole_0(B_688,B_688)) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_33254,c_302])).

tff(c_34522,plain,
    ( k4_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2')) = '#skF_3'
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28580,c_34282])).

tff(c_34627,plain,
    ( k4_xboole_0('#skF_3','#skF_2') = '#skF_3'
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19191,c_34522])).

tff(c_34628,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_6590,c_34627])).

tff(c_129,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_63,c_118])).

tff(c_273,plain,(
    ! [B_62,C_61,B_14] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_62,C_61),B_14),C_61) ),
    inference(resolution,[status(thm)],[c_16,c_243])).

tff(c_1761,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r1_xboole_0(A_143,B_144)
      | ~ r2_hidden(C_145,B_144)
      | ~ r2_hidden(C_145,A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_15245,plain,(
    ! [C_517,C_518,B_519,B_520] :
      ( ~ r2_hidden(C_517,C_518)
      | ~ r2_hidden(C_517,k4_xboole_0(k4_xboole_0(B_519,C_518),B_520)) ) ),
    inference(resolution,[status(thm)],[c_273,c_1761])).

tff(c_16961,plain,(
    ! [C_528,B_529] :
      ( ~ r2_hidden(C_528,'#skF_4')
      | ~ r2_hidden(C_528,k4_xboole_0('#skF_3',B_529)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_15245])).

tff(c_17013,plain,(
    ! [C_528,B_16] :
      ( ~ r2_hidden(C_528,'#skF_4')
      | ~ r2_hidden(C_528,k3_xboole_0('#skF_3',B_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_16961])).

tff(c_34642,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34628,c_17013])).

tff(c_34659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34642])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.38/5.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.38/5.57  
% 13.38/5.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.38/5.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 13.38/5.57  
% 13.38/5.57  %Foreground sorts:
% 13.38/5.57  
% 13.38/5.57  
% 13.38/5.57  %Background operators:
% 13.38/5.57  
% 13.38/5.57  
% 13.38/5.57  %Foreground operators:
% 13.38/5.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.38/5.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.38/5.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.38/5.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.38/5.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.38/5.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.38/5.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.38/5.57  tff('#skF_5', type, '#skF_5': $i).
% 13.38/5.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.38/5.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.38/5.57  tff('#skF_2', type, '#skF_2': $i).
% 13.38/5.57  tff('#skF_3', type, '#skF_3': $i).
% 13.38/5.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.38/5.57  tff('#skF_4', type, '#skF_4': $i).
% 13.38/5.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.38/5.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.38/5.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.38/5.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.38/5.57  
% 13.52/5.59  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 13.52/5.59  tff(f_79, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.52/5.59  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 13.52/5.59  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 13.52/5.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.52/5.59  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.52/5.59  tff(f_83, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 13.52/5.59  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.52/5.59  tff(f_94, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 13.52/5.59  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 13.52/5.59  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.52/5.59  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.52/5.59  tff(c_28, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k4_xboole_0(A_20, B_21)!=A_20)), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.52/5.59  tff(c_44, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.52/5.59  tff(c_60, plain, (![B_36, A_37]: (r1_xboole_0(B_36, A_37) | ~r1_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.52/5.59  tff(c_63, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_60])).
% 13.52/5.59  tff(c_1905, plain, (![A_150, C_151, B_152]: (~r1_xboole_0(A_150, C_151) | ~r1_xboole_0(A_150, B_152) | r1_xboole_0(A_150, k2_xboole_0(B_152, C_151)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.52/5.59  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.52/5.59  tff(c_6552, plain, (![B_293, C_294, A_295]: (r1_xboole_0(k2_xboole_0(B_293, C_294), A_295) | ~r1_xboole_0(A_295, C_294) | ~r1_xboole_0(A_295, B_293))), inference(resolution, [status(thm)], [c_1905, c_4])).
% 13.52/5.59  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.52/5.59  tff(c_6570, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6552, c_42])).
% 13.52/5.59  tff(c_6578, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_6570])).
% 13.52/5.59  tff(c_6590, plain, (k4_xboole_0('#skF_3', '#skF_2')!='#skF_3'), inference(resolution, [status(thm)], [c_28, c_6578])).
% 13.52/5.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.52/5.59  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.52/5.59  tff(c_384, plain, (![A_71, C_72, B_73]: (r1_xboole_0(A_71, k4_xboole_0(C_72, B_73)) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.52/5.59  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.52/5.59  tff(c_2623, plain, (![A_188, C_189, B_190]: (k4_xboole_0(A_188, k4_xboole_0(C_189, B_190))=A_188 | ~r1_tarski(A_188, B_190))), inference(resolution, [status(thm)], [c_384, c_26])).
% 13.52/5.59  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.52/5.59  tff(c_2875, plain, (![C_193, B_194]: (k3_xboole_0(C_193, B_194)=C_193 | ~r1_tarski(C_193, B_194))), inference(superposition, [status(thm), theory('equality')], [c_2623, c_18])).
% 13.52/5.59  tff(c_15845, plain, (![A_523, B_524]: (k3_xboole_0(k4_xboole_0(A_523, B_524), A_523)=k4_xboole_0(A_523, B_524))), inference(resolution, [status(thm)], [c_16, c_2875])).
% 13.52/5.59  tff(c_16238, plain, (![A_1, B_524]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_524))=k4_xboole_0(A_1, B_524))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15845])).
% 13.52/5.59  tff(c_168, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.52/5.59  tff(c_171, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k3_xboole_0(A_51, k4_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_18])).
% 13.52/5.59  tff(c_19191, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(demodulation, [status(thm), theory('equality')], [c_16238, c_171])).
% 13.52/5.59  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.52/5.59  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 13.52/5.59  tff(c_40, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k1_tarski(B_32))=A_31 | r2_hidden(B_32, A_31))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.52/5.59  tff(c_28509, plain, (![A_636, A_637, B_638]: (k4_xboole_0(A_636, A_637)=A_636 | ~r1_tarski(A_636, k1_tarski(B_638)) | r2_hidden(B_638, A_637))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2623])).
% 13.52/5.59  tff(c_28580, plain, (![A_637]: (k4_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), A_637)=k3_xboole_0('#skF_3', '#skF_2') | r2_hidden('#skF_5', A_637))), inference(resolution, [status(thm)], [c_49, c_28509])).
% 13.52/5.59  tff(c_2824, plain, (![A_191, B_192]: (r1_tarski(A_191, A_191) | ~r1_tarski(A_191, B_192))), inference(superposition, [status(thm), theory('equality')], [c_2623, c_16])).
% 13.52/5.59  tff(c_3294, plain, (![A_199, B_200]: (r1_tarski(k4_xboole_0(A_199, B_200), k4_xboole_0(A_199, B_200)))), inference(resolution, [status(thm)], [c_16, c_2824])).
% 13.52/5.59  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, C_12) | ~r1_tarski(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.52/5.59  tff(c_3415, plain, (![A_204, B_205]: (r1_xboole_0(k4_xboole_0(A_204, B_205), B_205))), inference(resolution, [status(thm)], [c_3294, c_12])).
% 13.52/5.59  tff(c_3485, plain, (![B_206, A_207]: (r1_xboole_0(B_206, k4_xboole_0(A_207, B_206)))), inference(resolution, [status(thm)], [c_3415, c_4])).
% 13.52/5.59  tff(c_3546, plain, (![B_208, A_209]: (k4_xboole_0(B_208, k4_xboole_0(A_209, B_208))=B_208)), inference(resolution, [status(thm)], [c_3485, c_26])).
% 13.52/5.59  tff(c_3691, plain, (![B_208]: (r1_tarski(B_208, B_208))), inference(superposition, [status(thm), theory('equality')], [c_3546, c_16])).
% 13.52/5.59  tff(c_32005, plain, (![A_659, C_660, B_661]: (k4_xboole_0(A_659, A_659)=k3_xboole_0(A_659, k4_xboole_0(C_660, B_661)) | ~r1_tarski(A_659, B_661))), inference(superposition, [status(thm), theory('equality')], [c_2623, c_18])).
% 13.52/5.59  tff(c_177, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), A_51))), inference(superposition, [status(thm), theory('equality')], [c_168, c_16])).
% 13.52/5.59  tff(c_702, plain, (![A_92, B_93, C_94]: (r1_tarski(A_92, B_93) | ~r1_tarski(A_92, k4_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.52/5.59  tff(c_1267, plain, (![B_114, C_115, B_116]: (r1_tarski(k3_xboole_0(k4_xboole_0(B_114, C_115), B_116), B_114))), inference(resolution, [status(thm)], [c_177, c_702])).
% 13.52/5.59  tff(c_1323, plain, (![B_2, B_114, C_115]: (r1_tarski(k3_xboole_0(B_2, k4_xboole_0(B_114, C_115)), B_114))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1267])).
% 13.52/5.59  tff(c_33192, plain, (![A_664, C_665, B_666]: (r1_tarski(k4_xboole_0(A_664, A_664), C_665) | ~r1_tarski(A_664, B_666))), inference(superposition, [status(thm), theory('equality')], [c_32005, c_1323])).
% 13.52/5.59  tff(c_33254, plain, (![B_667, C_668]: (r1_tarski(k4_xboole_0(B_667, B_667), C_668))), inference(resolution, [status(thm)], [c_3691, c_33192])).
% 13.52/5.59  tff(c_118, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.52/5.59  tff(c_130, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_44, c_118])).
% 13.52/5.59  tff(c_243, plain, (![A_60, C_61, B_62]: (r1_xboole_0(A_60, C_61) | ~r1_tarski(A_60, k4_xboole_0(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.52/5.59  tff(c_274, plain, (![A_63]: (r1_xboole_0(A_63, '#skF_3') | ~r1_tarski(A_63, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_243])).
% 13.52/5.59  tff(c_286, plain, (![A_64]: (r1_xboole_0('#skF_3', A_64) | ~r1_tarski(A_64, '#skF_4'))), inference(resolution, [status(thm)], [c_274, c_4])).
% 13.52/5.59  tff(c_302, plain, (![A_64]: (k4_xboole_0('#skF_3', A_64)='#skF_3' | ~r1_tarski(A_64, '#skF_4'))), inference(resolution, [status(thm)], [c_286, c_26])).
% 13.52/5.59  tff(c_34282, plain, (![B_688]: (k4_xboole_0('#skF_3', k4_xboole_0(B_688, B_688))='#skF_3')), inference(resolution, [status(thm)], [c_33254, c_302])).
% 13.52/5.59  tff(c_34522, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2'))='#skF_3' | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28580, c_34282])).
% 13.52/5.59  tff(c_34627, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3' | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_19191, c_34522])).
% 13.52/5.59  tff(c_34628, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_6590, c_34627])).
% 13.52/5.59  tff(c_129, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_63, c_118])).
% 13.52/5.59  tff(c_273, plain, (![B_62, C_61, B_14]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_62, C_61), B_14), C_61))), inference(resolution, [status(thm)], [c_16, c_243])).
% 13.52/5.59  tff(c_1761, plain, (![A_143, B_144, C_145]: (~r1_xboole_0(A_143, B_144) | ~r2_hidden(C_145, B_144) | ~r2_hidden(C_145, A_143))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.52/5.59  tff(c_15245, plain, (![C_517, C_518, B_519, B_520]: (~r2_hidden(C_517, C_518) | ~r2_hidden(C_517, k4_xboole_0(k4_xboole_0(B_519, C_518), B_520)))), inference(resolution, [status(thm)], [c_273, c_1761])).
% 13.52/5.59  tff(c_16961, plain, (![C_528, B_529]: (~r2_hidden(C_528, '#skF_4') | ~r2_hidden(C_528, k4_xboole_0('#skF_3', B_529)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_15245])).
% 13.52/5.59  tff(c_17013, plain, (![C_528, B_16]: (~r2_hidden(C_528, '#skF_4') | ~r2_hidden(C_528, k3_xboole_0('#skF_3', B_16)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_16961])).
% 13.52/5.59  tff(c_34642, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34628, c_17013])).
% 13.52/5.59  tff(c_34659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_34642])).
% 13.52/5.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.52/5.59  
% 13.52/5.59  Inference rules
% 13.52/5.59  ----------------------
% 13.52/5.59  #Ref     : 0
% 13.52/5.59  #Sup     : 8524
% 13.52/5.59  #Fact    : 0
% 13.52/5.59  #Define  : 0
% 13.52/5.59  #Split   : 2
% 13.52/5.59  #Chain   : 0
% 13.52/5.59  #Close   : 0
% 13.52/5.59  
% 13.52/5.59  Ordering : KBO
% 13.52/5.59  
% 13.52/5.59  Simplification rules
% 13.52/5.59  ----------------------
% 13.52/5.59  #Subsume      : 713
% 13.52/5.59  #Demod        : 5422
% 13.52/5.59  #Tautology    : 4720
% 13.52/5.59  #SimpNegUnit  : 2
% 13.52/5.59  #BackRed      : 2
% 13.52/5.59  
% 13.52/5.59  #Partial instantiations: 0
% 13.52/5.59  #Strategies tried      : 1
% 13.52/5.59  
% 13.52/5.59  Timing (in seconds)
% 13.52/5.59  ----------------------
% 13.52/5.59  Preprocessing        : 0.32
% 13.52/5.59  Parsing              : 0.18
% 13.52/5.59  CNF conversion       : 0.02
% 13.52/5.59  Main loop            : 4.48
% 13.52/5.59  Inferencing          : 0.78
% 13.52/5.59  Reduction            : 2.25
% 13.52/5.59  Demodulation         : 1.93
% 13.52/5.59  BG Simplification    : 0.09
% 13.52/5.59  Subsumption          : 1.11
% 13.52/5.60  Abstraction          : 0.11
% 13.52/5.60  MUC search           : 0.00
% 13.52/5.60  Cooper               : 0.00
% 13.52/5.60  Total                : 4.83
% 13.52/5.60  Index Insertion      : 0.00
% 13.52/5.60  Index Deletion       : 0.00
% 13.52/5.60  Index Matching       : 0.00
% 13.52/5.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
