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
% DateTime   : Thu Dec  3 10:06:07 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :   73 (  97 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 214 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( v3_ordinal1(B)
       => ~ ( r1_tarski(A,B)
            & A != k1_xboole_0
            & ! [C] :
                ( v3_ordinal1(C)
               => ~ ( r2_hidden(C,A)
                    & ! [D] :
                        ( v3_ordinal1(D)
                       => ( r2_hidden(D,A)
                         => r1_ordinal1(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_97,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_92,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_16324,plain,(
    ! [A_1062,B_1063,C_1064] :
      ( r2_hidden('#skF_2'(A_1062,B_1063,C_1064),A_1062)
      | r2_hidden('#skF_3'(A_1062,B_1063,C_1064),C_1064)
      | k4_xboole_0(A_1062,B_1063) = C_1064 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16645,plain,(
    ! [A_1089,B_1090] :
      ( r2_hidden('#skF_3'(A_1089,B_1090,A_1089),A_1089)
      | k4_xboole_0(A_1089,B_1090) = A_1089 ) ),
    inference(resolution,[status(thm)],[c_16324,c_20])).

tff(c_30,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_144,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_4'(A_84,B_85),B_85)
      | ~ r2_hidden(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_56,plain,(
    ! [B_59,A_58] :
      ( ~ r1_tarski(B_59,A_58)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_193,plain,(
    ! [B_96,A_97] :
      ( ~ r1_tarski(B_96,'#skF_4'(A_97,B_96))
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(resolution,[status(thm)],[c_144,c_56])).

tff(c_198,plain,(
    ! [A_97] : ~ r2_hidden(A_97,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_193])).

tff(c_16696,plain,(
    ! [B_1090] : k4_xboole_0(k1_xboole_0,B_1090) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16645,c_198])).

tff(c_16416,plain,(
    ! [B_1063,C_1064] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_1063,C_1064),C_1064)
      | k4_xboole_0(k1_xboole_0,B_1063) = C_1064 ) ),
    inference(resolution,[status(thm)],[c_16324,c_198])).

tff(c_25120,plain,(
    ! [B_1063,C_1064] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_1063,C_1064),C_1064)
      | k1_xboole_0 = C_1064 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16696,c_16416])).

tff(c_62,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_60,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_48,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_4'(A_44,B_45),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_218,plain,(
    ! [C_101,B_102,A_103] :
      ( r2_hidden(C_101,B_102)
      | ~ r2_hidden(C_101,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_498,plain,(
    ! [A_148,B_149,B_150] :
      ( r2_hidden('#skF_4'(A_148,B_149),B_150)
      | ~ r1_tarski(B_149,B_150)
      | ~ r2_hidden(A_148,B_149) ) ),
    inference(resolution,[status(thm)],[c_48,c_218])).

tff(c_52,plain,(
    ! [A_53,B_54] :
      ( v3_ordinal1(A_53)
      | ~ r2_hidden(A_53,B_54)
      | ~ v3_ordinal1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_41184,plain,(
    ! [A_2485,B_2486,B_2487] :
      ( v3_ordinal1('#skF_4'(A_2485,B_2486))
      | ~ v3_ordinal1(B_2487)
      | ~ r1_tarski(B_2486,B_2487)
      | ~ r2_hidden(A_2485,B_2486) ) ),
    inference(resolution,[status(thm)],[c_498,c_52])).

tff(c_41196,plain,(
    ! [A_2485] :
      ( v3_ordinal1('#skF_4'(A_2485,'#skF_5'))
      | ~ v3_ordinal1('#skF_6')
      | ~ r2_hidden(A_2485,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_41184])).

tff(c_41204,plain,(
    ! [A_2485] :
      ( v3_ordinal1('#skF_4'(A_2485,'#skF_5'))
      | ~ r2_hidden(A_2485,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_41196])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_138,plain,(
    ! [A_82,B_83] :
      ( ~ r2_hidden('#skF_1'(A_82,B_83),B_83)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_143,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_223,plain,(
    ! [A_44,B_45,B_102] :
      ( r2_hidden('#skF_4'(A_44,B_45),B_102)
      | ~ r1_tarski(B_45,B_102)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_48,c_218])).

tff(c_68,plain,(
    ! [C_63] :
      ( v3_ordinal1('#skF_7'(C_63))
      | ~ r2_hidden(C_63,'#skF_5')
      | ~ v3_ordinal1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_66,plain,(
    ! [C_63] :
      ( r2_hidden('#skF_7'(C_63),'#skF_5')
      | ~ r2_hidden(C_63,'#skF_5')
      | ~ v3_ordinal1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_54,plain,(
    ! [B_57,A_55] :
      ( r2_hidden(B_57,A_55)
      | r1_ordinal1(A_55,B_57)
      | ~ v3_ordinal1(B_57)
      | ~ v3_ordinal1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_297,plain,(
    ! [D_117,A_118,B_119] :
      ( ~ r2_hidden(D_117,'#skF_4'(A_118,B_119))
      | ~ r2_hidden(D_117,B_119)
      | ~ r2_hidden(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_43963,plain,(
    ! [B_2614,B_2615,A_2616] :
      ( ~ r2_hidden(B_2614,B_2615)
      | ~ r2_hidden(A_2616,B_2615)
      | r1_ordinal1('#skF_4'(A_2616,B_2615),B_2614)
      | ~ v3_ordinal1(B_2614)
      | ~ v3_ordinal1('#skF_4'(A_2616,B_2615)) ) ),
    inference(resolution,[status(thm)],[c_54,c_297])).

tff(c_64,plain,(
    ! [C_63] :
      ( ~ r1_ordinal1(C_63,'#skF_7'(C_63))
      | ~ r2_hidden(C_63,'#skF_5')
      | ~ v3_ordinal1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44066,plain,(
    ! [A_2628,B_2629] :
      ( ~ r2_hidden('#skF_4'(A_2628,B_2629),'#skF_5')
      | ~ r2_hidden('#skF_7'('#skF_4'(A_2628,B_2629)),B_2629)
      | ~ r2_hidden(A_2628,B_2629)
      | ~ v3_ordinal1('#skF_7'('#skF_4'(A_2628,B_2629)))
      | ~ v3_ordinal1('#skF_4'(A_2628,B_2629)) ) ),
    inference(resolution,[status(thm)],[c_43963,c_64])).

tff(c_44422,plain,(
    ! [A_2657] :
      ( ~ r2_hidden(A_2657,'#skF_5')
      | ~ v3_ordinal1('#skF_7'('#skF_4'(A_2657,'#skF_5')))
      | ~ r2_hidden('#skF_4'(A_2657,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_4'(A_2657,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_66,c_44066])).

tff(c_44427,plain,(
    ! [A_2658] :
      ( ~ r2_hidden(A_2658,'#skF_5')
      | ~ r2_hidden('#skF_4'(A_2658,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_4'(A_2658,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_68,c_44422])).

tff(c_44431,plain,(
    ! [A_44] :
      ( ~ v3_ordinal1('#skF_4'(A_44,'#skF_5'))
      | ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden(A_44,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_223,c_44427])).

tff(c_44444,plain,(
    ! [A_2659] :
      ( ~ v3_ordinal1('#skF_4'(A_2659,'#skF_5'))
      | ~ r2_hidden(A_2659,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_44431])).

tff(c_44455,plain,(
    ! [A_2660] : ~ r2_hidden(A_2660,'#skF_5') ),
    inference(resolution,[status(thm)],[c_41204,c_44444])).

tff(c_44505,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_25120,c_44455])).

tff(c_44558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_44505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:35:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.62/5.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/5.18  
% 11.62/5.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/5.19  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.62/5.19  
% 11.62/5.19  %Foreground sorts:
% 11.62/5.19  
% 11.62/5.19  
% 11.62/5.19  %Background operators:
% 11.62/5.19  
% 11.62/5.19  
% 11.62/5.19  %Foreground operators:
% 11.62/5.19  tff('#skF_7', type, '#skF_7': $i > $i).
% 11.62/5.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.62/5.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.62/5.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.62/5.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.62/5.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.62/5.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.62/5.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.62/5.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.62/5.19  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 11.62/5.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.62/5.19  tff('#skF_5', type, '#skF_5': $i).
% 11.62/5.19  tff('#skF_6', type, '#skF_6': $i).
% 11.62/5.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.62/5.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.62/5.19  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 11.62/5.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.62/5.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.62/5.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.62/5.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.62/5.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.62/5.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.62/5.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.62/5.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.62/5.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.62/5.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.62/5.19  
% 11.62/5.20  tff(f_119, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_ordinal1)).
% 11.62/5.20  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.62/5.20  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.62/5.20  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 11.62/5.20  tff(f_97, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.62/5.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.62/5.20  tff(f_83, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 11.62/5.20  tff(f_92, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 11.62/5.20  tff(c_58, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.62/5.20  tff(c_16324, plain, (![A_1062, B_1063, C_1064]: (r2_hidden('#skF_2'(A_1062, B_1063, C_1064), A_1062) | r2_hidden('#skF_3'(A_1062, B_1063, C_1064), C_1064) | k4_xboole_0(A_1062, B_1063)=C_1064)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.62/5.20  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.62/5.20  tff(c_16645, plain, (![A_1089, B_1090]: (r2_hidden('#skF_3'(A_1089, B_1090, A_1089), A_1089) | k4_xboole_0(A_1089, B_1090)=A_1089)), inference(resolution, [status(thm)], [c_16324, c_20])).
% 11.62/5.20  tff(c_30, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.62/5.20  tff(c_144, plain, (![A_84, B_85]: (r2_hidden('#skF_4'(A_84, B_85), B_85) | ~r2_hidden(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.62/5.20  tff(c_56, plain, (![B_59, A_58]: (~r1_tarski(B_59, A_58) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.62/5.20  tff(c_193, plain, (![B_96, A_97]: (~r1_tarski(B_96, '#skF_4'(A_97, B_96)) | ~r2_hidden(A_97, B_96))), inference(resolution, [status(thm)], [c_144, c_56])).
% 11.62/5.20  tff(c_198, plain, (![A_97]: (~r2_hidden(A_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_193])).
% 11.62/5.20  tff(c_16696, plain, (![B_1090]: (k4_xboole_0(k1_xboole_0, B_1090)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16645, c_198])).
% 11.62/5.20  tff(c_16416, plain, (![B_1063, C_1064]: (r2_hidden('#skF_3'(k1_xboole_0, B_1063, C_1064), C_1064) | k4_xboole_0(k1_xboole_0, B_1063)=C_1064)), inference(resolution, [status(thm)], [c_16324, c_198])).
% 11.62/5.20  tff(c_25120, plain, (![B_1063, C_1064]: (r2_hidden('#skF_3'(k1_xboole_0, B_1063, C_1064), C_1064) | k1_xboole_0=C_1064)), inference(demodulation, [status(thm), theory('equality')], [c_16696, c_16416])).
% 11.62/5.20  tff(c_62, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.62/5.20  tff(c_60, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.62/5.20  tff(c_48, plain, (![A_44, B_45]: (r2_hidden('#skF_4'(A_44, B_45), B_45) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.62/5.20  tff(c_218, plain, (![C_101, B_102, A_103]: (r2_hidden(C_101, B_102) | ~r2_hidden(C_101, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.62/5.20  tff(c_498, plain, (![A_148, B_149, B_150]: (r2_hidden('#skF_4'(A_148, B_149), B_150) | ~r1_tarski(B_149, B_150) | ~r2_hidden(A_148, B_149))), inference(resolution, [status(thm)], [c_48, c_218])).
% 11.62/5.20  tff(c_52, plain, (![A_53, B_54]: (v3_ordinal1(A_53) | ~r2_hidden(A_53, B_54) | ~v3_ordinal1(B_54))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.62/5.20  tff(c_41184, plain, (![A_2485, B_2486, B_2487]: (v3_ordinal1('#skF_4'(A_2485, B_2486)) | ~v3_ordinal1(B_2487) | ~r1_tarski(B_2486, B_2487) | ~r2_hidden(A_2485, B_2486))), inference(resolution, [status(thm)], [c_498, c_52])).
% 11.62/5.20  tff(c_41196, plain, (![A_2485]: (v3_ordinal1('#skF_4'(A_2485, '#skF_5')) | ~v3_ordinal1('#skF_6') | ~r2_hidden(A_2485, '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_41184])).
% 11.62/5.20  tff(c_41204, plain, (![A_2485]: (v3_ordinal1('#skF_4'(A_2485, '#skF_5')) | ~r2_hidden(A_2485, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_41196])).
% 11.62/5.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.62/5.20  tff(c_138, plain, (![A_82, B_83]: (~r2_hidden('#skF_1'(A_82, B_83), B_83) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.62/5.20  tff(c_143, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_138])).
% 11.62/5.20  tff(c_223, plain, (![A_44, B_45, B_102]: (r2_hidden('#skF_4'(A_44, B_45), B_102) | ~r1_tarski(B_45, B_102) | ~r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_48, c_218])).
% 11.62/5.20  tff(c_68, plain, (![C_63]: (v3_ordinal1('#skF_7'(C_63)) | ~r2_hidden(C_63, '#skF_5') | ~v3_ordinal1(C_63))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.62/5.20  tff(c_66, plain, (![C_63]: (r2_hidden('#skF_7'(C_63), '#skF_5') | ~r2_hidden(C_63, '#skF_5') | ~v3_ordinal1(C_63))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.62/5.20  tff(c_54, plain, (![B_57, A_55]: (r2_hidden(B_57, A_55) | r1_ordinal1(A_55, B_57) | ~v3_ordinal1(B_57) | ~v3_ordinal1(A_55))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.62/5.20  tff(c_297, plain, (![D_117, A_118, B_119]: (~r2_hidden(D_117, '#skF_4'(A_118, B_119)) | ~r2_hidden(D_117, B_119) | ~r2_hidden(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.62/5.20  tff(c_43963, plain, (![B_2614, B_2615, A_2616]: (~r2_hidden(B_2614, B_2615) | ~r2_hidden(A_2616, B_2615) | r1_ordinal1('#skF_4'(A_2616, B_2615), B_2614) | ~v3_ordinal1(B_2614) | ~v3_ordinal1('#skF_4'(A_2616, B_2615)))), inference(resolution, [status(thm)], [c_54, c_297])).
% 11.62/5.20  tff(c_64, plain, (![C_63]: (~r1_ordinal1(C_63, '#skF_7'(C_63)) | ~r2_hidden(C_63, '#skF_5') | ~v3_ordinal1(C_63))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.62/5.20  tff(c_44066, plain, (![A_2628, B_2629]: (~r2_hidden('#skF_4'(A_2628, B_2629), '#skF_5') | ~r2_hidden('#skF_7'('#skF_4'(A_2628, B_2629)), B_2629) | ~r2_hidden(A_2628, B_2629) | ~v3_ordinal1('#skF_7'('#skF_4'(A_2628, B_2629))) | ~v3_ordinal1('#skF_4'(A_2628, B_2629)))), inference(resolution, [status(thm)], [c_43963, c_64])).
% 11.62/5.20  tff(c_44422, plain, (![A_2657]: (~r2_hidden(A_2657, '#skF_5') | ~v3_ordinal1('#skF_7'('#skF_4'(A_2657, '#skF_5'))) | ~r2_hidden('#skF_4'(A_2657, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_4'(A_2657, '#skF_5')))), inference(resolution, [status(thm)], [c_66, c_44066])).
% 11.62/5.20  tff(c_44427, plain, (![A_2658]: (~r2_hidden(A_2658, '#skF_5') | ~r2_hidden('#skF_4'(A_2658, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_4'(A_2658, '#skF_5')))), inference(resolution, [status(thm)], [c_68, c_44422])).
% 11.62/5.20  tff(c_44431, plain, (![A_44]: (~v3_ordinal1('#skF_4'(A_44, '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden(A_44, '#skF_5'))), inference(resolution, [status(thm)], [c_223, c_44427])).
% 11.62/5.20  tff(c_44444, plain, (![A_2659]: (~v3_ordinal1('#skF_4'(A_2659, '#skF_5')) | ~r2_hidden(A_2659, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_44431])).
% 11.62/5.20  tff(c_44455, plain, (![A_2660]: (~r2_hidden(A_2660, '#skF_5'))), inference(resolution, [status(thm)], [c_41204, c_44444])).
% 11.62/5.20  tff(c_44505, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_25120, c_44455])).
% 11.62/5.20  tff(c_44558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_44505])).
% 11.62/5.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/5.20  
% 11.62/5.20  Inference rules
% 11.62/5.20  ----------------------
% 11.62/5.20  #Ref     : 0
% 11.62/5.20  #Sup     : 10268
% 11.62/5.20  #Fact    : 0
% 11.62/5.20  #Define  : 0
% 11.62/5.20  #Split   : 17
% 11.62/5.20  #Chain   : 0
% 11.62/5.20  #Close   : 0
% 11.62/5.20  
% 11.62/5.20  Ordering : KBO
% 11.62/5.20  
% 11.62/5.20  Simplification rules
% 11.62/5.20  ----------------------
% 11.62/5.20  #Subsume      : 5822
% 11.62/5.20  #Demod        : 3195
% 11.62/5.20  #Tautology    : 1170
% 11.62/5.20  #SimpNegUnit  : 330
% 11.62/5.20  #BackRed      : 46
% 11.62/5.20  
% 11.62/5.20  #Partial instantiations: 0
% 11.62/5.20  #Strategies tried      : 1
% 11.62/5.20  
% 11.62/5.20  Timing (in seconds)
% 11.62/5.20  ----------------------
% 11.62/5.20  Preprocessing        : 0.47
% 11.62/5.20  Parsing              : 0.25
% 11.62/5.20  CNF conversion       : 0.03
% 11.62/5.20  Main loop            : 3.93
% 11.62/5.20  Inferencing          : 1.11
% 11.62/5.20  Reduction            : 1.14
% 11.62/5.20  Demodulation         : 0.75
% 11.62/5.20  BG Simplification    : 0.10
% 11.62/5.20  Subsumption          : 1.29
% 11.62/5.20  Abstraction          : 0.15
% 11.62/5.20  MUC search           : 0.00
% 11.62/5.20  Cooper               : 0.00
% 11.62/5.20  Total                : 4.42
% 11.62/5.20  Index Insertion      : 0.00
% 11.62/5.20  Index Deletion       : 0.00
% 11.62/5.20  Index Matching       : 0.00
% 11.62/5.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
