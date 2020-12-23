%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:39 EST 2020

% Result     : Theorem 10.68s
% Output     : CNFRefutation 10.68s
% Verified   : 
% Statistics : Number of formulae       :   79 (  90 expanded)
%              Number of leaves         :   41 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   81 ( 103 expanded)
%              Number of equality atoms :   37 (  43 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_94,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_96,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_98,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_100,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_enumset1(F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F,G,H,I,J] :
      ( J = k7_enumset1(A,B,C,D,E,F,G,H,I)
    <=> ! [K] :
          ( r2_hidden(K,J)
        <=> ~ ( K != A
              & K != B
              & K != C
              & K != D
              & K != E
              & K != F
              & K != G
              & K != H
              & K != I ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).

tff(f_106,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_88,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_110,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_88,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_90,plain,(
    ! [A_51,B_52,C_53] : k2_enumset1(A_51,A_51,B_52,C_53) = k1_enumset1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_92,plain,(
    ! [A_54,B_55,C_56,D_57] : k3_enumset1(A_54,A_54,B_55,C_56,D_57) = k2_enumset1(A_54,B_55,C_56,D_57) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_94,plain,(
    ! [B_59,A_58,E_62,D_61,C_60] : k4_enumset1(A_58,A_58,B_59,C_60,D_61,E_62) = k3_enumset1(A_58,B_59,C_60,D_61,E_62) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_96,plain,(
    ! [D_66,F_68,B_64,C_65,A_63,E_67] : k5_enumset1(A_63,A_63,B_64,C_65,D_66,E_67,F_68) = k4_enumset1(A_63,B_64,C_65,D_66,E_67,F_68) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_98,plain,(
    ! [B_70,F_74,G_75,E_73,D_72,C_71,A_69] : k6_enumset1(A_69,A_69,B_70,C_71,D_72,E_73,F_74,G_75) = k5_enumset1(A_69,B_70,C_71,D_72,E_73,F_74,G_75) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_82,plain,(
    ! [A_31,C_33,B_32,H_38,F_36,E_35,G_37,D_34] : k2_xboole_0(k2_enumset1(A_31,B_32,C_33,D_34),k2_enumset1(E_35,F_36,G_37,H_38)) = k6_enumset1(A_31,B_32,C_33,D_34,E_35,F_36,G_37,H_38) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1960,plain,(
    ! [B_380,H_379,C_381,G_382,D_383,E_386,A_378,I_384,F_385] : k2_xboole_0(k3_enumset1(A_378,B_380,C_381,D_383,E_386),k2_enumset1(F_385,G_382,H_379,I_384)) = k7_enumset1(A_378,B_380,C_381,D_383,E_386,F_385,G_382,H_379,I_384) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1975,plain,(
    ! [H_379,C_56,G_382,I_384,F_385,D_57,B_55,A_54] : k7_enumset1(A_54,A_54,B_55,C_56,D_57,F_385,G_382,H_379,I_384) = k2_xboole_0(k2_enumset1(A_54,B_55,C_56,D_57),k2_enumset1(F_385,G_382,H_379,I_384)) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_1960])).

tff(c_7680,plain,(
    ! [B_1107,G_1103,H_1106,A_1105,C_1104,I_1108,F_1102,D_1109] : k7_enumset1(A_1105,A_1105,B_1107,C_1104,D_1109,F_1102,G_1103,H_1106,I_1108) = k6_enumset1(A_1105,B_1107,C_1104,D_1109,F_1102,G_1103,H_1106,I_1108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1975])).

tff(c_24,plain,(
    ! [H_25,E_22,K_30,G_24,D_21,F_23,A_18,C_20,B_19] : r2_hidden(K_30,k7_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24,H_25,K_30)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8081,plain,(
    ! [C_1187,D_1186,H_1185,F_1183,A_1184,G_1188,I_1182,B_1189] : r2_hidden(I_1182,k6_enumset1(A_1184,B_1189,C_1187,D_1186,F_1183,G_1188,H_1185,I_1182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7680,c_24])).

tff(c_8107,plain,(
    ! [A_1192,E_1194,D_1193,B_1190,C_1195,G_1196,F_1191] : r2_hidden(G_1196,k5_enumset1(A_1192,B_1190,C_1195,D_1193,E_1194,F_1191,G_1196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_8081])).

tff(c_8130,plain,(
    ! [D_1202,C_1198,F_1201,A_1200,E_1197,B_1199] : r2_hidden(F_1201,k4_enumset1(A_1200,B_1199,C_1198,D_1202,E_1197,F_1201)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_8107])).

tff(c_8153,plain,(
    ! [C_1207,D_1204,B_1203,A_1205,E_1206] : r2_hidden(E_1206,k3_enumset1(A_1205,B_1203,C_1207,D_1204,E_1206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_8130])).

tff(c_8176,plain,(
    ! [D_1208,A_1209,B_1210,C_1211] : r2_hidden(D_1208,k2_enumset1(A_1209,B_1210,C_1211,D_1208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_8153])).

tff(c_8199,plain,(
    ! [C_1212,A_1213,B_1214] : r2_hidden(C_1212,k1_enumset1(A_1213,B_1214,C_1212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_8176])).

tff(c_8237,plain,(
    ! [B_1233,A_1234] : r2_hidden(B_1233,k2_tarski(A_1234,B_1233)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8199])).

tff(c_102,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_171,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(A_95,k3_tarski(B_96))
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_174,plain,(
    ! [A_95,A_78,B_79] :
      ( r1_tarski(A_95,k2_xboole_0(A_78,B_79))
      | ~ r2_hidden(A_95,k2_tarski(A_78,B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_171])).

tff(c_8261,plain,(
    ! [B_1233,A_1234] : r1_tarski(B_1233,k2_xboole_0(A_1234,B_1233)) ),
    inference(resolution,[status(thm)],[c_8237,c_174])).

tff(c_112,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_240,plain,(
    ! [A_106,B_107] :
      ( r2_xboole_0(A_106,B_107)
      | B_107 = A_106
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( ~ r2_xboole_0(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_429,plain,(
    ! [B_136,A_137] :
      ( ~ r1_tarski(B_136,A_137)
      | B_136 = A_137
      | ~ r1_tarski(A_137,B_136) ) ),
    inference(resolution,[status(thm)],[c_240,c_12])).

tff(c_440,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_xboole_0(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_112,c_429])).

tff(c_625,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_8272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8261,c_625])).

tff(c_8273,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_86,plain,(
    ! [A_48] : k2_tarski(A_48,A_48) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_221,plain,(
    ! [A_103,C_104,B_105] :
      ( r2_hidden(A_103,C_104)
      | ~ r1_tarski(k2_tarski(A_103,B_105),C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_255,plain,(
    ! [A_108,B_109,B_110] : r2_hidden(A_108,k2_xboole_0(k2_tarski(A_108,B_109),B_110)) ),
    inference(resolution,[status(thm)],[c_14,c_221])).

tff(c_262,plain,(
    ! [A_48,B_110] : r2_hidden(A_48,k2_xboole_0(k1_tarski(A_48),B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_255])).

tff(c_8279,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8273,c_262])).

tff(c_8286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_8279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.68/3.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.68/3.45  
% 10.68/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.68/3.45  %$ r2_xboole_0 > r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.68/3.45  
% 10.68/3.45  %Foreground sorts:
% 10.68/3.45  
% 10.68/3.45  
% 10.68/3.45  %Background operators:
% 10.68/3.45  
% 10.68/3.45  
% 10.68/3.45  %Foreground operators:
% 10.68/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.68/3.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.68/3.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.68/3.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.68/3.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.68/3.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.68/3.45  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.68/3.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.68/3.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.68/3.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.68/3.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.68/3.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.68/3.45  tff('#skF_3', type, '#skF_3': $i).
% 10.68/3.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.68/3.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.68/3.45  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 10.68/3.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.68/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.68/3.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.68/3.45  tff('#skF_4', type, '#skF_4': $i).
% 10.68/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.68/3.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.68/3.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.68/3.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.68/3.45  
% 10.68/3.47  tff(f_117, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 10.68/3.47  tff(f_90, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 10.68/3.47  tff(f_92, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 10.68/3.47  tff(f_94, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 10.68/3.47  tff(f_96, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 10.68/3.47  tff(f_98, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 10.68/3.47  tff(f_100, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 10.68/3.47  tff(f_84, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 10.68/3.47  tff(f_86, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_enumset1(F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 10.68/3.47  tff(f_82, axiom, (![A, B, C, D, E, F, G, H, I, J]: ((J = k7_enumset1(A, B, C, D, E, F, G, H, I)) <=> (![K]: (r2_hidden(K, J) <=> ~((((((((~(K = A) & ~(K = B)) & ~(K = C)) & ~(K = D)) & ~(K = E)) & ~(K = F)) & ~(K = G)) & ~(K = H)) & ~(K = I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 10.68/3.47  tff(f_106, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.68/3.47  tff(f_104, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 10.68/3.47  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 10.68/3.47  tff(f_41, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 10.68/3.47  tff(f_88, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.68/3.47  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.68/3.47  tff(f_112, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.68/3.47  tff(c_110, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.68/3.47  tff(c_88, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.68/3.47  tff(c_90, plain, (![A_51, B_52, C_53]: (k2_enumset1(A_51, A_51, B_52, C_53)=k1_enumset1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.68/3.47  tff(c_92, plain, (![A_54, B_55, C_56, D_57]: (k3_enumset1(A_54, A_54, B_55, C_56, D_57)=k2_enumset1(A_54, B_55, C_56, D_57))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.68/3.47  tff(c_94, plain, (![B_59, A_58, E_62, D_61, C_60]: (k4_enumset1(A_58, A_58, B_59, C_60, D_61, E_62)=k3_enumset1(A_58, B_59, C_60, D_61, E_62))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.68/3.47  tff(c_96, plain, (![D_66, F_68, B_64, C_65, A_63, E_67]: (k5_enumset1(A_63, A_63, B_64, C_65, D_66, E_67, F_68)=k4_enumset1(A_63, B_64, C_65, D_66, E_67, F_68))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.68/3.47  tff(c_98, plain, (![B_70, F_74, G_75, E_73, D_72, C_71, A_69]: (k6_enumset1(A_69, A_69, B_70, C_71, D_72, E_73, F_74, G_75)=k5_enumset1(A_69, B_70, C_71, D_72, E_73, F_74, G_75))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.68/3.47  tff(c_82, plain, (![A_31, C_33, B_32, H_38, F_36, E_35, G_37, D_34]: (k2_xboole_0(k2_enumset1(A_31, B_32, C_33, D_34), k2_enumset1(E_35, F_36, G_37, H_38))=k6_enumset1(A_31, B_32, C_33, D_34, E_35, F_36, G_37, H_38))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.68/3.47  tff(c_1960, plain, (![B_380, H_379, C_381, G_382, D_383, E_386, A_378, I_384, F_385]: (k2_xboole_0(k3_enumset1(A_378, B_380, C_381, D_383, E_386), k2_enumset1(F_385, G_382, H_379, I_384))=k7_enumset1(A_378, B_380, C_381, D_383, E_386, F_385, G_382, H_379, I_384))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.68/3.47  tff(c_1975, plain, (![H_379, C_56, G_382, I_384, F_385, D_57, B_55, A_54]: (k7_enumset1(A_54, A_54, B_55, C_56, D_57, F_385, G_382, H_379, I_384)=k2_xboole_0(k2_enumset1(A_54, B_55, C_56, D_57), k2_enumset1(F_385, G_382, H_379, I_384)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_1960])).
% 10.68/3.47  tff(c_7680, plain, (![B_1107, G_1103, H_1106, A_1105, C_1104, I_1108, F_1102, D_1109]: (k7_enumset1(A_1105, A_1105, B_1107, C_1104, D_1109, F_1102, G_1103, H_1106, I_1108)=k6_enumset1(A_1105, B_1107, C_1104, D_1109, F_1102, G_1103, H_1106, I_1108))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1975])).
% 10.68/3.47  tff(c_24, plain, (![H_25, E_22, K_30, G_24, D_21, F_23, A_18, C_20, B_19]: (r2_hidden(K_30, k7_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24, H_25, K_30)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.68/3.47  tff(c_8081, plain, (![C_1187, D_1186, H_1185, F_1183, A_1184, G_1188, I_1182, B_1189]: (r2_hidden(I_1182, k6_enumset1(A_1184, B_1189, C_1187, D_1186, F_1183, G_1188, H_1185, I_1182)))), inference(superposition, [status(thm), theory('equality')], [c_7680, c_24])).
% 10.68/3.47  tff(c_8107, plain, (![A_1192, E_1194, D_1193, B_1190, C_1195, G_1196, F_1191]: (r2_hidden(G_1196, k5_enumset1(A_1192, B_1190, C_1195, D_1193, E_1194, F_1191, G_1196)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_8081])).
% 10.68/3.47  tff(c_8130, plain, (![D_1202, C_1198, F_1201, A_1200, E_1197, B_1199]: (r2_hidden(F_1201, k4_enumset1(A_1200, B_1199, C_1198, D_1202, E_1197, F_1201)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_8107])).
% 10.68/3.47  tff(c_8153, plain, (![C_1207, D_1204, B_1203, A_1205, E_1206]: (r2_hidden(E_1206, k3_enumset1(A_1205, B_1203, C_1207, D_1204, E_1206)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_8130])).
% 10.68/3.47  tff(c_8176, plain, (![D_1208, A_1209, B_1210, C_1211]: (r2_hidden(D_1208, k2_enumset1(A_1209, B_1210, C_1211, D_1208)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_8153])).
% 10.68/3.47  tff(c_8199, plain, (![C_1212, A_1213, B_1214]: (r2_hidden(C_1212, k1_enumset1(A_1213, B_1214, C_1212)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_8176])).
% 10.68/3.47  tff(c_8237, plain, (![B_1233, A_1234]: (r2_hidden(B_1233, k2_tarski(A_1234, B_1233)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_8199])).
% 10.68/3.47  tff(c_102, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.68/3.47  tff(c_171, plain, (![A_95, B_96]: (r1_tarski(A_95, k3_tarski(B_96)) | ~r2_hidden(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/3.47  tff(c_174, plain, (![A_95, A_78, B_79]: (r1_tarski(A_95, k2_xboole_0(A_78, B_79)) | ~r2_hidden(A_95, k2_tarski(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_171])).
% 10.68/3.47  tff(c_8261, plain, (![B_1233, A_1234]: (r1_tarski(B_1233, k2_xboole_0(A_1234, B_1233)))), inference(resolution, [status(thm)], [c_8237, c_174])).
% 10.68/3.47  tff(c_112, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.68/3.47  tff(c_240, plain, (![A_106, B_107]: (r2_xboole_0(A_106, B_107) | B_107=A_106 | ~r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.68/3.47  tff(c_12, plain, (![B_8, A_7]: (~r2_xboole_0(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.68/3.47  tff(c_429, plain, (![B_136, A_137]: (~r1_tarski(B_136, A_137) | B_136=A_137 | ~r1_tarski(A_137, B_136))), inference(resolution, [status(thm)], [c_240, c_12])).
% 10.68/3.47  tff(c_440, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_112, c_429])).
% 10.68/3.47  tff(c_625, plain, (~r1_tarski('#skF_4', k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_440])).
% 10.68/3.47  tff(c_8272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8261, c_625])).
% 10.68/3.47  tff(c_8273, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_440])).
% 10.68/3.47  tff(c_86, plain, (![A_48]: (k2_tarski(A_48, A_48)=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.68/3.47  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.68/3.47  tff(c_221, plain, (![A_103, C_104, B_105]: (r2_hidden(A_103, C_104) | ~r1_tarski(k2_tarski(A_103, B_105), C_104))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.68/3.47  tff(c_255, plain, (![A_108, B_109, B_110]: (r2_hidden(A_108, k2_xboole_0(k2_tarski(A_108, B_109), B_110)))), inference(resolution, [status(thm)], [c_14, c_221])).
% 10.68/3.47  tff(c_262, plain, (![A_48, B_110]: (r2_hidden(A_48, k2_xboole_0(k1_tarski(A_48), B_110)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_255])).
% 10.68/3.47  tff(c_8279, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8273, c_262])).
% 10.68/3.47  tff(c_8286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_8279])).
% 10.68/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.68/3.47  
% 10.68/3.47  Inference rules
% 10.68/3.47  ----------------------
% 10.68/3.47  #Ref     : 0
% 10.68/3.47  #Sup     : 1791
% 10.68/3.47  #Fact    : 0
% 10.68/3.47  #Define  : 0
% 10.68/3.47  #Split   : 1
% 10.68/3.47  #Chain   : 0
% 10.68/3.47  #Close   : 0
% 10.68/3.47  
% 10.68/3.47  Ordering : KBO
% 10.68/3.47  
% 10.68/3.47  Simplification rules
% 10.68/3.47  ----------------------
% 10.68/3.47  #Subsume      : 24
% 10.68/3.47  #Demod        : 1245
% 10.68/3.47  #Tautology    : 630
% 10.68/3.47  #SimpNegUnit  : 1
% 10.68/3.47  #BackRed      : 2
% 10.68/3.47  
% 10.68/3.47  #Partial instantiations: 0
% 10.68/3.47  #Strategies tried      : 1
% 10.68/3.47  
% 10.68/3.47  Timing (in seconds)
% 10.68/3.47  ----------------------
% 10.68/3.47  Preprocessing        : 0.39
% 10.68/3.47  Parsing              : 0.18
% 10.68/3.47  CNF conversion       : 0.03
% 10.68/3.47  Main loop            : 2.31
% 10.68/3.47  Inferencing          : 0.66
% 10.68/3.47  Reduction            : 0.95
% 10.68/3.47  Demodulation         : 0.79
% 10.68/3.47  BG Simplification    : 0.08
% 10.68/3.47  Subsumption          : 0.51
% 10.68/3.47  Abstraction          : 0.11
% 10.68/3.47  MUC search           : 0.00
% 10.68/3.47  Cooper               : 0.00
% 10.68/3.47  Total                : 2.73
% 10.68/3.47  Index Insertion      : 0.00
% 10.68/3.47  Index Deletion       : 0.00
% 10.68/3.47  Index Matching       : 0.00
% 10.68/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
