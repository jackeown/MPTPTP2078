%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:39 EST 2020

% Result     : Theorem 23.87s
% Output     : CNFRefutation 23.87s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 501 expanded)
%              Number of leaves         :   14 ( 174 expanded)
%              Depth                    :   21
%              Number of atoms          :  148 (1307 expanded)
%              Number of equality atoms :   23 ( 109 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_26,plain,(
    k3_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_1'(A_18,B_19),A_18)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_35,B_36,B_37] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_35,B_36),B_37),B_36)
      | r1_tarski(k3_xboole_0(A_35,B_36),B_37) ) ),
    inference(resolution,[status(thm)],[c_31,c_10])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_35,B_36] : r1_tarski(k3_xboole_0(A_35,B_36),B_36) ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_1,B_2,B_24] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_24)
      | ~ r1_tarski(A_1,B_24)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_53,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,k3_xboole_0(A_27,B_28))
      | ~ r2_hidden(D_26,B_28)
      | ~ r2_hidden(D_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1819,plain,(
    ! [A_239,A_240,B_241] :
      ( r1_tarski(A_239,k3_xboole_0(A_240,B_241))
      | ~ r2_hidden('#skF_1'(A_239,k3_xboole_0(A_240,B_241)),B_241)
      | ~ r2_hidden('#skF_1'(A_239,k3_xboole_0(A_240,B_241)),A_240) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_1883,plain,(
    ! [A_242,A_243] :
      ( ~ r2_hidden('#skF_1'(A_242,k3_xboole_0(A_243,A_242)),A_243)
      | r1_tarski(A_242,k3_xboole_0(A_243,A_242)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1819])).

tff(c_1964,plain,(
    ! [A_244,B_245] :
      ( ~ r1_tarski(A_244,B_245)
      | r1_tarski(A_244,k3_xboole_0(B_245,A_244)) ) ),
    inference(resolution,[status(thm)],[c_52,c_1883])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    ! [A_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(A_32,B_33),B_34)
      | ~ r1_tarski(A_32,B_34)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [A_73,B_74,B_75,B_76] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_75)
      | ~ r1_tarski(B_76,B_75)
      | ~ r1_tarski(A_73,B_76)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_318,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_1'(A_80,B_81),'#skF_5')
      | ~ r1_tarski(A_80,'#skF_4')
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_28,c_292])).

tff(c_327,plain,(
    ! [A_82] :
      ( ~ r1_tarski(A_82,'#skF_4')
      | r1_tarski(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_318,c_4])).

tff(c_91,plain,(
    ! [A_32,B_33,B_2,B_34] :
      ( r2_hidden('#skF_1'(A_32,B_33),B_2)
      | ~ r1_tarski(B_34,B_2)
      | ~ r1_tarski(A_32,B_34)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_333,plain,(
    ! [A_32,B_33,A_82] :
      ( r2_hidden('#skF_1'(A_32,B_33),'#skF_5')
      | ~ r1_tarski(A_32,A_82)
      | r1_tarski(A_32,B_33)
      | ~ r1_tarski(A_82,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_327,c_91])).

tff(c_39011,plain,(
    ! [A_1186,B_1187,B_1188] :
      ( r2_hidden('#skF_1'(A_1186,B_1187),'#skF_5')
      | r1_tarski(A_1186,B_1187)
      | ~ r1_tarski(k3_xboole_0(B_1188,A_1186),'#skF_4')
      | ~ r1_tarski(A_1186,B_1188) ) ),
    inference(resolution,[status(thm)],[c_1964,c_333])).

tff(c_39047,plain,(
    ! [B_1187,A_35] :
      ( r2_hidden('#skF_1'('#skF_4',B_1187),'#skF_5')
      | r1_tarski('#skF_4',B_1187)
      | ~ r1_tarski('#skF_4',A_35) ) ),
    inference(resolution,[status(thm)],[c_111,c_39011])).

tff(c_39048,plain,(
    ! [A_35] : ~ r1_tarski('#skF_4',A_35) ),
    inference(splitLeft,[status(thm)],[c_39047])).

tff(c_39050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39048,c_28])).

tff(c_39052,plain,(
    ! [B_1189] :
      ( r2_hidden('#skF_1'('#skF_4',B_1189),'#skF_5')
      | r1_tarski('#skF_4',B_1189) ) ),
    inference(splitRight,[status(thm)],[c_39047])).

tff(c_1882,plain,(
    ! [A_1,A_240] :
      ( ~ r2_hidden('#skF_1'(A_1,k3_xboole_0(A_240,A_1)),A_240)
      | r1_tarski(A_1,k3_xboole_0(A_240,A_1)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1819])).

tff(c_39153,plain,(
    r1_tarski('#skF_4',k3_xboole_0('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_39052,c_1882])).

tff(c_326,plain,(
    ! [A_80] :
      ( ~ r1_tarski(A_80,'#skF_4')
      | r1_tarski(A_80,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_318,c_4])).

tff(c_207,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_2'(A_58,B_59,C_60),A_58)
      | r2_hidden('#skF_3'(A_58,B_59,C_60),C_60)
      | k3_xboole_0(A_58,B_59) = C_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_239,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_3'(A_61,B_62,A_61),A_61)
      | k3_xboole_0(A_61,B_62) = A_61 ) ),
    inference(resolution,[status(thm)],[c_207,c_20])).

tff(c_267,plain,(
    ! [A_66,B_67,B_68] :
      ( r2_hidden('#skF_3'(A_66,B_67,A_66),B_68)
      | ~ r1_tarski(A_66,B_68)
      | k3_xboole_0(A_66,B_67) = A_66 ) ),
    inference(resolution,[status(thm)],[c_239,c_2])).

tff(c_18043,plain,(
    ! [A_812,B_813,B_814,B_815] :
      ( r2_hidden('#skF_3'(A_812,B_813,A_812),B_814)
      | ~ r1_tarski(B_815,B_814)
      | ~ r1_tarski(A_812,B_815)
      | k3_xboole_0(A_812,B_813) = A_812 ) ),
    inference(resolution,[status(thm)],[c_267,c_2])).

tff(c_18399,plain,(
    ! [A_812,B_813,A_80] :
      ( r2_hidden('#skF_3'(A_812,B_813,A_812),'#skF_5')
      | ~ r1_tarski(A_812,A_80)
      | k3_xboole_0(A_812,B_813) = A_812
      | ~ r1_tarski(A_80,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_326,c_18043])).

tff(c_39452,plain,(
    ! [B_813] :
      ( r2_hidden('#skF_3'('#skF_4',B_813,'#skF_4'),'#skF_5')
      | k3_xboole_0('#skF_4',B_813) = '#skF_4'
      | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_4'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39153,c_18399])).

tff(c_39494,plain,(
    ! [B_813] :
      ( r2_hidden('#skF_3'('#skF_4',B_813,'#skF_4'),'#skF_5')
      | k3_xboole_0('#skF_4',B_813) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_39452])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_3003,plain,(
    ! [A_283,B_284,C_285,B_286] :
      ( r2_hidden('#skF_2'(A_283,B_284,C_285),B_286)
      | ~ r1_tarski(A_283,B_286)
      | r2_hidden('#skF_3'(A_283,B_284,C_285),C_285)
      | k3_xboole_0(A_283,B_284) = C_285 ) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_3065,plain,(
    ! [A_287,B_288,B_289] :
      ( ~ r1_tarski(A_287,B_288)
      | r2_hidden('#skF_3'(A_287,B_289,B_288),B_288)
      | k3_xboole_0(A_287,B_289) = B_288 ) ),
    inference(resolution,[status(thm)],[c_3003,c_20])).

tff(c_3095,plain,(
    ! [A_287,B_289,B_288,B_2] :
      ( r2_hidden('#skF_3'(A_287,B_289,B_288),B_2)
      | ~ r1_tarski(B_288,B_2)
      | ~ r1_tarski(A_287,B_288)
      | k3_xboole_0(A_287,B_289) = B_288 ) ),
    inference(resolution,[status(thm)],[c_3065,c_2])).

tff(c_40002,plain,(
    ! [B_1201] :
      ( r2_hidden('#skF_3'('#skF_4',B_1201,'#skF_4'),'#skF_5')
      | k3_xboole_0('#skF_4',B_1201) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_39452])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40061,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40002,c_18])).

tff(c_40097,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_40061])).

tff(c_40458,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40097])).

tff(c_40465,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3095,c_40458])).

tff(c_40493,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_40465])).

tff(c_40495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_40493])).

tff(c_40497,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_40097])).

tff(c_40496,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_40097])).

tff(c_40721,plain,(
    ! [B_1207] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),B_1207)
      | ~ r1_tarski('#skF_4',B_1207) ) ),
    inference(resolution,[status(thm)],[c_40496,c_2])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40797,plain,
    ( ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_40721,c_14])).

tff(c_40847,plain,
    ( ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_4'),'#skF_5')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_40497,c_40797])).

tff(c_40848,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_40847])).

tff(c_40991,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39494,c_40848])).

tff(c_41013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_40991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.87/14.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.87/14.28  
% 23.87/14.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.87/14.28  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 23.87/14.28  
% 23.87/14.28  %Foreground sorts:
% 23.87/14.28  
% 23.87/14.28  
% 23.87/14.28  %Background operators:
% 23.87/14.28  
% 23.87/14.28  
% 23.87/14.28  %Foreground operators:
% 23.87/14.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.87/14.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.87/14.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.87/14.28  tff('#skF_5', type, '#skF_5': $i).
% 23.87/14.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.87/14.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.87/14.28  tff('#skF_4', type, '#skF_4': $i).
% 23.87/14.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 23.87/14.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.87/14.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.87/14.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 23.87/14.28  
% 23.87/14.29  tff(f_46, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 23.87/14.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 23.87/14.29  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 23.87/14.29  tff(c_26, plain, (k3_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_46])).
% 23.87/14.29  tff(c_31, plain, (![A_18, B_19]: (r2_hidden('#skF_1'(A_18, B_19), A_18) | r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.87/14.29  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.87/14.29  tff(c_95, plain, (![A_35, B_36, B_37]: (r2_hidden('#skF_1'(k3_xboole_0(A_35, B_36), B_37), B_36) | r1_tarski(k3_xboole_0(A_35, B_36), B_37))), inference(resolution, [status(thm)], [c_31, c_10])).
% 23.87/14.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.87/14.29  tff(c_111, plain, (![A_35, B_36]: (r1_tarski(k3_xboole_0(A_35, B_36), B_36))), inference(resolution, [status(thm)], [c_95, c_4])).
% 23.87/14.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.87/14.29  tff(c_49, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.87/14.29  tff(c_52, plain, (![A_1, B_2, B_24]: (r2_hidden('#skF_1'(A_1, B_2), B_24) | ~r1_tarski(A_1, B_24) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_49])).
% 23.87/14.29  tff(c_53, plain, (![D_26, A_27, B_28]: (r2_hidden(D_26, k3_xboole_0(A_27, B_28)) | ~r2_hidden(D_26, B_28) | ~r2_hidden(D_26, A_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.87/14.29  tff(c_1819, plain, (![A_239, A_240, B_241]: (r1_tarski(A_239, k3_xboole_0(A_240, B_241)) | ~r2_hidden('#skF_1'(A_239, k3_xboole_0(A_240, B_241)), B_241) | ~r2_hidden('#skF_1'(A_239, k3_xboole_0(A_240, B_241)), A_240))), inference(resolution, [status(thm)], [c_53, c_4])).
% 23.87/14.29  tff(c_1883, plain, (![A_242, A_243]: (~r2_hidden('#skF_1'(A_242, k3_xboole_0(A_243, A_242)), A_243) | r1_tarski(A_242, k3_xboole_0(A_243, A_242)))), inference(resolution, [status(thm)], [c_6, c_1819])).
% 23.87/14.29  tff(c_1964, plain, (![A_244, B_245]: (~r1_tarski(A_244, B_245) | r1_tarski(A_244, k3_xboole_0(B_245, A_244)))), inference(resolution, [status(thm)], [c_52, c_1883])).
% 23.87/14.29  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 23.87/14.29  tff(c_76, plain, (![A_32, B_33, B_34]: (r2_hidden('#skF_1'(A_32, B_33), B_34) | ~r1_tarski(A_32, B_34) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_6, c_49])).
% 23.87/14.29  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.87/14.29  tff(c_292, plain, (![A_73, B_74, B_75, B_76]: (r2_hidden('#skF_1'(A_73, B_74), B_75) | ~r1_tarski(B_76, B_75) | ~r1_tarski(A_73, B_76) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_76, c_2])).
% 23.87/14.29  tff(c_318, plain, (![A_80, B_81]: (r2_hidden('#skF_1'(A_80, B_81), '#skF_5') | ~r1_tarski(A_80, '#skF_4') | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_28, c_292])).
% 23.87/14.29  tff(c_327, plain, (![A_82]: (~r1_tarski(A_82, '#skF_4') | r1_tarski(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_318, c_4])).
% 23.87/14.29  tff(c_91, plain, (![A_32, B_33, B_2, B_34]: (r2_hidden('#skF_1'(A_32, B_33), B_2) | ~r1_tarski(B_34, B_2) | ~r1_tarski(A_32, B_34) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_76, c_2])).
% 23.87/14.29  tff(c_333, plain, (![A_32, B_33, A_82]: (r2_hidden('#skF_1'(A_32, B_33), '#skF_5') | ~r1_tarski(A_32, A_82) | r1_tarski(A_32, B_33) | ~r1_tarski(A_82, '#skF_4'))), inference(resolution, [status(thm)], [c_327, c_91])).
% 23.87/14.29  tff(c_39011, plain, (![A_1186, B_1187, B_1188]: (r2_hidden('#skF_1'(A_1186, B_1187), '#skF_5') | r1_tarski(A_1186, B_1187) | ~r1_tarski(k3_xboole_0(B_1188, A_1186), '#skF_4') | ~r1_tarski(A_1186, B_1188))), inference(resolution, [status(thm)], [c_1964, c_333])).
% 23.87/14.29  tff(c_39047, plain, (![B_1187, A_35]: (r2_hidden('#skF_1'('#skF_4', B_1187), '#skF_5') | r1_tarski('#skF_4', B_1187) | ~r1_tarski('#skF_4', A_35))), inference(resolution, [status(thm)], [c_111, c_39011])).
% 23.87/14.29  tff(c_39048, plain, (![A_35]: (~r1_tarski('#skF_4', A_35))), inference(splitLeft, [status(thm)], [c_39047])).
% 23.87/14.29  tff(c_39050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39048, c_28])).
% 23.87/14.29  tff(c_39052, plain, (![B_1189]: (r2_hidden('#skF_1'('#skF_4', B_1189), '#skF_5') | r1_tarski('#skF_4', B_1189))), inference(splitRight, [status(thm)], [c_39047])).
% 23.87/14.29  tff(c_1882, plain, (![A_1, A_240]: (~r2_hidden('#skF_1'(A_1, k3_xboole_0(A_240, A_1)), A_240) | r1_tarski(A_1, k3_xboole_0(A_240, A_1)))), inference(resolution, [status(thm)], [c_6, c_1819])).
% 23.87/14.29  tff(c_39153, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_39052, c_1882])).
% 23.87/14.29  tff(c_326, plain, (![A_80]: (~r1_tarski(A_80, '#skF_4') | r1_tarski(A_80, '#skF_5'))), inference(resolution, [status(thm)], [c_318, c_4])).
% 23.87/14.29  tff(c_207, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_2'(A_58, B_59, C_60), A_58) | r2_hidden('#skF_3'(A_58, B_59, C_60), C_60) | k3_xboole_0(A_58, B_59)=C_60)), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.87/14.29  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.87/14.29  tff(c_239, plain, (![A_61, B_62]: (r2_hidden('#skF_3'(A_61, B_62, A_61), A_61) | k3_xboole_0(A_61, B_62)=A_61)), inference(resolution, [status(thm)], [c_207, c_20])).
% 23.87/14.29  tff(c_267, plain, (![A_66, B_67, B_68]: (r2_hidden('#skF_3'(A_66, B_67, A_66), B_68) | ~r1_tarski(A_66, B_68) | k3_xboole_0(A_66, B_67)=A_66)), inference(resolution, [status(thm)], [c_239, c_2])).
% 23.87/14.29  tff(c_18043, plain, (![A_812, B_813, B_814, B_815]: (r2_hidden('#skF_3'(A_812, B_813, A_812), B_814) | ~r1_tarski(B_815, B_814) | ~r1_tarski(A_812, B_815) | k3_xboole_0(A_812, B_813)=A_812)), inference(resolution, [status(thm)], [c_267, c_2])).
% 23.87/14.29  tff(c_18399, plain, (![A_812, B_813, A_80]: (r2_hidden('#skF_3'(A_812, B_813, A_812), '#skF_5') | ~r1_tarski(A_812, A_80) | k3_xboole_0(A_812, B_813)=A_812 | ~r1_tarski(A_80, '#skF_4'))), inference(resolution, [status(thm)], [c_326, c_18043])).
% 23.87/14.29  tff(c_39452, plain, (![B_813]: (r2_hidden('#skF_3'('#skF_4', B_813, '#skF_4'), '#skF_5') | k3_xboole_0('#skF_4', B_813)='#skF_4' | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_4'), '#skF_4'))), inference(resolution, [status(thm)], [c_39153, c_18399])).
% 23.87/14.29  tff(c_39494, plain, (![B_813]: (r2_hidden('#skF_3'('#skF_4', B_813, '#skF_4'), '#skF_5') | k3_xboole_0('#skF_4', B_813)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_39452])).
% 23.87/14.29  tff(c_42, plain, (![A_20, B_21]: (~r2_hidden('#skF_1'(A_20, B_21), B_21) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.87/14.29  tff(c_47, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_42])).
% 23.87/14.29  tff(c_3003, plain, (![A_283, B_284, C_285, B_286]: (r2_hidden('#skF_2'(A_283, B_284, C_285), B_286) | ~r1_tarski(A_283, B_286) | r2_hidden('#skF_3'(A_283, B_284, C_285), C_285) | k3_xboole_0(A_283, B_284)=C_285)), inference(resolution, [status(thm)], [c_207, c_2])).
% 23.87/14.29  tff(c_3065, plain, (![A_287, B_288, B_289]: (~r1_tarski(A_287, B_288) | r2_hidden('#skF_3'(A_287, B_289, B_288), B_288) | k3_xboole_0(A_287, B_289)=B_288)), inference(resolution, [status(thm)], [c_3003, c_20])).
% 23.87/14.29  tff(c_3095, plain, (![A_287, B_289, B_288, B_2]: (r2_hidden('#skF_3'(A_287, B_289, B_288), B_2) | ~r1_tarski(B_288, B_2) | ~r1_tarski(A_287, B_288) | k3_xboole_0(A_287, B_289)=B_288)), inference(resolution, [status(thm)], [c_3065, c_2])).
% 23.87/14.29  tff(c_40002, plain, (![B_1201]: (r2_hidden('#skF_3'('#skF_4', B_1201, '#skF_4'), '#skF_5') | k3_xboole_0('#skF_4', B_1201)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_39452])).
% 23.87/14.29  tff(c_18, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.87/14.29  tff(c_40061, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_40002, c_18])).
% 23.87/14.29  tff(c_40097, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_40061])).
% 23.87/14.29  tff(c_40458, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_40097])).
% 23.87/14.29  tff(c_40465, plain, (~r1_tarski('#skF_4', '#skF_4') | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_3095, c_40458])).
% 23.87/14.29  tff(c_40493, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_40465])).
% 23.87/14.29  tff(c_40495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_40493])).
% 23.87/14.29  tff(c_40497, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_40097])).
% 23.87/14.29  tff(c_40496, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_40097])).
% 23.87/14.29  tff(c_40721, plain, (![B_1207]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), B_1207) | ~r1_tarski('#skF_4', B_1207))), inference(resolution, [status(thm)], [c_40496, c_2])).
% 23.87/14.29  tff(c_14, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.87/14.29  tff(c_40797, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_40721, c_14])).
% 23.87/14.29  tff(c_40847, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_4'), '#skF_5') | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_40497, c_40797])).
% 23.87/14.29  tff(c_40848, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_26, c_40847])).
% 23.87/14.29  tff(c_40991, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_39494, c_40848])).
% 23.87/14.29  tff(c_41013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_40991])).
% 23.87/14.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.87/14.29  
% 23.87/14.29  Inference rules
% 23.87/14.29  ----------------------
% 23.87/14.29  #Ref     : 0
% 23.87/14.29  #Sup     : 11992
% 23.87/14.29  #Fact    : 0
% 23.87/14.29  #Define  : 0
% 23.87/14.29  #Split   : 3
% 23.87/14.29  #Chain   : 0
% 23.87/14.29  #Close   : 0
% 23.87/14.29  
% 23.87/14.29  Ordering : KBO
% 23.87/14.29  
% 23.87/14.29  Simplification rules
% 23.87/14.29  ----------------------
% 23.87/14.29  #Subsume      : 3428
% 23.87/14.29  #Demod        : 746
% 23.87/14.29  #Tautology    : 371
% 23.87/14.29  #SimpNegUnit  : 13
% 23.87/14.29  #BackRed      : 1
% 23.87/14.29  
% 23.87/14.29  #Partial instantiations: 0
% 23.87/14.29  #Strategies tried      : 1
% 23.87/14.29  
% 23.87/14.29  Timing (in seconds)
% 23.87/14.29  ----------------------
% 23.87/14.30  Preprocessing        : 0.27
% 23.87/14.30  Parsing              : 0.14
% 23.87/14.30  CNF conversion       : 0.02
% 23.87/14.30  Main loop            : 13.25
% 23.87/14.30  Inferencing          : 1.24
% 23.87/14.30  Reduction            : 2.14
% 23.87/14.30  Demodulation         : 1.67
% 23.87/14.30  BG Simplification    : 0.19
% 23.87/14.30  Subsumption          : 9.16
% 23.87/14.30  Abstraction          : 0.29
% 23.87/14.30  MUC search           : 0.00
% 23.87/14.30  Cooper               : 0.00
% 23.87/14.30  Total                : 13.56
% 23.87/14.30  Index Insertion      : 0.00
% 23.87/14.30  Index Deletion       : 0.00
% 23.87/14.30  Index Matching       : 0.00
% 23.87/14.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
