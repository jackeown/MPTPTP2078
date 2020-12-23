%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0389+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:14 EST 2020

% Result     : Theorem 11.21s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 159 expanded)
%              Number of leaves         :   22 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 378 expanded)
%              Number of equality atoms :   31 (  72 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_51,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_5'(A_20,B_21),A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_5'(A_35,B_36),B_36)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    ! [A_20] : r1_tarski(A_20,A_20) ),
    inference(resolution,[status(thm)],[c_28,c_72])).

tff(c_40,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_79,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,(
    ! [A_44,B_45,B_46] :
      ( r2_hidden('#skF_5'(A_44,B_45),B_46)
      | ~ r1_tarski(A_44,B_46)
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_28,c_79])).

tff(c_34,plain,(
    ! [B_27,A_26] :
      ( ~ v1_xboole_0(B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    ! [B_47,A_48,B_49] :
      ( ~ v1_xboole_0(B_47)
      | ~ r1_tarski(A_48,B_47)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_87,c_34])).

tff(c_112,plain,(
    ! [B_49] :
      ( ~ v1_xboole_0('#skF_7')
      | r1_tarski('#skF_6',B_49) ) ),
    inference(resolution,[status(thm)],[c_40,c_103])).

tff(c_113,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_24,plain,(
    ! [C_24,B_21,A_20] :
      ( r2_hidden(C_24,B_21)
      | ~ r2_hidden(C_24,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_157,plain,(
    ! [A_57,B_58,B_59,B_60] :
      ( r2_hidden('#skF_5'(A_57,B_58),B_59)
      | ~ r1_tarski(B_60,B_59)
      | ~ r1_tarski(A_57,B_60)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_87,c_24])).

tff(c_167,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_5'(A_61,B_62),'#skF_7')
      | ~ r1_tarski(A_61,'#skF_6')
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_40,c_157])).

tff(c_14,plain,(
    ! [C_13,D_16,A_1] :
      ( r2_hidden(C_13,D_16)
      | ~ r2_hidden(D_16,A_1)
      | ~ r2_hidden(C_13,k1_setfam_1(A_1))
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_179,plain,(
    ! [C_13,A_61,B_62] :
      ( r2_hidden(C_13,'#skF_5'(A_61,B_62))
      | ~ r2_hidden(C_13,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7'
      | ~ r1_tarski(A_61,'#skF_6')
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_167,c_14])).

tff(c_229,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30])).

tff(c_235,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_52])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_235])).

tff(c_243,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_114,plain,(
    ! [A_50,C_51] :
      ( r2_hidden('#skF_1'(A_50,k1_setfam_1(A_50),C_51),A_50)
      | r2_hidden(C_51,k1_setfam_1(A_50))
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_328,plain,(
    ! [A_84,C_85,B_86] :
      ( r2_hidden('#skF_1'(A_84,k1_setfam_1(A_84),C_85),B_86)
      | ~ r1_tarski(A_84,B_86)
      | r2_hidden(C_85,k1_setfam_1(A_84))
      | k1_xboole_0 = A_84 ) ),
    inference(resolution,[status(thm)],[c_114,c_24])).

tff(c_2296,plain,(
    ! [A_241,C_242,B_243,B_244] :
      ( r2_hidden('#skF_1'(A_241,k1_setfam_1(A_241),C_242),B_243)
      | ~ r1_tarski(B_244,B_243)
      | ~ r1_tarski(A_241,B_244)
      | r2_hidden(C_242,k1_setfam_1(A_241))
      | k1_xboole_0 = A_241 ) ),
    inference(resolution,[status(thm)],[c_328,c_24])).

tff(c_2407,plain,(
    ! [A_248,C_249] :
      ( r2_hidden('#skF_1'(A_248,k1_setfam_1(A_248),C_249),'#skF_7')
      | ~ r1_tarski(A_248,'#skF_6')
      | r2_hidden(C_249,k1_setfam_1(A_248))
      | k1_xboole_0 = A_248 ) ),
    inference(resolution,[status(thm)],[c_40,c_2296])).

tff(c_2424,plain,(
    ! [C_13,A_248,C_249] :
      ( r2_hidden(C_13,'#skF_1'(A_248,k1_setfam_1(A_248),C_249))
      | ~ r2_hidden(C_13,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7'
      | ~ r1_tarski(A_248,'#skF_6')
      | r2_hidden(C_249,k1_setfam_1(A_248))
      | k1_xboole_0 = A_248 ) ),
    inference(resolution,[status(thm)],[c_2407,c_14])).

tff(c_13153,plain,(
    ! [C_721,A_722,C_723] :
      ( r2_hidden(C_721,'#skF_1'(A_722,k1_setfam_1(A_722),C_723))
      | ~ r2_hidden(C_721,k1_setfam_1('#skF_7'))
      | ~ r1_tarski(A_722,'#skF_6')
      | r2_hidden(C_723,k1_setfam_1(A_722))
      | k1_xboole_0 = A_722 ) ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_2424])).

tff(c_16,plain,(
    ! [C_13,A_1] :
      ( ~ r2_hidden(C_13,'#skF_1'(A_1,k1_setfam_1(A_1),C_13))
      | r2_hidden(C_13,k1_setfam_1(A_1))
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13235,plain,(
    ! [C_724,A_725] :
      ( ~ r2_hidden(C_724,k1_setfam_1('#skF_7'))
      | ~ r1_tarski(A_725,'#skF_6')
      | r2_hidden(C_724,k1_setfam_1(A_725))
      | k1_xboole_0 = A_725 ) ),
    inference(resolution,[status(thm)],[c_13153,c_16])).

tff(c_13582,plain,(
    ! [A_726,B_727] :
      ( ~ r1_tarski(A_726,'#skF_6')
      | r2_hidden('#skF_5'(k1_setfam_1('#skF_7'),B_727),k1_setfam_1(A_726))
      | k1_xboole_0 = A_726
      | r1_tarski(k1_setfam_1('#skF_7'),B_727) ) ),
    inference(resolution,[status(thm)],[c_28,c_13235])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_5'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_13975,plain,(
    ! [A_732] :
      ( ~ r1_tarski(A_732,'#skF_6')
      | k1_xboole_0 = A_732
      | r1_tarski(k1_setfam_1('#skF_7'),k1_setfam_1(A_732)) ) ),
    inference(resolution,[status(thm)],[c_13582,c_26])).

tff(c_36,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_7'),k1_setfam_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14069,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_13975,c_36])).

tff(c_14146,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_14069])).

tff(c_14148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_14146])).

tff(c_14150,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_32,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14154,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_14150,c_32])).

tff(c_22,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14159,plain,(
    k1_setfam_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14154,c_14154,c_22])).

tff(c_62,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_5'(A_31,B_32),A_31)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_67,plain,(
    ! [A_33,B_34] :
      ( ~ v1_xboole_0(A_33)
      | r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_62,c_34])).

tff(c_71,plain,(
    ~ v1_xboole_0(k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_67,c_36])).

tff(c_14176,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14159,c_71])).

tff(c_14180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14150,c_14176])).

%------------------------------------------------------------------------------
