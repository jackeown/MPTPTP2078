%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:52 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 128 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :   82 ( 138 expanded)
%              Number of equality atoms :   47 (  90 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_73,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_118,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_185,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(B_62,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_118])).

tff(c_42,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_224,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_42])).

tff(c_240,plain,(
    ! [A_66] : k2_xboole_0(k1_xboole_0,A_66) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_18])).

tff(c_463,plain,(
    ! [A_84,B_85] : k2_xboole_0(A_84,k4_xboole_0(B_85,A_84)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_473,plain,(
    ! [B_85] : k4_xboole_0(B_85,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_240])).

tff(c_488,plain,(
    ! [B_85] : k4_xboole_0(B_85,k1_xboole_0) = B_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_473])).

tff(c_26,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_311,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_356,plain,(
    ! [A_77,B_78] :
      ( ~ r1_xboole_0(A_77,B_78)
      | k3_xboole_0(A_77,B_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_311])).

tff(c_415,plain,(
    ! [A_82] : k3_xboole_0(A_82,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_356])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_426,plain,(
    ! [A_82] : k5_xboole_0(A_82,k1_xboole_0) = k4_xboole_0(A_82,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_16])).

tff(c_517,plain,(
    ! [A_82] : k5_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_426])).

tff(c_101,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,A_45)
      | ~ r1_xboole_0(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [A_21] : r1_xboole_0(k1_xboole_0,A_21) ),
    inference(resolution,[status(thm)],[c_26,c_101])).

tff(c_390,plain,(
    ! [A_81] : k3_xboole_0(k1_xboole_0,A_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_356])).

tff(c_398,plain,(
    ! [A_81] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_16])).

tff(c_518,plain,(
    ! [A_81] : k4_xboole_0(k1_xboole_0,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_398])).

tff(c_365,plain,(
    ! [A_79,B_80] : k4_xboole_0(k2_xboole_0(A_79,B_80),B_80) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_374,plain,(
    ! [A_66] : k4_xboole_0(k1_xboole_0,A_66) = k4_xboole_0(A_66,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_365])).

tff(c_571,plain,(
    ! [A_66] : k4_xboole_0(A_66,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_374])).

tff(c_14,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_153,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_157,plain,(
    ! [B_11] : k3_xboole_0(B_11,B_11) = B_11 ),
    inference(resolution,[status(thm)],[c_14,c_153])).

tff(c_211,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_220,plain,(
    ! [B_11] : k5_xboole_0(B_11,B_11) = k4_xboole_0(B_11,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_211])).

tff(c_572,plain,(
    ! [B_11] : k5_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_220])).

tff(c_158,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tarski(A_56),B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1002,plain,(
    ! [A_113,B_114] :
      ( k3_xboole_0(k1_tarski(A_113),B_114) = k1_tarski(A_113)
      | ~ r2_hidden(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_158,c_20])).

tff(c_1018,plain,(
    ! [A_113,B_114] :
      ( k5_xboole_0(k1_tarski(A_113),k1_tarski(A_113)) = k4_xboole_0(k1_tarski(A_113),B_114)
      | ~ r2_hidden(A_113,B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_16])).

tff(c_1044,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(k1_tarski(A_115),B_116) = k1_xboole_0
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_1018])).

tff(c_22,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1066,plain,(
    ! [B_116,A_115] :
      ( k2_xboole_0(B_116,k1_tarski(A_115)) = k2_xboole_0(B_116,k1_xboole_0)
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_22])).

tff(c_1354,plain,(
    ! [B_123,A_124] :
      ( k2_xboole_0(B_123,k1_tarski(A_124)) = B_123
      | ~ r2_hidden(A_124,B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1066])).

tff(c_191,plain,(
    ! [B_62,A_61] : k2_xboole_0(B_62,A_61) = k2_xboole_0(A_61,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_42])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_223,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_44])).

tff(c_1392,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1354,c_223])).

tff(c_1441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:34:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.44  
% 2.86/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.86/1.44  
% 2.86/1.44  %Foreground sorts:
% 2.86/1.44  
% 2.86/1.44  
% 2.86/1.44  %Background operators:
% 2.86/1.44  
% 2.86/1.44  
% 2.86/1.44  %Foreground operators:
% 2.86/1.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.86/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.86/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.86/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.86/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.86/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.86/1.44  
% 2.86/1.45  tff(f_92, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.86/1.45  tff(f_61, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.86/1.45  tff(f_73, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.86/1.45  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.86/1.45  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.86/1.45  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.86/1.45  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.86/1.45  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.86/1.45  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.86/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.86/1.45  tff(f_69, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.86/1.45  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.86/1.45  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.86/1.45  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.86/1.45  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.45  tff(c_18, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.45  tff(c_28, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.86/1.45  tff(c_118, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.86/1.45  tff(c_185, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(B_62, A_61))), inference(superposition, [status(thm), theory('equality')], [c_28, c_118])).
% 2.86/1.45  tff(c_42, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.86/1.45  tff(c_224, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_185, c_42])).
% 2.86/1.45  tff(c_240, plain, (![A_66]: (k2_xboole_0(k1_xboole_0, A_66)=A_66)), inference(superposition, [status(thm), theory('equality')], [c_224, c_18])).
% 2.86/1.45  tff(c_463, plain, (![A_84, B_85]: (k2_xboole_0(A_84, k4_xboole_0(B_85, A_84))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.86/1.45  tff(c_473, plain, (![B_85]: (k4_xboole_0(B_85, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_85))), inference(superposition, [status(thm), theory('equality')], [c_463, c_240])).
% 2.86/1.45  tff(c_488, plain, (![B_85]: (k4_xboole_0(B_85, k1_xboole_0)=B_85)), inference(demodulation, [status(thm), theory('equality')], [c_240, c_473])).
% 2.86/1.45  tff(c_26, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.45  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.86/1.45  tff(c_311, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.45  tff(c_356, plain, (![A_77, B_78]: (~r1_xboole_0(A_77, B_78) | k3_xboole_0(A_77, B_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_311])).
% 2.86/1.45  tff(c_415, plain, (![A_82]: (k3_xboole_0(A_82, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_356])).
% 2.86/1.45  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.86/1.45  tff(c_426, plain, (![A_82]: (k5_xboole_0(A_82, k1_xboole_0)=k4_xboole_0(A_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_415, c_16])).
% 2.86/1.45  tff(c_517, plain, (![A_82]: (k5_xboole_0(A_82, k1_xboole_0)=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_488, c_426])).
% 2.86/1.45  tff(c_101, plain, (![B_44, A_45]: (r1_xboole_0(B_44, A_45) | ~r1_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.45  tff(c_104, plain, (![A_21]: (r1_xboole_0(k1_xboole_0, A_21))), inference(resolution, [status(thm)], [c_26, c_101])).
% 2.86/1.45  tff(c_390, plain, (![A_81]: (k3_xboole_0(k1_xboole_0, A_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_356])).
% 2.86/1.45  tff(c_398, plain, (![A_81]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_81))), inference(superposition, [status(thm), theory('equality')], [c_390, c_16])).
% 2.86/1.45  tff(c_518, plain, (![A_81]: (k4_xboole_0(k1_xboole_0, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_517, c_398])).
% 2.86/1.45  tff(c_365, plain, (![A_79, B_80]: (k4_xboole_0(k2_xboole_0(A_79, B_80), B_80)=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.86/1.45  tff(c_374, plain, (![A_66]: (k4_xboole_0(k1_xboole_0, A_66)=k4_xboole_0(A_66, A_66))), inference(superposition, [status(thm), theory('equality')], [c_240, c_365])).
% 2.86/1.45  tff(c_571, plain, (![A_66]: (k4_xboole_0(A_66, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_518, c_374])).
% 2.86/1.45  tff(c_14, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.86/1.45  tff(c_153, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.86/1.45  tff(c_157, plain, (![B_11]: (k3_xboole_0(B_11, B_11)=B_11)), inference(resolution, [status(thm)], [c_14, c_153])).
% 2.86/1.45  tff(c_211, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.86/1.45  tff(c_220, plain, (![B_11]: (k5_xboole_0(B_11, B_11)=k4_xboole_0(B_11, B_11))), inference(superposition, [status(thm), theory('equality')], [c_157, c_211])).
% 2.86/1.45  tff(c_572, plain, (![B_11]: (k5_xboole_0(B_11, B_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_571, c_220])).
% 2.86/1.45  tff(c_158, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), B_57) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.86/1.45  tff(c_20, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.86/1.45  tff(c_1002, plain, (![A_113, B_114]: (k3_xboole_0(k1_tarski(A_113), B_114)=k1_tarski(A_113) | ~r2_hidden(A_113, B_114))), inference(resolution, [status(thm)], [c_158, c_20])).
% 2.86/1.45  tff(c_1018, plain, (![A_113, B_114]: (k5_xboole_0(k1_tarski(A_113), k1_tarski(A_113))=k4_xboole_0(k1_tarski(A_113), B_114) | ~r2_hidden(A_113, B_114))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_16])).
% 2.86/1.45  tff(c_1044, plain, (![A_115, B_116]: (k4_xboole_0(k1_tarski(A_115), B_116)=k1_xboole_0 | ~r2_hidden(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_572, c_1018])).
% 2.86/1.45  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.86/1.45  tff(c_1066, plain, (![B_116, A_115]: (k2_xboole_0(B_116, k1_tarski(A_115))=k2_xboole_0(B_116, k1_xboole_0) | ~r2_hidden(A_115, B_116))), inference(superposition, [status(thm), theory('equality')], [c_1044, c_22])).
% 2.86/1.45  tff(c_1354, plain, (![B_123, A_124]: (k2_xboole_0(B_123, k1_tarski(A_124))=B_123 | ~r2_hidden(A_124, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1066])).
% 2.86/1.45  tff(c_191, plain, (![B_62, A_61]: (k2_xboole_0(B_62, A_61)=k2_xboole_0(A_61, B_62))), inference(superposition, [status(thm), theory('equality')], [c_185, c_42])).
% 2.86/1.45  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.45  tff(c_223, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_44])).
% 2.86/1.45  tff(c_1392, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1354, c_223])).
% 2.86/1.45  tff(c_1441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1392])).
% 2.86/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  Inference rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Ref     : 0
% 2.86/1.45  #Sup     : 327
% 2.86/1.45  #Fact    : 0
% 2.86/1.45  #Define  : 0
% 2.86/1.45  #Split   : 0
% 2.86/1.45  #Chain   : 0
% 2.86/1.45  #Close   : 0
% 2.86/1.45  
% 2.86/1.45  Ordering : KBO
% 2.86/1.45  
% 2.86/1.45  Simplification rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Subsume      : 15
% 2.86/1.45  #Demod        : 252
% 2.86/1.45  #Tautology    : 256
% 2.86/1.45  #SimpNegUnit  : 2
% 2.86/1.45  #BackRed      : 4
% 2.86/1.45  
% 2.86/1.45  #Partial instantiations: 0
% 2.86/1.45  #Strategies tried      : 1
% 2.86/1.45  
% 2.86/1.45  Timing (in seconds)
% 2.86/1.45  ----------------------
% 2.86/1.46  Preprocessing        : 0.32
% 2.86/1.46  Parsing              : 0.17
% 2.86/1.46  CNF conversion       : 0.02
% 2.86/1.46  Main loop            : 0.38
% 2.86/1.46  Inferencing          : 0.14
% 2.86/1.46  Reduction            : 0.14
% 2.86/1.46  Demodulation         : 0.12
% 2.86/1.46  BG Simplification    : 0.02
% 2.86/1.46  Subsumption          : 0.05
% 2.86/1.46  Abstraction          : 0.02
% 2.86/1.46  MUC search           : 0.00
% 2.86/1.46  Cooper               : 0.00
% 2.86/1.46  Total                : 0.73
% 2.86/1.46  Index Insertion      : 0.00
% 2.86/1.46  Index Deletion       : 0.00
% 2.86/1.46  Index Matching       : 0.00
% 2.86/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
