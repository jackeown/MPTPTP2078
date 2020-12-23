%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:09 EST 2020

% Result     : Theorem 46.53s
% Output     : CNFRefutation 46.53s
% Verified   : 
% Statistics : Number of formulae       :   61 (  82 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 106 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_100,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_110,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_102,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_98,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_185,plain,(
    ! [A_74,B_75] :
      ( r1_xboole_0(A_74,B_75)
      | k3_xboole_0(A_74,B_75) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_197,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_185,c_58])).

tff(c_38,plain,(
    ! [A_35] : r1_tarski(k1_xboole_0,A_35) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_94,plain,(
    ! [A_60,B_61] :
      ( k2_xboole_0(A_60,B_61) = B_61
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_105,plain,(
    ! [A_35] : k2_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(resolution,[status(thm)],[c_38,c_94])).

tff(c_44,plain,(
    ! [A_42] : r1_xboole_0(A_42,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_224,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = k1_xboole_0
      | ~ r1_xboole_0(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_244,plain,(
    ! [A_42] : k3_xboole_0(A_42,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_224])).

tff(c_2029,plain,(
    ! [A_167,B_168,C_169] : r1_tarski(k2_xboole_0(k3_xboole_0(A_167,B_168),k3_xboole_0(A_167,C_169)),k2_xboole_0(B_168,C_169)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2089,plain,(
    ! [A_42,C_169] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(A_42,C_169)),k2_xboole_0(k1_xboole_0,C_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_2029])).

tff(c_2132,plain,(
    ! [A_42,C_169] : r1_tarski(k3_xboole_0(A_42,C_169),C_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_105,c_2089])).

tff(c_28,plain,(
    ! [A_22,B_23] : r1_tarski(k3_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_199,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_221,plain,(
    ! [A_22,B_23] : k3_xboole_0(k3_xboole_0(A_22,B_23),A_22) = k3_xboole_0(A_22,B_23) ),
    inference(resolution,[status(thm)],[c_28,c_199])).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_106,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_94])).

tff(c_36,plain,(
    ! [A_32,B_33,C_34] : r1_tarski(k3_xboole_0(A_32,B_33),k2_xboole_0(A_32,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4125,plain,(
    ! [A_233,B_234,C_235] : k3_xboole_0(k3_xboole_0(A_233,B_234),k2_xboole_0(A_233,C_235)) = k3_xboole_0(A_233,B_234) ),
    inference(resolution,[status(thm)],[c_36,c_199])).

tff(c_32,plain,(
    ! [A_27,C_29,B_28] :
      ( r1_tarski(k3_xboole_0(A_27,C_29),k3_xboole_0(B_28,C_29))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_221217,plain,(
    ! [A_13151,B_13152,B_13153,C_13154] :
      ( r1_tarski(k3_xboole_0(A_13151,B_13152),k3_xboole_0(B_13153,k2_xboole_0(A_13151,C_13154)))
      | ~ r1_tarski(k3_xboole_0(A_13151,B_13152),B_13153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4125,c_32])).

tff(c_232099,plain,(
    ! [B_13416,B_13417] :
      ( r1_tarski(k3_xboole_0('#skF_3',B_13416),k3_xboole_0(B_13417,'#skF_5'))
      | ~ r1_tarski(k3_xboole_0('#skF_3',B_13416),B_13417) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_221217])).

tff(c_54,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_72,plain,(
    ! [B_57,A_58] :
      ( r1_xboole_0(B_57,A_58)
      | ~ r1_xboole_0(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_77,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_72])).

tff(c_241,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_224])).

tff(c_1730,plain,(
    ! [A_155,C_156,B_157] :
      ( r1_tarski(k3_xboole_0(A_155,C_156),k3_xboole_0(B_157,C_156))
      | ~ r1_tarski(A_155,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8179,plain,(
    ! [A_301,C_302,B_303] :
      ( k3_xboole_0(k3_xboole_0(A_301,C_302),k3_xboole_0(B_303,C_302)) = k3_xboole_0(A_301,C_302)
      | ~ r1_tarski(A_301,B_303) ) ),
    inference(resolution,[status(thm)],[c_1730,c_34])).

tff(c_8480,plain,(
    ! [A_301] :
      ( k3_xboole_0(k3_xboole_0(A_301,'#skF_3'),k1_xboole_0) = k3_xboole_0(A_301,'#skF_3')
      | ~ r1_tarski(A_301,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_8179])).

tff(c_8554,plain,(
    ! [A_301] :
      ( k3_xboole_0(A_301,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_301,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_8480])).

tff(c_232131,plain,(
    ! [B_13416] :
      ( k3_xboole_0(k3_xboole_0('#skF_3',B_13416),'#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0('#skF_3',B_13416),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_232099,c_8554])).

tff(c_240093,plain,(
    ! [B_13709] :
      ( k3_xboole_0('#skF_3',B_13709) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0('#skF_3',B_13709),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_232131])).

tff(c_240324,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2132,c_240093])).

tff(c_240424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_240324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 46.53/36.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.53/36.05  
% 46.53/36.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.53/36.05  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 46.53/36.05  
% 46.53/36.05  %Foreground sorts:
% 46.53/36.05  
% 46.53/36.05  
% 46.53/36.05  %Background operators:
% 46.53/36.05  
% 46.53/36.05  
% 46.53/36.05  %Foreground operators:
% 46.53/36.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 46.53/36.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 46.53/36.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 46.53/36.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 46.53/36.05  tff('#skF_5', type, '#skF_5': $i).
% 46.53/36.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 46.53/36.05  tff('#skF_3', type, '#skF_3': $i).
% 46.53/36.05  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 46.53/36.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 46.53/36.05  tff('#skF_4', type, '#skF_4': $i).
% 46.53/36.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 46.53/36.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 46.53/36.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 46.53/36.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 46.53/36.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 46.53/36.05  
% 46.53/36.07  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 46.53/36.07  tff(f_143, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 46.53/36.07  tff(f_100, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 46.53/36.07  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 46.53/36.07  tff(f_110, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 46.53/36.07  tff(f_102, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 46.53/36.07  tff(f_82, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 46.53/36.07  tff(f_96, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 46.53/36.07  tff(f_98, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 46.53/36.07  tff(f_92, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_xboole_1)).
% 46.53/36.07  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 46.53/36.07  tff(c_185, plain, (![A_74, B_75]: (r1_xboole_0(A_74, B_75) | k3_xboole_0(A_74, B_75)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 46.53/36.07  tff(c_58, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 46.53/36.07  tff(c_197, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_185, c_58])).
% 46.53/36.07  tff(c_38, plain, (![A_35]: (r1_tarski(k1_xboole_0, A_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 46.53/36.07  tff(c_94, plain, (![A_60, B_61]: (k2_xboole_0(A_60, B_61)=B_61 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_80])).
% 46.53/36.07  tff(c_105, plain, (![A_35]: (k2_xboole_0(k1_xboole_0, A_35)=A_35)), inference(resolution, [status(thm)], [c_38, c_94])).
% 46.53/36.07  tff(c_44, plain, (![A_42]: (r1_xboole_0(A_42, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_110])).
% 46.53/36.07  tff(c_224, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=k1_xboole_0 | ~r1_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 46.53/36.07  tff(c_244, plain, (![A_42]: (k3_xboole_0(A_42, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_224])).
% 46.53/36.07  tff(c_2029, plain, (![A_167, B_168, C_169]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_167, B_168), k3_xboole_0(A_167, C_169)), k2_xboole_0(B_168, C_169)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 46.53/36.07  tff(c_2089, plain, (![A_42, C_169]: (r1_tarski(k2_xboole_0(k1_xboole_0, k3_xboole_0(A_42, C_169)), k2_xboole_0(k1_xboole_0, C_169)))), inference(superposition, [status(thm), theory('equality')], [c_244, c_2029])).
% 46.53/36.07  tff(c_2132, plain, (![A_42, C_169]: (r1_tarski(k3_xboole_0(A_42, C_169), C_169))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_105, c_2089])).
% 46.53/36.07  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(k3_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 46.53/36.07  tff(c_199, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_96])).
% 46.53/36.07  tff(c_221, plain, (![A_22, B_23]: (k3_xboole_0(k3_xboole_0(A_22, B_23), A_22)=k3_xboole_0(A_22, B_23))), inference(resolution, [status(thm)], [c_28, c_199])).
% 46.53/36.07  tff(c_56, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 46.53/36.07  tff(c_106, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_56, c_94])).
% 46.53/36.07  tff(c_36, plain, (![A_32, B_33, C_34]: (r1_tarski(k3_xboole_0(A_32, B_33), k2_xboole_0(A_32, C_34)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 46.53/36.07  tff(c_4125, plain, (![A_233, B_234, C_235]: (k3_xboole_0(k3_xboole_0(A_233, B_234), k2_xboole_0(A_233, C_235))=k3_xboole_0(A_233, B_234))), inference(resolution, [status(thm)], [c_36, c_199])).
% 46.53/36.07  tff(c_32, plain, (![A_27, C_29, B_28]: (r1_tarski(k3_xboole_0(A_27, C_29), k3_xboole_0(B_28, C_29)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_92])).
% 46.53/36.07  tff(c_221217, plain, (![A_13151, B_13152, B_13153, C_13154]: (r1_tarski(k3_xboole_0(A_13151, B_13152), k3_xboole_0(B_13153, k2_xboole_0(A_13151, C_13154))) | ~r1_tarski(k3_xboole_0(A_13151, B_13152), B_13153))), inference(superposition, [status(thm), theory('equality')], [c_4125, c_32])).
% 46.53/36.07  tff(c_232099, plain, (![B_13416, B_13417]: (r1_tarski(k3_xboole_0('#skF_3', B_13416), k3_xboole_0(B_13417, '#skF_5')) | ~r1_tarski(k3_xboole_0('#skF_3', B_13416), B_13417))), inference(superposition, [status(thm), theory('equality')], [c_106, c_221217])).
% 46.53/36.07  tff(c_54, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 46.53/36.07  tff(c_72, plain, (![B_57, A_58]: (r1_xboole_0(B_57, A_58) | ~r1_xboole_0(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_40])).
% 46.53/36.07  tff(c_77, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_54, c_72])).
% 46.53/36.07  tff(c_241, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_77, c_224])).
% 46.53/36.07  tff(c_1730, plain, (![A_155, C_156, B_157]: (r1_tarski(k3_xboole_0(A_155, C_156), k3_xboole_0(B_157, C_156)) | ~r1_tarski(A_155, B_157))), inference(cnfTransformation, [status(thm)], [f_92])).
% 46.53/36.07  tff(c_34, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_96])).
% 46.53/36.07  tff(c_8179, plain, (![A_301, C_302, B_303]: (k3_xboole_0(k3_xboole_0(A_301, C_302), k3_xboole_0(B_303, C_302))=k3_xboole_0(A_301, C_302) | ~r1_tarski(A_301, B_303))), inference(resolution, [status(thm)], [c_1730, c_34])).
% 46.53/36.07  tff(c_8480, plain, (![A_301]: (k3_xboole_0(k3_xboole_0(A_301, '#skF_3'), k1_xboole_0)=k3_xboole_0(A_301, '#skF_3') | ~r1_tarski(A_301, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_241, c_8179])).
% 46.53/36.07  tff(c_8554, plain, (![A_301]: (k3_xboole_0(A_301, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_301, k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_8480])).
% 46.53/36.07  tff(c_232131, plain, (![B_13416]: (k3_xboole_0(k3_xboole_0('#skF_3', B_13416), '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_xboole_0('#skF_3', B_13416), '#skF_4'))), inference(resolution, [status(thm)], [c_232099, c_8554])).
% 46.53/36.07  tff(c_240093, plain, (![B_13709]: (k3_xboole_0('#skF_3', B_13709)=k1_xboole_0 | ~r1_tarski(k3_xboole_0('#skF_3', B_13709), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_232131])).
% 46.53/36.07  tff(c_240324, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2132, c_240093])).
% 46.53/36.07  tff(c_240424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_240324])).
% 46.53/36.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.53/36.07  
% 46.53/36.07  Inference rules
% 46.53/36.07  ----------------------
% 46.53/36.07  #Ref     : 0
% 46.53/36.07  #Sup     : 50616
% 46.53/36.07  #Fact    : 2
% 46.53/36.07  #Define  : 0
% 46.53/36.07  #Split   : 16
% 46.53/36.07  #Chain   : 0
% 46.53/36.07  #Close   : 0
% 46.53/36.07  
% 46.53/36.07  Ordering : KBO
% 46.53/36.07  
% 46.53/36.07  Simplification rules
% 46.53/36.07  ----------------------
% 46.53/36.07  #Subsume      : 16256
% 46.53/36.07  #Demod        : 30991
% 46.53/36.07  #Tautology    : 19508
% 46.53/36.07  #SimpNegUnit  : 1095
% 46.53/36.07  #BackRed      : 66
% 46.53/36.07  
% 46.53/36.07  #Partial instantiations: 12160
% 46.53/36.07  #Strategies tried      : 1
% 46.53/36.07  
% 46.53/36.07  Timing (in seconds)
% 46.53/36.07  ----------------------
% 46.64/36.07  Preprocessing        : 0.38
% 46.64/36.07  Parsing              : 0.20
% 46.64/36.07  CNF conversion       : 0.03
% 46.64/36.07  Main loop            : 34.88
% 46.64/36.07  Inferencing          : 3.37
% 46.64/36.07  Reduction            : 18.85
% 46.64/36.07  Demodulation         : 15.53
% 46.64/36.07  BG Simplification    : 0.35
% 46.64/36.07  Subsumption          : 11.10
% 46.64/36.07  Abstraction          : 0.53
% 46.64/36.07  MUC search           : 0.00
% 46.64/36.07  Cooper               : 0.00
% 46.64/36.07  Total                : 35.29
% 46.64/36.07  Index Insertion      : 0.00
% 46.64/36.07  Index Deletion       : 0.00
% 46.64/36.07  Index Matching       : 0.00
% 46.64/36.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
