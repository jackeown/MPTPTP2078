%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:16 EST 2020

% Result     : Theorem 17.60s
% Output     : CNFRefutation 17.71s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 131 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :   81 ( 146 expanded)
%              Number of equality atoms :   45 ( 100 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_46,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_111,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_135,plain,(
    ! [B_50,A_51] : k3_tarski(k2_tarski(B_50,A_51)) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_111])).

tff(c_34,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_159,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,A_53) = k2_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_34])).

tff(c_175,plain,(
    ! [A_53] : k2_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_12])).

tff(c_254,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_261,plain,(
    ! [B_58] : k4_xboole_0(B_58,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_175])).

tff(c_270,plain,(
    ! [B_58] : k4_xboole_0(B_58,k1_xboole_0) = B_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_261])).

tff(c_421,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k4_xboole_0(B_66,A_65)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_439,plain,(
    ! [B_58] : k5_xboole_0(k1_xboole_0,B_58) = k2_xboole_0(k1_xboole_0,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_421])).

tff(c_445,plain,(
    ! [B_58] : k5_xboole_0(k1_xboole_0,B_58) = B_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_439])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_600,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,k2_xboole_0(C_72,B_73))
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_632,plain,(
    ! [A_74,A_75] :
      ( r1_tarski(A_74,A_75)
      | ~ r1_tarski(A_74,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_600])).

tff(c_637,plain,(
    ! [A_76] : r1_tarski(k1_xboole_0,A_76) ),
    inference(resolution,[status(thm)],[c_6,c_632])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_649,plain,(
    ! [A_76] : k3_xboole_0(k1_xboole_0,A_76) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_637,c_14])).

tff(c_733,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_746,plain,(
    ! [A_76] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_733])).

tff(c_757,plain,(
    ! [A_76] : k4_xboole_0(k1_xboole_0,A_76) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_746])).

tff(c_287,plain,(
    ! [A_60,B_61] : k4_xboole_0(k2_xboole_0(A_60,B_61),B_61) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_310,plain,(
    ! [A_53] : k4_xboole_0(k1_xboole_0,A_53) = k4_xboole_0(A_53,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_287])).

tff(c_761,plain,(
    ! [A_53] : k4_xboole_0(A_53,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_310])).

tff(c_92,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_753,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_733])).

tff(c_876,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_753])).

tff(c_959,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_tarski(k2_tarski(A_104,B_105),C_106)
      | ~ r2_hidden(B_105,C_106)
      | ~ r2_hidden(A_104,C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3756,plain,(
    ! [A_184,B_185,C_186] :
      ( k3_xboole_0(k2_tarski(A_184,B_185),C_186) = k2_tarski(A_184,B_185)
      | ~ r2_hidden(B_185,C_186)
      | ~ r2_hidden(A_184,C_186) ) ),
    inference(resolution,[status(thm)],[c_959,c_14])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3770,plain,(
    ! [A_184,B_185,C_186] :
      ( k5_xboole_0(k2_tarski(A_184,B_185),k2_tarski(A_184,B_185)) = k4_xboole_0(k2_tarski(A_184,B_185),C_186)
      | ~ r2_hidden(B_185,C_186)
      | ~ r2_hidden(A_184,C_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3756,c_8])).

tff(c_39186,plain,(
    ! [A_793,B_794,C_795] :
      ( k4_xboole_0(k2_tarski(A_793,B_794),C_795) = k1_xboole_0
      | ~ r2_hidden(B_794,C_795)
      | ~ r2_hidden(A_793,C_795) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_3770])).

tff(c_16,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_39390,plain,(
    ! [C_795,A_793,B_794] :
      ( k2_xboole_0(C_795,k2_tarski(A_793,B_794)) = k2_xboole_0(C_795,k1_xboole_0)
      | ~ r2_hidden(B_794,C_795)
      | ~ r2_hidden(A_793,C_795) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39186,c_16])).

tff(c_50407,plain,(
    ! [C_968,A_969,B_970] :
      ( k2_xboole_0(C_968,k2_tarski(A_969,B_970)) = C_968
      | ~ r2_hidden(B_970,C_968)
      | ~ r2_hidden(A_969,C_968) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_39390])).

tff(c_141,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_34])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_158,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_42])).

tff(c_51153,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50407,c_158])).

tff(c_51327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_51153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:19:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.60/9.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.60/9.67  
% 17.60/9.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.67/9.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 17.67/9.67  
% 17.67/9.67  %Foreground sorts:
% 17.67/9.67  
% 17.67/9.67  
% 17.67/9.67  %Background operators:
% 17.67/9.67  
% 17.67/9.67  
% 17.67/9.67  %Foreground operators:
% 17.67/9.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.67/9.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.67/9.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.67/9.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.67/9.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.67/9.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.67/9.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.67/9.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.67/9.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.67/9.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.67/9.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.67/9.67  tff('#skF_2', type, '#skF_2': $i).
% 17.67/9.67  tff('#skF_3', type, '#skF_3': $i).
% 17.67/9.67  tff('#skF_1', type, '#skF_1': $i).
% 17.67/9.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.67/9.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.67/9.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.67/9.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.67/9.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.67/9.67  
% 17.71/9.69  tff(f_76, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 17.71/9.69  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 17.71/9.69  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 17.71/9.69  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 17.71/9.69  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 17.71/9.69  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 17.71/9.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.71/9.69  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 17.71/9.69  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.71/9.69  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 17.71/9.69  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 17.71/9.69  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 17.71/9.69  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.71/9.69  tff(c_44, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.71/9.69  tff(c_12, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.71/9.69  tff(c_26, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.71/9.69  tff(c_111, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.71/9.69  tff(c_135, plain, (![B_50, A_51]: (k3_tarski(k2_tarski(B_50, A_51))=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_26, c_111])).
% 17.71/9.69  tff(c_34, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.71/9.69  tff(c_159, plain, (![B_52, A_53]: (k2_xboole_0(B_52, A_53)=k2_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_135, c_34])).
% 17.71/9.69  tff(c_175, plain, (![A_53]: (k2_xboole_0(k1_xboole_0, A_53)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_159, c_12])).
% 17.71/9.69  tff(c_254, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.71/9.69  tff(c_261, plain, (![B_58]: (k4_xboole_0(B_58, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_58))), inference(superposition, [status(thm), theory('equality')], [c_254, c_175])).
% 17.71/9.69  tff(c_270, plain, (![B_58]: (k4_xboole_0(B_58, k1_xboole_0)=B_58)), inference(demodulation, [status(thm), theory('equality')], [c_175, c_261])).
% 17.71/9.69  tff(c_421, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k4_xboole_0(B_66, A_65))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.71/9.69  tff(c_439, plain, (![B_58]: (k5_xboole_0(k1_xboole_0, B_58)=k2_xboole_0(k1_xboole_0, B_58))), inference(superposition, [status(thm), theory('equality')], [c_270, c_421])).
% 17.71/9.69  tff(c_445, plain, (![B_58]: (k5_xboole_0(k1_xboole_0, B_58)=B_58)), inference(demodulation, [status(thm), theory('equality')], [c_175, c_439])).
% 17.71/9.69  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.71/9.69  tff(c_600, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, k2_xboole_0(C_72, B_73)) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.71/9.69  tff(c_632, plain, (![A_74, A_75]: (r1_tarski(A_74, A_75) | ~r1_tarski(A_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_600])).
% 17.71/9.69  tff(c_637, plain, (![A_76]: (r1_tarski(k1_xboole_0, A_76))), inference(resolution, [status(thm)], [c_6, c_632])).
% 17.71/9.69  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.71/9.69  tff(c_649, plain, (![A_76]: (k3_xboole_0(k1_xboole_0, A_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_637, c_14])).
% 17.71/9.69  tff(c_733, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.71/9.69  tff(c_746, plain, (![A_76]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_76))), inference(superposition, [status(thm), theory('equality')], [c_649, c_733])).
% 17.71/9.69  tff(c_757, plain, (![A_76]: (k4_xboole_0(k1_xboole_0, A_76)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_445, c_746])).
% 17.71/9.69  tff(c_287, plain, (![A_60, B_61]: (k4_xboole_0(k2_xboole_0(A_60, B_61), B_61)=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.71/9.69  tff(c_310, plain, (![A_53]: (k4_xboole_0(k1_xboole_0, A_53)=k4_xboole_0(A_53, A_53))), inference(superposition, [status(thm), theory('equality')], [c_175, c_287])).
% 17.71/9.69  tff(c_761, plain, (![A_53]: (k4_xboole_0(A_53, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_757, c_310])).
% 17.71/9.69  tff(c_92, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.71/9.69  tff(c_96, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_92])).
% 17.71/9.69  tff(c_753, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_96, c_733])).
% 17.71/9.69  tff(c_876, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_761, c_753])).
% 17.71/9.69  tff(c_959, plain, (![A_104, B_105, C_106]: (r1_tarski(k2_tarski(A_104, B_105), C_106) | ~r2_hidden(B_105, C_106) | ~r2_hidden(A_104, C_106))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.71/9.69  tff(c_3756, plain, (![A_184, B_185, C_186]: (k3_xboole_0(k2_tarski(A_184, B_185), C_186)=k2_tarski(A_184, B_185) | ~r2_hidden(B_185, C_186) | ~r2_hidden(A_184, C_186))), inference(resolution, [status(thm)], [c_959, c_14])).
% 17.71/9.69  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.71/9.69  tff(c_3770, plain, (![A_184, B_185, C_186]: (k5_xboole_0(k2_tarski(A_184, B_185), k2_tarski(A_184, B_185))=k4_xboole_0(k2_tarski(A_184, B_185), C_186) | ~r2_hidden(B_185, C_186) | ~r2_hidden(A_184, C_186))), inference(superposition, [status(thm), theory('equality')], [c_3756, c_8])).
% 17.71/9.69  tff(c_39186, plain, (![A_793, B_794, C_795]: (k4_xboole_0(k2_tarski(A_793, B_794), C_795)=k1_xboole_0 | ~r2_hidden(B_794, C_795) | ~r2_hidden(A_793, C_795))), inference(demodulation, [status(thm), theory('equality')], [c_876, c_3770])).
% 17.71/9.69  tff(c_16, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.71/9.69  tff(c_39390, plain, (![C_795, A_793, B_794]: (k2_xboole_0(C_795, k2_tarski(A_793, B_794))=k2_xboole_0(C_795, k1_xboole_0) | ~r2_hidden(B_794, C_795) | ~r2_hidden(A_793, C_795))), inference(superposition, [status(thm), theory('equality')], [c_39186, c_16])).
% 17.71/9.69  tff(c_50407, plain, (![C_968, A_969, B_970]: (k2_xboole_0(C_968, k2_tarski(A_969, B_970))=C_968 | ~r2_hidden(B_970, C_968) | ~r2_hidden(A_969, C_968))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_39390])).
% 17.71/9.69  tff(c_141, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_135, c_34])).
% 17.71/9.69  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.71/9.69  tff(c_158, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_42])).
% 17.71/9.69  tff(c_51153, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50407, c_158])).
% 17.71/9.69  tff(c_51327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_51153])).
% 17.71/9.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.71/9.69  
% 17.71/9.69  Inference rules
% 17.71/9.69  ----------------------
% 17.71/9.69  #Ref     : 0
% 17.71/9.69  #Sup     : 12945
% 17.71/9.69  #Fact    : 0
% 17.71/9.69  #Define  : 0
% 17.71/9.69  #Split   : 13
% 17.71/9.69  #Chain   : 0
% 17.71/9.69  #Close   : 0
% 17.71/9.69  
% 17.71/9.69  Ordering : KBO
% 17.71/9.69  
% 17.71/9.69  Simplification rules
% 17.71/9.69  ----------------------
% 17.71/9.69  #Subsume      : 3883
% 17.71/9.69  #Demod        : 13492
% 17.71/9.69  #Tautology    : 4785
% 17.71/9.69  #SimpNegUnit  : 18
% 17.71/9.69  #BackRed      : 26
% 17.71/9.69  
% 17.71/9.69  #Partial instantiations: 0
% 17.71/9.69  #Strategies tried      : 1
% 17.71/9.69  
% 17.71/9.69  Timing (in seconds)
% 17.71/9.69  ----------------------
% 17.71/9.69  Preprocessing        : 0.33
% 17.71/9.69  Parsing              : 0.18
% 17.71/9.69  CNF conversion       : 0.02
% 17.71/9.69  Main loop            : 8.54
% 17.71/9.69  Inferencing          : 1.16
% 17.71/9.69  Reduction            : 4.65
% 17.71/9.69  Demodulation         : 4.19
% 17.71/9.69  BG Simplification    : 0.13
% 17.71/9.69  Subsumption          : 2.25
% 17.71/9.69  Abstraction          : 0.25
% 17.71/9.69  MUC search           : 0.00
% 17.71/9.69  Cooper               : 0.00
% 17.71/9.69  Total                : 8.90
% 17.71/9.69  Index Insertion      : 0.00
% 17.71/9.69  Index Deletion       : 0.00
% 17.71/9.69  Index Matching       : 0.00
% 17.71/9.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
