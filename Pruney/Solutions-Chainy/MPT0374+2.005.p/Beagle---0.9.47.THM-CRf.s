%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:59 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 210 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 464 expanded)
%              Number of equality atoms :   15 (  64 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_292,plain,(
    ! [B_65,A_66] :
      ( v1_xboole_0(B_65)
      | ~ m1_subset_1(B_65,A_66)
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_303,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_292])).

tff(c_305,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_432,plain,(
    ! [A_92,B_93,C_94] :
      ( k4_xboole_0(k2_tarski(A_92,B_93),C_94) = k1_xboole_0
      | ~ r2_hidden(B_93,C_94)
      | ~ r2_hidden(A_92,C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_86])).

tff(c_99,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_44,plain,(
    m1_subset_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_179,plain,(
    ! [A_58,B_59,C_60] :
      ( k4_xboole_0(k2_tarski(A_58,B_59),C_60) = k1_xboole_0
      | ~ r2_hidden(B_59,C_60)
      | ~ r2_hidden(A_58,C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    ! [B_25,A_26] :
      ( m1_subset_1(B_25,A_26)
      | ~ v1_xboole_0(B_25)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ~ m1_subset_1(k2_tarski('#skF_5','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_58,plain,
    ( ~ v1_xboole_0(k2_tarski('#skF_5','#skF_6'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_40])).

tff(c_60,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_16,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_160,plain,(
    ! [C_56,A_57] :
      ( m1_subset_1(C_56,k1_zfmisc_1(A_57))
      | v1_xboole_0(k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_56,A_57) ) ),
    inference(resolution,[status(thm)],[c_16,c_115])).

tff(c_169,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_160,c_40])).

tff(c_174,plain,(
    ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_169])).

tff(c_178,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_174])).

tff(c_196,plain,
    ( ~ r2_hidden('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_178])).

tff(c_200,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_203,plain,
    ( ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_200])).

tff(c_206,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_203])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_206])).

tff(c_209,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_241,plain,
    ( ~ m1_subset_1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_209])).

tff(c_244,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_241])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_244])).

tff(c_248,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_255,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_248,c_6])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_255])).

tff(c_261,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_265,plain,(
    k1_zfmisc_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_261,c_6])).

tff(c_266,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_261])).

tff(c_318,plain,(
    ! [C_70,A_71] :
      ( r2_hidden(C_70,k1_zfmisc_1(A_71))
      | ~ r1_tarski(C_70,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_330,plain,(
    ! [A_72,C_73] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_72))
      | ~ r1_tarski(C_73,A_72) ) ),
    inference(resolution,[status(thm)],[c_318,c_2])).

tff(c_332,plain,(
    ! [C_73] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(C_73,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_330])).

tff(c_336,plain,(
    ! [C_74] : ~ r1_tarski(C_74,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_332])).

tff(c_341,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_336])).

tff(c_452,plain,(
    ! [B_93,A_92] :
      ( ~ r2_hidden(B_93,'#skF_4')
      | ~ r2_hidden(A_92,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_341])).

tff(c_455,plain,(
    ! [A_95] : ~ r2_hidden(A_95,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_452])).

tff(c_463,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_455])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_463])).

tff(c_472,plain,(
    ! [B_96] : ~ r2_hidden(B_96,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_480,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_472])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_480])).

tff(c_489,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_497,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_489,c_6])).

tff(c_501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_497])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.43/1.38  
% 2.43/1.38  %Foreground sorts:
% 2.43/1.38  
% 2.43/1.38  
% 2.43/1.38  %Background operators:
% 2.43/1.38  
% 2.43/1.38  
% 2.43/1.38  %Foreground operators:
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.43/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.43/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.43/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.43/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.43/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.38  
% 2.43/1.39  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_subset_1)).
% 2.43/1.39  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.43/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.43/1.39  tff(f_54, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 2.43/1.39  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.43/1.39  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.43/1.39  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.43/1.39  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.43/1.39  tff(c_46, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.43/1.39  tff(c_292, plain, (![B_65, A_66]: (v1_xboole_0(B_65) | ~m1_subset_1(B_65, A_66) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.39  tff(c_303, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_292])).
% 2.43/1.39  tff(c_305, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_303])).
% 2.43/1.39  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.39  tff(c_432, plain, (![A_92, B_93, C_94]: (k4_xboole_0(k2_tarski(A_92, B_93), C_94)=k1_xboole_0 | ~r2_hidden(B_93, C_94) | ~r2_hidden(A_92, C_94))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.43/1.39  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.39  tff(c_86, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.39  tff(c_97, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_86])).
% 2.43/1.39  tff(c_99, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_97])).
% 2.43/1.39  tff(c_44, plain, (m1_subset_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.43/1.39  tff(c_34, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.39  tff(c_179, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k2_tarski(A_58, B_59), C_60)=k1_xboole_0 | ~r2_hidden(B_59, C_60) | ~r2_hidden(A_58, C_60))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.43/1.39  tff(c_54, plain, (![B_25, A_26]: (m1_subset_1(B_25, A_26) | ~v1_xboole_0(B_25) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.39  tff(c_40, plain, (~m1_subset_1(k2_tarski('#skF_5', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.43/1.39  tff(c_58, plain, (~v1_xboole_0(k2_tarski('#skF_5', '#skF_6')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_40])).
% 2.43/1.39  tff(c_60, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_58])).
% 2.43/1.39  tff(c_16, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.43/1.39  tff(c_115, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.39  tff(c_160, plain, (![C_56, A_57]: (m1_subset_1(C_56, k1_zfmisc_1(A_57)) | v1_xboole_0(k1_zfmisc_1(A_57)) | ~r1_tarski(C_56, A_57))), inference(resolution, [status(thm)], [c_16, c_115])).
% 2.43/1.39  tff(c_169, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_160, c_40])).
% 2.43/1.39  tff(c_174, plain, (~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_169])).
% 2.43/1.39  tff(c_178, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_174])).
% 2.43/1.39  tff(c_196, plain, (~r2_hidden('#skF_6', '#skF_4') | ~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_179, c_178])).
% 2.43/1.39  tff(c_200, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_196])).
% 2.43/1.39  tff(c_203, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_200])).
% 2.43/1.39  tff(c_206, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_203])).
% 2.43/1.39  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_206])).
% 2.43/1.39  tff(c_209, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_196])).
% 2.43/1.39  tff(c_241, plain, (~m1_subset_1('#skF_6', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_209])).
% 2.43/1.39  tff(c_244, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_241])).
% 2.43/1.39  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_244])).
% 2.43/1.39  tff(c_248, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_97])).
% 2.43/1.39  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.39  tff(c_255, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_248, c_6])).
% 2.43/1.39  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_255])).
% 2.43/1.39  tff(c_261, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 2.43/1.39  tff(c_265, plain, (k1_zfmisc_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_261, c_6])).
% 2.43/1.39  tff(c_266, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_265, c_261])).
% 2.43/1.39  tff(c_318, plain, (![C_70, A_71]: (r2_hidden(C_70, k1_zfmisc_1(A_71)) | ~r1_tarski(C_70, A_71))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.43/1.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.39  tff(c_330, plain, (![A_72, C_73]: (~v1_xboole_0(k1_zfmisc_1(A_72)) | ~r1_tarski(C_73, A_72))), inference(resolution, [status(thm)], [c_318, c_2])).
% 2.43/1.39  tff(c_332, plain, (![C_73]: (~v1_xboole_0(k1_xboole_0) | ~r1_tarski(C_73, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_265, c_330])).
% 2.43/1.39  tff(c_336, plain, (![C_74]: (~r1_tarski(C_74, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_332])).
% 2.43/1.39  tff(c_341, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_336])).
% 2.43/1.39  tff(c_452, plain, (![B_93, A_92]: (~r2_hidden(B_93, '#skF_4') | ~r2_hidden(A_92, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_341])).
% 2.43/1.39  tff(c_455, plain, (![A_95]: (~r2_hidden(A_95, '#skF_4'))), inference(splitLeft, [status(thm)], [c_452])).
% 2.43/1.39  tff(c_463, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_455])).
% 2.43/1.39  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_463])).
% 2.43/1.39  tff(c_472, plain, (![B_96]: (~r2_hidden(B_96, '#skF_4'))), inference(splitRight, [status(thm)], [c_452])).
% 2.43/1.39  tff(c_480, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_472])).
% 2.43/1.39  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_480])).
% 2.43/1.39  tff(c_489, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_303])).
% 2.43/1.39  tff(c_497, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_489, c_6])).
% 2.43/1.39  tff(c_501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_497])).
% 2.43/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.39  
% 2.43/1.39  Inference rules
% 2.43/1.39  ----------------------
% 2.43/1.39  #Ref     : 0
% 2.43/1.39  #Sup     : 86
% 2.43/1.39  #Fact    : 0
% 2.43/1.39  #Define  : 0
% 2.43/1.39  #Split   : 6
% 2.43/1.39  #Chain   : 0
% 2.43/1.39  #Close   : 0
% 2.43/1.39  
% 2.43/1.39  Ordering : KBO
% 2.43/1.39  
% 2.43/1.39  Simplification rules
% 2.43/1.39  ----------------------
% 2.43/1.39  #Subsume      : 7
% 2.43/1.39  #Demod        : 18
% 2.43/1.39  #Tautology    : 42
% 2.43/1.39  #SimpNegUnit  : 14
% 2.43/1.39  #BackRed      : 3
% 2.43/1.39  
% 2.43/1.39  #Partial instantiations: 0
% 2.43/1.39  #Strategies tried      : 1
% 2.43/1.39  
% 2.43/1.39  Timing (in seconds)
% 2.43/1.39  ----------------------
% 2.43/1.40  Preprocessing        : 0.32
% 2.43/1.40  Parsing              : 0.17
% 2.43/1.40  CNF conversion       : 0.02
% 2.43/1.40  Main loop            : 0.24
% 2.43/1.40  Inferencing          : 0.10
% 2.43/1.40  Reduction            : 0.06
% 2.43/1.40  Demodulation         : 0.04
% 2.43/1.40  BG Simplification    : 0.01
% 2.43/1.40  Subsumption          : 0.04
% 2.43/1.40  Abstraction          : 0.01
% 2.43/1.40  MUC search           : 0.00
% 2.43/1.40  Cooper               : 0.00
% 2.43/1.40  Total                : 0.60
% 2.43/1.40  Index Insertion      : 0.00
% 2.43/1.40  Index Deletion       : 0.00
% 2.43/1.40  Index Matching       : 0.00
% 2.43/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
