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
% DateTime   : Thu Dec  3 09:57:00 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 107 expanded)
%              Number of leaves         :   28 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 261 expanded)
%              Number of equality atoms :   25 (  70 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ! [D] :
                ( m1_subset_1(D,A)
               => ( A != k1_xboole_0
                 => m1_subset_1(k1_enumset1(B,C,D),k1_zfmisc_1(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( m1_subset_1(C,A)
         => ( A != k1_xboole_0
           => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_28,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    m1_subset_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    ! [B_39,C_41,A_38] :
      ( m1_subset_1(k2_tarski(B_39,C_41),k1_zfmisc_1(A_38))
      | k1_xboole_0 = A_38
      | ~ m1_subset_1(C_41,A_38)
      | ~ m1_subset_1(B_39,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_167,plain,(
    ! [B_68,C_69,A_70] :
      ( m1_subset_1(k2_tarski(B_68,C_69),k1_zfmisc_1(A_70))
      | k1_xboole_0 = A_70
      | ~ m1_subset_1(C_69,A_70)
      | ~ m1_subset_1(B_68,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_170,plain,(
    ! [A_4,A_70] :
      ( m1_subset_1(k1_tarski(A_4),k1_zfmisc_1(A_70))
      | k1_xboole_0 = A_70
      | ~ m1_subset_1(A_4,A_70)
      | ~ m1_subset_1(A_4,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_167])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k1_tarski(A_1),k2_tarski(B_2,C_3)) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_172,plain,(
    ! [A_73,B_74,C_75] :
      ( k4_subset_1(A_73,B_74,C_75) = k2_xboole_0(B_74,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_224,plain,(
    ! [A_98,B_99,B_100,C_101] :
      ( k4_subset_1(A_98,B_99,k2_tarski(B_100,C_101)) = k2_xboole_0(B_99,k2_tarski(B_100,C_101))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98))
      | k1_xboole_0 = A_98
      | ~ m1_subset_1(C_101,A_98)
      | ~ m1_subset_1(B_100,A_98) ) ),
    inference(resolution,[status(thm)],[c_24,c_172])).

tff(c_228,plain,(
    ! [A_70,A_4,B_100,C_101] :
      ( k4_subset_1(A_70,k1_tarski(A_4),k2_tarski(B_100,C_101)) = k2_xboole_0(k1_tarski(A_4),k2_tarski(B_100,C_101))
      | ~ m1_subset_1(C_101,A_70)
      | ~ m1_subset_1(B_100,A_70)
      | k1_xboole_0 = A_70
      | ~ m1_subset_1(A_4,A_70) ) ),
    inference(resolution,[status(thm)],[c_170,c_224])).

tff(c_246,plain,(
    ! [A_106,A_107,B_108,C_109] :
      ( k4_subset_1(A_106,k1_tarski(A_107),k2_tarski(B_108,C_109)) = k1_enumset1(A_107,B_108,C_109)
      | ~ m1_subset_1(C_109,A_106)
      | ~ m1_subset_1(B_108,A_106)
      | k1_xboole_0 = A_106
      | ~ m1_subset_1(A_107,A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_228])).

tff(c_20,plain,(
    ! [A_32,B_33,C_34] :
      ( m1_subset_1(k4_subset_1(A_32,B_33,C_34),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_714,plain,(
    ! [A_164,B_165,C_166,A_167] :
      ( m1_subset_1(k1_enumset1(A_164,B_165,C_166),k1_zfmisc_1(A_167))
      | ~ m1_subset_1(k2_tarski(B_165,C_166),k1_zfmisc_1(A_167))
      | ~ m1_subset_1(k1_tarski(A_164),k1_zfmisc_1(A_167))
      | ~ m1_subset_1(C_166,A_167)
      | ~ m1_subset_1(B_165,A_167)
      | k1_xboole_0 = A_167
      | ~ m1_subset_1(A_164,A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_20])).

tff(c_26,plain,(
    ~ m1_subset_1(k1_enumset1('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_727,plain,
    ( ~ m1_subset_1(k2_tarski('#skF_3','#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_714,c_26])).

tff(c_744,plain,
    ( ~ m1_subset_1(k2_tarski('#skF_3','#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_727])).

tff(c_745,plain,
    ( ~ m1_subset_1(k2_tarski('#skF_3','#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_744])).

tff(c_749,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_745])).

tff(c_752,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_170,c_749])).

tff(c_755,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_752])).

tff(c_757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_755])).

tff(c_758,plain,(
    ~ m1_subset_1(k2_tarski('#skF_3','#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_783,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_4','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_758])).

tff(c_786,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_783])).

tff(c_788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:02:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.54  
% 3.01/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.54  %$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.01/1.54  
% 3.01/1.54  %Foreground sorts:
% 3.01/1.54  
% 3.01/1.54  
% 3.01/1.54  %Background operators:
% 3.01/1.54  
% 3.01/1.54  
% 3.01/1.54  %Foreground operators:
% 3.01/1.54  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.01/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.01/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.01/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.01/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.01/1.54  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.01/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.01/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.01/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.01/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.01/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.54  
% 3.01/1.55  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_enumset1(B, C, D), k1_zfmisc_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_subset_1)).
% 3.01/1.55  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_subset_1)).
% 3.01/1.55  tff(f_30, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.01/1.55  tff(f_28, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.01/1.55  tff(f_54, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.01/1.55  tff(f_48, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 3.01/1.55  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.55  tff(c_32, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.55  tff(c_30, plain, (m1_subset_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.55  tff(c_24, plain, (![B_39, C_41, A_38]: (m1_subset_1(k2_tarski(B_39, C_41), k1_zfmisc_1(A_38)) | k1_xboole_0=A_38 | ~m1_subset_1(C_41, A_38) | ~m1_subset_1(B_39, A_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.55  tff(c_34, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.55  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.01/1.55  tff(c_167, plain, (![B_68, C_69, A_70]: (m1_subset_1(k2_tarski(B_68, C_69), k1_zfmisc_1(A_70)) | k1_xboole_0=A_70 | ~m1_subset_1(C_69, A_70) | ~m1_subset_1(B_68, A_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.55  tff(c_170, plain, (![A_4, A_70]: (m1_subset_1(k1_tarski(A_4), k1_zfmisc_1(A_70)) | k1_xboole_0=A_70 | ~m1_subset_1(A_4, A_70) | ~m1_subset_1(A_4, A_70))), inference(superposition, [status(thm), theory('equality')], [c_6, c_167])).
% 3.01/1.55  tff(c_4, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k1_tarski(A_1), k2_tarski(B_2, C_3))=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.01/1.55  tff(c_172, plain, (![A_73, B_74, C_75]: (k4_subset_1(A_73, B_74, C_75)=k2_xboole_0(B_74, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.01/1.55  tff(c_224, plain, (![A_98, B_99, B_100, C_101]: (k4_subset_1(A_98, B_99, k2_tarski(B_100, C_101))=k2_xboole_0(B_99, k2_tarski(B_100, C_101)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)) | k1_xboole_0=A_98 | ~m1_subset_1(C_101, A_98) | ~m1_subset_1(B_100, A_98))), inference(resolution, [status(thm)], [c_24, c_172])).
% 3.01/1.55  tff(c_228, plain, (![A_70, A_4, B_100, C_101]: (k4_subset_1(A_70, k1_tarski(A_4), k2_tarski(B_100, C_101))=k2_xboole_0(k1_tarski(A_4), k2_tarski(B_100, C_101)) | ~m1_subset_1(C_101, A_70) | ~m1_subset_1(B_100, A_70) | k1_xboole_0=A_70 | ~m1_subset_1(A_4, A_70))), inference(resolution, [status(thm)], [c_170, c_224])).
% 3.01/1.55  tff(c_246, plain, (![A_106, A_107, B_108, C_109]: (k4_subset_1(A_106, k1_tarski(A_107), k2_tarski(B_108, C_109))=k1_enumset1(A_107, B_108, C_109) | ~m1_subset_1(C_109, A_106) | ~m1_subset_1(B_108, A_106) | k1_xboole_0=A_106 | ~m1_subset_1(A_107, A_106))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_228])).
% 3.01/1.55  tff(c_20, plain, (![A_32, B_33, C_34]: (m1_subset_1(k4_subset_1(A_32, B_33, C_34), k1_zfmisc_1(A_32)) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.01/1.55  tff(c_714, plain, (![A_164, B_165, C_166, A_167]: (m1_subset_1(k1_enumset1(A_164, B_165, C_166), k1_zfmisc_1(A_167)) | ~m1_subset_1(k2_tarski(B_165, C_166), k1_zfmisc_1(A_167)) | ~m1_subset_1(k1_tarski(A_164), k1_zfmisc_1(A_167)) | ~m1_subset_1(C_166, A_167) | ~m1_subset_1(B_165, A_167) | k1_xboole_0=A_167 | ~m1_subset_1(A_164, A_167))), inference(superposition, [status(thm), theory('equality')], [c_246, c_20])).
% 3.01/1.55  tff(c_26, plain, (~m1_subset_1(k1_enumset1('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.55  tff(c_727, plain, (~m1_subset_1(k2_tarski('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_4', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1') | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_714, c_26])).
% 3.01/1.55  tff(c_744, plain, (~m1_subset_1(k2_tarski('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_727])).
% 3.01/1.55  tff(c_745, plain, (~m1_subset_1(k2_tarski('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_28, c_744])).
% 3.01/1.55  tff(c_749, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_745])).
% 3.01/1.55  tff(c_752, plain, (k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_170, c_749])).
% 3.01/1.55  tff(c_755, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_752])).
% 3.01/1.55  tff(c_757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_755])).
% 3.01/1.55  tff(c_758, plain, (~m1_subset_1(k2_tarski('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_745])).
% 3.01/1.55  tff(c_783, plain, (k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_4', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_758])).
% 3.01/1.55  tff(c_786, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_783])).
% 3.01/1.55  tff(c_788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_786])).
% 3.01/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.55  
% 3.01/1.55  Inference rules
% 3.01/1.55  ----------------------
% 3.01/1.55  #Ref     : 0
% 3.01/1.55  #Sup     : 200
% 3.01/1.55  #Fact    : 0
% 3.01/1.55  #Define  : 0
% 3.01/1.55  #Split   : 1
% 3.01/1.55  #Chain   : 0
% 3.01/1.55  #Close   : 0
% 3.01/1.55  
% 3.01/1.55  Ordering : KBO
% 3.01/1.55  
% 3.01/1.55  Simplification rules
% 3.01/1.55  ----------------------
% 3.01/1.55  #Subsume      : 25
% 3.01/1.55  #Demod        : 22
% 3.01/1.55  #Tautology    : 62
% 3.01/1.55  #SimpNegUnit  : 6
% 3.01/1.55  #BackRed      : 0
% 3.01/1.55  
% 3.01/1.55  #Partial instantiations: 0
% 3.01/1.55  #Strategies tried      : 1
% 3.01/1.55  
% 3.01/1.55  Timing (in seconds)
% 3.01/1.55  ----------------------
% 3.01/1.56  Preprocessing        : 0.32
% 3.01/1.56  Parsing              : 0.18
% 3.01/1.56  CNF conversion       : 0.02
% 3.01/1.56  Main loop            : 0.43
% 3.01/1.56  Inferencing          : 0.18
% 3.01/1.56  Reduction            : 0.12
% 3.01/1.56  Demodulation         : 0.09
% 3.01/1.56  BG Simplification    : 0.03
% 3.01/1.56  Subsumption          : 0.07
% 3.01/1.56  Abstraction          : 0.03
% 3.01/1.56  MUC search           : 0.00
% 3.01/1.56  Cooper               : 0.00
% 3.01/1.56  Total                : 0.77
% 3.01/1.56  Index Insertion      : 0.00
% 3.01/1.56  Index Deletion       : 0.00
% 3.01/1.56  Index Matching       : 0.00
% 3.01/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
