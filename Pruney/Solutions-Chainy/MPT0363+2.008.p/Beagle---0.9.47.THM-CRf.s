%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:37 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   61 (  76 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   72 ( 116 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_99,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_100,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_129,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k3_subset_1(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_139,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_129])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_215,plain,(
    ! [A_46] :
      ( r1_xboole_0(A_46,'#skF_3')
      | ~ r1_tarski(A_46,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_6])).

tff(c_218,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_215])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_218])).

tff(c_227,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_227])).

tff(c_231,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_290,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_300,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_290])).

tff(c_373,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,k4_xboole_0(B_68,C_69))
      | ~ r1_xboole_0(A_67,C_69)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_406,plain,(
    ! [A_71] :
      ( r1_tarski(A_71,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_71,'#skF_3')
      | ~ r1_tarski(A_71,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_373])).

tff(c_230,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_417,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_406,c_230])).

tff(c_423,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_417])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_12] : k1_subset_1(A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_subset_1(A_16)) = k2_subset_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_37,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_subset_1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_38,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_37])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_424,plain,(
    ! [C_72,A_73,B_74] :
      ( r1_tarski(C_72,k3_subset_1(A_73,B_74))
      | ~ r1_tarski(B_74,k3_subset_1(A_73,C_72))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_433,plain,(
    ! [C_72,A_73] :
      ( r1_tarski(C_72,k3_subset_1(A_73,k1_xboole_0))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_10,c_424])).

tff(c_445,plain,(
    ! [C_75,A_76] :
      ( r1_tarski(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_76)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_38,c_433])).

tff(c_454,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_445])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_423,c_454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:07:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.37  
% 2.42/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.38  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.42/1.38  
% 2.42/1.38  %Foreground sorts:
% 2.42/1.38  
% 2.42/1.38  
% 2.42/1.38  %Background operators:
% 2.42/1.38  
% 2.42/1.38  
% 2.42/1.38  %Foreground operators:
% 2.42/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.42/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.42/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.38  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.42/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.42/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.38  
% 2.42/1.39  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.42/1.39  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.42/1.39  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.42/1.39  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.42/1.39  tff(f_64, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.42/1.39  tff(f_45, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.42/1.39  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.42/1.39  tff(f_53, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.42/1.39  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.42/1.39  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.42/1.39  tff(c_30, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.42/1.39  tff(c_99, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.42/1.39  tff(c_36, plain, (r1_xboole_0('#skF_2', '#skF_3') | r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.42/1.39  tff(c_100, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.42/1.39  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.42/1.39  tff(c_129, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k3_subset_1(A_38, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.42/1.39  tff(c_139, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_129])).
% 2.42/1.39  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.39  tff(c_215, plain, (![A_46]: (r1_xboole_0(A_46, '#skF_3') | ~r1_tarski(A_46, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_139, c_6])).
% 2.42/1.39  tff(c_218, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_100, c_215])).
% 2.42/1.39  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_218])).
% 2.42/1.39  tff(c_227, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.42/1.39  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_227])).
% 2.42/1.39  tff(c_231, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.42/1.39  tff(c_290, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.42/1.39  tff(c_300, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_290])).
% 2.42/1.39  tff(c_373, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, k4_xboole_0(B_68, C_69)) | ~r1_xboole_0(A_67, C_69) | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.42/1.39  tff(c_406, plain, (![A_71]: (r1_tarski(A_71, k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_71, '#skF_3') | ~r1_tarski(A_71, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_300, c_373])).
% 2.42/1.39  tff(c_230, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 2.42/1.39  tff(c_417, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_406, c_230])).
% 2.42/1.39  tff(c_423, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_417])).
% 2.42/1.39  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.42/1.39  tff(c_24, plain, (![A_21]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.42/1.39  tff(c_14, plain, (![A_12]: (k1_subset_1(A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.42/1.39  tff(c_16, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.39  tff(c_20, plain, (![A_16]: (k3_subset_1(A_16, k1_subset_1(A_16))=k2_subset_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.42/1.39  tff(c_37, plain, (![A_16]: (k3_subset_1(A_16, k1_subset_1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 2.42/1.39  tff(c_38, plain, (![A_16]: (k3_subset_1(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_37])).
% 2.42/1.39  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.39  tff(c_424, plain, (![C_72, A_73, B_74]: (r1_tarski(C_72, k3_subset_1(A_73, B_74)) | ~r1_tarski(B_74, k3_subset_1(A_73, C_72)) | ~m1_subset_1(C_72, k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.42/1.39  tff(c_433, plain, (![C_72, A_73]: (r1_tarski(C_72, k3_subset_1(A_73, k1_xboole_0)) | ~m1_subset_1(C_72, k1_zfmisc_1(A_73)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_73)))), inference(resolution, [status(thm)], [c_10, c_424])).
% 2.42/1.39  tff(c_445, plain, (![C_75, A_76]: (r1_tarski(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_38, c_433])).
% 2.42/1.39  tff(c_454, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_445])).
% 2.42/1.39  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_423, c_454])).
% 2.42/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.39  
% 2.42/1.39  Inference rules
% 2.42/1.39  ----------------------
% 2.42/1.39  #Ref     : 0
% 2.42/1.39  #Sup     : 97
% 2.42/1.39  #Fact    : 0
% 2.42/1.39  #Define  : 0
% 2.42/1.39  #Split   : 2
% 2.42/1.39  #Chain   : 0
% 2.42/1.39  #Close   : 0
% 2.42/1.39  
% 2.42/1.39  Ordering : KBO
% 2.42/1.39  
% 2.42/1.39  Simplification rules
% 2.42/1.39  ----------------------
% 2.42/1.39  #Subsume      : 3
% 2.42/1.39  #Demod        : 27
% 2.42/1.39  #Tautology    : 66
% 2.42/1.39  #SimpNegUnit  : 4
% 2.42/1.39  #BackRed      : 0
% 2.42/1.39  
% 2.42/1.39  #Partial instantiations: 0
% 2.42/1.39  #Strategies tried      : 1
% 2.42/1.39  
% 2.42/1.39  Timing (in seconds)
% 2.42/1.39  ----------------------
% 2.42/1.39  Preprocessing        : 0.32
% 2.42/1.39  Parsing              : 0.18
% 2.42/1.39  CNF conversion       : 0.02
% 2.42/1.39  Main loop            : 0.24
% 2.42/1.39  Inferencing          : 0.09
% 2.42/1.39  Reduction            : 0.08
% 2.42/1.39  Demodulation         : 0.06
% 2.42/1.39  BG Simplification    : 0.01
% 2.42/1.39  Subsumption          : 0.03
% 2.42/1.39  Abstraction          : 0.01
% 2.42/1.39  MUC search           : 0.00
% 2.42/1.39  Cooper               : 0.00
% 2.42/1.39  Total                : 0.59
% 2.42/1.39  Index Insertion      : 0.00
% 2.42/1.39  Index Deletion       : 0.00
% 2.42/1.39  Index Matching       : 0.00
% 2.42/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
