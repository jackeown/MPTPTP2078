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
% DateTime   : Thu Dec  3 09:56:41 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   51 (  86 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 199 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_29,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_28])).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k3_subset_1(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_32])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,k4_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_26] :
      ( r1_xboole_0(A_26,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_26,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_2])).

tff(c_58,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_29])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_58])).

tff(c_63,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_16,plain,(
    ! [B_17,A_16,C_19] :
      ( r1_tarski(B_17,k3_subset_1(A_16,C_19))
      | ~ r1_xboole_0(B_17,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_130,plain,(
    ! [C_46,A_47,B_48] :
      ( r1_tarski(C_46,k3_subset_1(A_47,B_48))
      | ~ r1_tarski(B_48,k3_subset_1(A_47,C_46))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    ! [C_49,A_50,B_51] :
      ( r1_tarski(C_49,k3_subset_1(A_50,B_51))
      | ~ r1_xboole_0(B_51,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_16,c_130])).

tff(c_14,plain,(
    ! [B_17,C_19,A_16] :
      ( r1_xboole_0(B_17,C_19)
      | ~ r1_tarski(B_17,k3_subset_1(A_16,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_153,plain,(
    ! [C_55,B_56,A_57] :
      ( r1_xboole_0(C_55,B_56)
      | ~ r1_xboole_0(B_56,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_134,c_14])).

tff(c_171,plain,(
    ! [A_57] :
      ( r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1(A_57))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_64,c_153])).

tff(c_173,plain,(
    ! [A_58] :
      ( ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1(A_58))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_58)) ) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_177,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_173])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_177])).

tff(c_182,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_142,plain,(
    ! [B_52,C_53,A_54] :
      ( r1_tarski(B_52,C_53)
      | ~ r1_tarski(k3_subset_1(A_54,C_53),k3_subset_1(A_54,B_52))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_54))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_256,plain,(
    ! [C_80,C_81,A_82] :
      ( r1_tarski(C_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_82))
      | ~ r1_xboole_0(k3_subset_1(A_82,C_81),C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_82))
      | ~ m1_subset_1(k3_subset_1(A_82,C_81),k1_zfmisc_1(A_82)) ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_264,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_182,c_256])).

tff(c_289,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_264])).

tff(c_290,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_289])).

tff(c_298,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_290])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.39  
% 2.26/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.39  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.26/1.39  
% 2.26/1.39  %Foreground sorts:
% 2.26/1.39  
% 2.26/1.39  
% 2.26/1.39  %Background operators:
% 2.26/1.39  
% 2.26/1.39  
% 2.26/1.39  %Foreground operators:
% 2.26/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.26/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.39  
% 2.56/1.40  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 2.56/1.40  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.56/1.40  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.56/1.40  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.56/1.40  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.56/1.40  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.56/1.40  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.56/1.40  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.40  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.40  tff(c_22, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.40  tff(c_29, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.56/1.40  tff(c_28, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.40  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_29, c_28])).
% 2.56/1.40  tff(c_32, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k3_subset_1(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.40  tff(c_39, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_32])).
% 2.56/1.40  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, k4_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.40  tff(c_55, plain, (![A_26]: (r1_xboole_0(A_26, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_26, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_2])).
% 2.56/1.40  tff(c_58, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_55, c_29])).
% 2.56/1.40  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_58])).
% 2.56/1.40  tff(c_63, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.56/1.40  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.40  tff(c_64, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_22])).
% 2.56/1.40  tff(c_16, plain, (![B_17, A_16, C_19]: (r1_tarski(B_17, k3_subset_1(A_16, C_19)) | ~r1_xboole_0(B_17, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.56/1.40  tff(c_130, plain, (![C_46, A_47, B_48]: (r1_tarski(C_46, k3_subset_1(A_47, B_48)) | ~r1_tarski(B_48, k3_subset_1(A_47, C_46)) | ~m1_subset_1(C_46, k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.56/1.40  tff(c_134, plain, (![C_49, A_50, B_51]: (r1_tarski(C_49, k3_subset_1(A_50, B_51)) | ~r1_xboole_0(B_51, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_16, c_130])).
% 2.56/1.40  tff(c_14, plain, (![B_17, C_19, A_16]: (r1_xboole_0(B_17, C_19) | ~r1_tarski(B_17, k3_subset_1(A_16, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.56/1.40  tff(c_153, plain, (![C_55, B_56, A_57]: (r1_xboole_0(C_55, B_56) | ~r1_xboole_0(B_56, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_57)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_134, c_14])).
% 2.56/1.40  tff(c_171, plain, (![A_57]: (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1(A_57)) | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_64, c_153])).
% 2.56/1.40  tff(c_173, plain, (![A_58]: (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1(A_58)) | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_58)))), inference(splitLeft, [status(thm)], [c_171])).
% 2.56/1.40  tff(c_177, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_173])).
% 2.56/1.40  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_177])).
% 2.56/1.40  tff(c_182, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_171])).
% 2.56/1.40  tff(c_142, plain, (![B_52, C_53, A_54]: (r1_tarski(B_52, C_53) | ~r1_tarski(k3_subset_1(A_54, C_53), k3_subset_1(A_54, B_52)) | ~m1_subset_1(C_53, k1_zfmisc_1(A_54)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.56/1.40  tff(c_256, plain, (![C_80, C_81, A_82]: (r1_tarski(C_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_82)) | ~r1_xboole_0(k3_subset_1(A_82, C_81), C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_82)) | ~m1_subset_1(k3_subset_1(A_82, C_81), k1_zfmisc_1(A_82)))), inference(resolution, [status(thm)], [c_16, c_142])).
% 2.56/1.40  tff(c_264, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_182, c_256])).
% 2.56/1.40  tff(c_289, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_264])).
% 2.56/1.40  tff(c_290, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_63, c_289])).
% 2.56/1.40  tff(c_298, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_290])).
% 2.56/1.40  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_298])).
% 2.56/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.40  
% 2.56/1.40  Inference rules
% 2.56/1.40  ----------------------
% 2.56/1.40  #Ref     : 0
% 2.56/1.40  #Sup     : 68
% 2.56/1.40  #Fact    : 0
% 2.56/1.40  #Define  : 0
% 2.56/1.40  #Split   : 2
% 2.56/1.40  #Chain   : 0
% 2.56/1.40  #Close   : 0
% 2.56/1.40  
% 2.56/1.40  Ordering : KBO
% 2.56/1.40  
% 2.56/1.40  Simplification rules
% 2.56/1.40  ----------------------
% 2.56/1.40  #Subsume      : 6
% 2.56/1.40  #Demod        : 16
% 2.56/1.40  #Tautology    : 23
% 2.56/1.40  #SimpNegUnit  : 3
% 2.56/1.40  #BackRed      : 0
% 2.56/1.40  
% 2.56/1.40  #Partial instantiations: 0
% 2.56/1.41  #Strategies tried      : 1
% 2.56/1.41  
% 2.56/1.41  Timing (in seconds)
% 2.56/1.41  ----------------------
% 2.56/1.41  Preprocessing        : 0.32
% 2.56/1.41  Parsing              : 0.18
% 2.56/1.41  CNF conversion       : 0.02
% 2.56/1.41  Main loop            : 0.24
% 2.56/1.41  Inferencing          : 0.10
% 2.56/1.41  Reduction            : 0.06
% 2.56/1.41  Demodulation         : 0.04
% 2.56/1.41  BG Simplification    : 0.02
% 2.56/1.41  Subsumption          : 0.05
% 2.56/1.41  Abstraction          : 0.01
% 2.56/1.41  MUC search           : 0.00
% 2.56/1.41  Cooper               : 0.00
% 2.56/1.41  Total                : 0.60
% 2.56/1.41  Index Insertion      : 0.00
% 2.56/1.41  Index Deletion       : 0.00
% 2.56/1.41  Index Matching       : 0.00
% 2.56/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
