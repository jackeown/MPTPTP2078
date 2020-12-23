%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:46 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   53 (  88 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :   94 ( 216 expanded)
%              Number of equality atoms :    6 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [B_15,A_14,C_17] :
      ( r1_tarski(B_15,k3_subset_1(A_14,C_17))
      | ~ r1_xboole_0(B_15,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,(
    ! [A_34,B_35] :
      ( k3_subset_1(A_34,k3_subset_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_157,plain,(
    ! [B_40,A_41,C_42] :
      ( r1_tarski(B_40,k3_subset_1(A_41,C_42))
      | ~ r1_xboole_0(B_40,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_169,plain,(
    ! [B_40] :
      ( r1_tarski(B_40,'#skF_3')
      | ~ r1_xboole_0(B_40,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_40,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_157])).

tff(c_283,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_286,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_283])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_286])).

tff(c_292,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_197,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(k3_subset_1(A_46,C_47),k3_subset_1(A_46,B_48))
      | ~ r1_tarski(B_48,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [B_15,C_17,A_14] :
      ( r1_xboole_0(B_15,C_17)
      | ~ r1_tarski(B_15,k3_subset_1(A_14,C_17))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_353,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_xboole_0(k3_subset_1(A_58,C_59),B_60)
      | ~ m1_subset_1(k3_subset_1(A_58,C_59),k1_zfmisc_1(A_58))
      | ~ r1_tarski(B_60,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_58)) ) ),
    inference(resolution,[status(thm)],[c_197,c_18])).

tff(c_363,plain,(
    ! [B_60] :
      ( r1_xboole_0(k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')),B_60)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(B_60,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_60,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_353])).

tff(c_430,plain,(
    ! [B_63] :
      ( r1_xboole_0('#skF_3',B_63)
      | ~ r1_tarski(B_63,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_63,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_30,c_70,c_363])).

tff(c_438,plain,(
    ! [B_15] :
      ( r1_xboole_0('#skF_3',B_15)
      | ~ r1_xboole_0(B_15,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_15,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_430])).

tff(c_445,plain,(
    ! [B_64] :
      ( r1_xboole_0('#skF_3',B_64)
      | ~ r1_xboole_0(B_64,'#skF_3')
      | ~ m1_subset_1(B_64,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_438])).

tff(c_458,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_445])).

tff(c_470,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_458])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = A_4
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_476,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_470,c_6])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_496,plain,(
    ! [A_65] :
      ( r1_xboole_0(A_65,'#skF_4')
      | ~ r1_tarski(A_65,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_2])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_160,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_157,c_22])).

tff(c_175,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_160])).

tff(c_505,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_496,c_175])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:24:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.39  
% 2.59/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.40  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.59/1.40  
% 2.59/1.40  %Foreground sorts:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Background operators:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Foreground operators:
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.59/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.40  
% 2.59/1.41  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 2.59/1.41  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.59/1.41  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.59/1.41  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.59/1.41  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.59/1.41  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.59/1.41  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.59/1.41  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.41  tff(c_24, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.41  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.41  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.41  tff(c_20, plain, (![B_15, A_14, C_17]: (r1_tarski(B_15, k3_subset_1(A_14, C_17)) | ~r1_xboole_0(B_15, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.41  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.41  tff(c_61, plain, (![A_34, B_35]: (k3_subset_1(A_34, k3_subset_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.41  tff(c_70, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_30, c_61])).
% 2.59/1.41  tff(c_157, plain, (![B_40, A_41, C_42]: (r1_tarski(B_40, k3_subset_1(A_41, C_42)) | ~r1_xboole_0(B_40, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_41)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.41  tff(c_169, plain, (![B_40]: (r1_tarski(B_40, '#skF_3') | ~r1_xboole_0(B_40, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_40, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_157])).
% 2.59/1.41  tff(c_283, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_169])).
% 2.59/1.41  tff(c_286, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_283])).
% 2.59/1.41  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_286])).
% 2.59/1.41  tff(c_292, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_169])).
% 2.59/1.41  tff(c_197, plain, (![A_46, C_47, B_48]: (r1_tarski(k3_subset_1(A_46, C_47), k3_subset_1(A_46, B_48)) | ~r1_tarski(B_48, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_46)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.59/1.41  tff(c_18, plain, (![B_15, C_17, A_14]: (r1_xboole_0(B_15, C_17) | ~r1_tarski(B_15, k3_subset_1(A_14, C_17)) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.41  tff(c_353, plain, (![A_58, C_59, B_60]: (r1_xboole_0(k3_subset_1(A_58, C_59), B_60) | ~m1_subset_1(k3_subset_1(A_58, C_59), k1_zfmisc_1(A_58)) | ~r1_tarski(B_60, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_58)))), inference(resolution, [status(thm)], [c_197, c_18])).
% 2.59/1.41  tff(c_363, plain, (![B_60]: (r1_xboole_0(k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3')), B_60) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~r1_tarski(B_60, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_60, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_353])).
% 2.59/1.41  tff(c_430, plain, (![B_63]: (r1_xboole_0('#skF_3', B_63) | ~r1_tarski(B_63, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(B_63, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_30, c_70, c_363])).
% 2.59/1.41  tff(c_438, plain, (![B_15]: (r1_xboole_0('#skF_3', B_15) | ~r1_xboole_0(B_15, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_15, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_430])).
% 2.59/1.41  tff(c_445, plain, (![B_64]: (r1_xboole_0('#skF_3', B_64) | ~r1_xboole_0(B_64, '#skF_3') | ~m1_subset_1(B_64, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_438])).
% 2.59/1.41  tff(c_458, plain, (r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_445])).
% 2.59/1.41  tff(c_470, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_458])).
% 2.59/1.41  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=A_4 | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.41  tff(c_476, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_470, c_6])).
% 2.59/1.41  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.41  tff(c_496, plain, (![A_65]: (r1_xboole_0(A_65, '#skF_4') | ~r1_tarski(A_65, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_476, c_2])).
% 2.59/1.41  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.41  tff(c_22, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.41  tff(c_160, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_157, c_22])).
% 2.59/1.41  tff(c_175, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_160])).
% 2.59/1.41  tff(c_505, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_496, c_175])).
% 2.59/1.41  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_505])).
% 2.59/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.41  
% 2.59/1.41  Inference rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Ref     : 0
% 2.59/1.41  #Sup     : 117
% 2.59/1.41  #Fact    : 0
% 2.59/1.41  #Define  : 0
% 2.59/1.41  #Split   : 6
% 2.59/1.41  #Chain   : 0
% 2.59/1.41  #Close   : 0
% 2.59/1.41  
% 2.59/1.41  Ordering : KBO
% 2.59/1.41  
% 2.59/1.41  Simplification rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Subsume      : 2
% 2.59/1.41  #Demod        : 42
% 2.59/1.41  #Tautology    : 36
% 2.59/1.41  #SimpNegUnit  : 0
% 2.59/1.41  #BackRed      : 0
% 2.59/1.41  
% 2.59/1.41  #Partial instantiations: 0
% 2.59/1.41  #Strategies tried      : 1
% 2.59/1.41  
% 2.59/1.41  Timing (in seconds)
% 2.59/1.41  ----------------------
% 2.59/1.41  Preprocessing        : 0.28
% 2.59/1.41  Parsing              : 0.16
% 2.59/1.41  CNF conversion       : 0.02
% 2.59/1.41  Main loop            : 0.30
% 2.59/1.41  Inferencing          : 0.11
% 2.59/1.41  Reduction            : 0.09
% 2.59/1.41  Demodulation         : 0.06
% 2.59/1.41  BG Simplification    : 0.02
% 2.59/1.41  Subsumption          : 0.07
% 2.59/1.41  Abstraction          : 0.01
% 2.59/1.41  MUC search           : 0.00
% 2.59/1.41  Cooper               : 0.00
% 2.59/1.41  Total                : 0.62
% 2.59/1.41  Index Insertion      : 0.00
% 2.59/1.41  Index Deletion       : 0.00
% 2.59/1.41  Index Matching       : 0.00
% 2.59/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
