%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:21 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  86 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(c_16,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_89,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_101,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k1_relset_1(A_22,B_23,C_24),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(k1_relset_1(A_25,B_26,C_27),A_25)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(resolution,[status(thm)],[c_101,c_6])).

tff(c_117,plain,(
    r1_tarski(k1_relset_1('#skF_2','#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    k2_xboole_0(k1_relset_1('#skF_2','#skF_1','#skF_3'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_125,plain,(
    k2_xboole_0('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_2])).

tff(c_18,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_160,plain,(
    ! [C_34,A_35,B_36,D_37] :
      ( r1_tarski(C_34,k1_relset_1(A_35,B_36,D_37))
      | ~ r1_tarski(k6_relat_1(C_34),D_37)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_164,plain,(
    ! [A_38,B_39] :
      ( r1_tarski('#skF_2',k1_relset_1(A_38,B_39,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(resolution,[status(thm)],[c_18,c_160])).

tff(c_172,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_164])).

tff(c_175,plain,(
    k2_xboole_0('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_4])).

tff(c_177,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_175])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_177])).

tff(c_180,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_282,plain,(
    ! [C_64,A_65,B_66,D_67] :
      ( r1_tarski(C_64,k2_relset_1(A_65,B_66,D_67))
      | ~ r1_tarski(k6_relat_1(C_64),D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_286,plain,(
    ! [A_68,B_69] :
      ( r1_tarski('#skF_2',k2_relset_1(A_68,B_69,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(resolution,[status(thm)],[c_18,c_282])).

tff(c_292,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_286])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  %$ r1_tarski > m1_subset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.23  
% 2.08/1.23  %Foreground sorts:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Background operators:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Foreground operators:
% 2.08/1.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.08/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.23  
% 2.08/1.24  tff(f_56, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 2.08/1.24  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.08/1.24  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.08/1.24  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.08/1.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.08/1.24  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.08/1.24  tff(c_16, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.24  tff(c_89, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_16])).
% 2.08/1.24  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.24  tff(c_101, plain, (![A_22, B_23, C_24]: (m1_subset_1(k1_relset_1(A_22, B_23, C_24), k1_zfmisc_1(A_22)) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.24  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.24  tff(c_106, plain, (![A_25, B_26, C_27]: (r1_tarski(k1_relset_1(A_25, B_26, C_27), A_25) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(resolution, [status(thm)], [c_101, c_6])).
% 2.08/1.24  tff(c_117, plain, (r1_tarski(k1_relset_1('#skF_2', '#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_106])).
% 2.08/1.24  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.24  tff(c_121, plain, (k2_xboole_0(k1_relset_1('#skF_2', '#skF_1', '#skF_3'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_117, c_4])).
% 2.08/1.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.24  tff(c_125, plain, (k2_xboole_0('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_121, c_2])).
% 2.08/1.24  tff(c_18, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.24  tff(c_160, plain, (![C_34, A_35, B_36, D_37]: (r1_tarski(C_34, k1_relset_1(A_35, B_36, D_37)) | ~r1_tarski(k6_relat_1(C_34), D_37) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.24  tff(c_164, plain, (![A_38, B_39]: (r1_tarski('#skF_2', k1_relset_1(A_38, B_39, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(resolution, [status(thm)], [c_18, c_160])).
% 2.08/1.24  tff(c_172, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_164])).
% 2.08/1.24  tff(c_175, plain, (k2_xboole_0('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_172, c_4])).
% 2.08/1.24  tff(c_177, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_175])).
% 2.08/1.24  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_177])).
% 2.08/1.24  tff(c_180, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_16])).
% 2.08/1.24  tff(c_282, plain, (![C_64, A_65, B_66, D_67]: (r1_tarski(C_64, k2_relset_1(A_65, B_66, D_67)) | ~r1_tarski(k6_relat_1(C_64), D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.24  tff(c_286, plain, (![A_68, B_69]: (r1_tarski('#skF_2', k2_relset_1(A_68, B_69, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(resolution, [status(thm)], [c_18, c_282])).
% 2.08/1.24  tff(c_292, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_286])).
% 2.08/1.24  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_292])).
% 2.08/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  Inference rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Ref     : 0
% 2.08/1.24  #Sup     : 69
% 2.08/1.24  #Fact    : 0
% 2.08/1.24  #Define  : 0
% 2.08/1.24  #Split   : 1
% 2.08/1.24  #Chain   : 0
% 2.08/1.24  #Close   : 0
% 2.08/1.24  
% 2.08/1.24  Ordering : KBO
% 2.08/1.24  
% 2.08/1.24  Simplification rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Subsume      : 0
% 2.08/1.24  #Demod        : 26
% 2.08/1.24  #Tautology    : 41
% 2.08/1.24  #SimpNegUnit  : 2
% 2.08/1.24  #BackRed      : 0
% 2.08/1.24  
% 2.08/1.24  #Partial instantiations: 0
% 2.08/1.24  #Strategies tried      : 1
% 2.08/1.24  
% 2.08/1.24  Timing (in seconds)
% 2.08/1.24  ----------------------
% 2.08/1.25  Preprocessing        : 0.27
% 2.08/1.25  Parsing              : 0.15
% 2.08/1.25  CNF conversion       : 0.02
% 2.08/1.25  Main loop            : 0.22
% 2.08/1.25  Inferencing          : 0.09
% 2.08/1.25  Reduction            : 0.07
% 2.08/1.25  Demodulation         : 0.05
% 2.08/1.25  BG Simplification    : 0.01
% 2.08/1.25  Subsumption          : 0.04
% 2.08/1.25  Abstraction          : 0.01
% 2.08/1.25  MUC search           : 0.00
% 2.08/1.25  Cooper               : 0.00
% 2.08/1.25  Total                : 0.51
% 2.08/1.25  Index Insertion      : 0.00
% 2.08/1.25  Index Deletion       : 0.00
% 2.08/1.25  Index Matching       : 0.00
% 2.08/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
