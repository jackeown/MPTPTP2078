%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:21 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
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
%$ r1_tarski > m1_subset_1 > k2_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_16,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_192,plain,(
    ! [C_44,A_45,B_46,D_47] :
      ( r1_tarski(C_44,k1_relset_1(A_45,B_46,D_47))
      | ~ r1_tarski(k6_relat_1(C_44),D_47)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_196,plain,(
    ! [A_48,B_49] :
      ( r1_tarski('#skF_2',k1_relset_1(A_48,B_49,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_204,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_196])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    k3_xboole_0('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_204,c_4])).

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

tff(c_121,plain,(
    k3_xboole_0(k1_relset_1('#skF_2','#skF_1','#skF_3'),'#skF_2') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_125,plain,(
    k3_xboole_0('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_2])).

tff(c_209,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_125])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_209])).

tff(c_212,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_311,plain,(
    ! [C_74,A_75,B_76,D_77] :
      ( r1_tarski(C_74,k2_relset_1(A_75,B_76,D_77))
      | ~ r1_tarski(k6_relat_1(C_74),D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_315,plain,(
    ! [A_78,B_79] :
      ( r1_tarski('#skF_2',k2_relset_1(A_78,B_79,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(resolution,[status(thm)],[c_18,c_311])).

tff(c_321,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_315])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:23:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  %$ r1_tarski > m1_subset_1 > k2_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.29  
% 2.07/1.29  %Foreground sorts:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Background operators:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Foreground operators:
% 2.07/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.07/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.29  
% 2.07/1.30  tff(f_56, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 2.07/1.30  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.07/1.30  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.07/1.30  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.07/1.30  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.07/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.07/1.30  tff(c_16, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.30  tff(c_92, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_16])).
% 2.07/1.30  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.30  tff(c_18, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.30  tff(c_192, plain, (![C_44, A_45, B_46, D_47]: (r1_tarski(C_44, k1_relset_1(A_45, B_46, D_47)) | ~r1_tarski(k6_relat_1(C_44), D_47) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.30  tff(c_196, plain, (![A_48, B_49]: (r1_tarski('#skF_2', k1_relset_1(A_48, B_49, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(resolution, [status(thm)], [c_18, c_192])).
% 2.07/1.30  tff(c_204, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_196])).
% 2.07/1.30  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.30  tff(c_208, plain, (k3_xboole_0('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_204, c_4])).
% 2.07/1.30  tff(c_101, plain, (![A_22, B_23, C_24]: (m1_subset_1(k1_relset_1(A_22, B_23, C_24), k1_zfmisc_1(A_22)) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.30  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.30  tff(c_106, plain, (![A_25, B_26, C_27]: (r1_tarski(k1_relset_1(A_25, B_26, C_27), A_25) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(resolution, [status(thm)], [c_101, c_6])).
% 2.07/1.30  tff(c_117, plain, (r1_tarski(k1_relset_1('#skF_2', '#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_106])).
% 2.07/1.30  tff(c_121, plain, (k3_xboole_0(k1_relset_1('#skF_2', '#skF_1', '#skF_3'), '#skF_2')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_117, c_4])).
% 2.07/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.30  tff(c_125, plain, (k3_xboole_0('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_121, c_2])).
% 2.07/1.30  tff(c_209, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_208, c_125])).
% 2.07/1.30  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_209])).
% 2.07/1.30  tff(c_212, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_16])).
% 2.07/1.30  tff(c_311, plain, (![C_74, A_75, B_76, D_77]: (r1_tarski(C_74, k2_relset_1(A_75, B_76, D_77)) | ~r1_tarski(k6_relat_1(C_74), D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.30  tff(c_315, plain, (![A_78, B_79]: (r1_tarski('#skF_2', k2_relset_1(A_78, B_79, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(resolution, [status(thm)], [c_18, c_311])).
% 2.07/1.30  tff(c_321, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_315])).
% 2.07/1.30  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_321])).
% 2.07/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.30  
% 2.07/1.30  Inference rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Ref     : 0
% 2.07/1.30  #Sup     : 75
% 2.07/1.30  #Fact    : 0
% 2.07/1.30  #Define  : 0
% 2.07/1.30  #Split   : 1
% 2.07/1.30  #Chain   : 0
% 2.07/1.30  #Close   : 0
% 2.07/1.30  
% 2.07/1.30  Ordering : KBO
% 2.07/1.30  
% 2.07/1.30  Simplification rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Subsume      : 0
% 2.07/1.30  #Demod        : 28
% 2.07/1.30  #Tautology    : 43
% 2.07/1.30  #SimpNegUnit  : 2
% 2.07/1.30  #BackRed      : 1
% 2.07/1.30  
% 2.07/1.30  #Partial instantiations: 0
% 2.07/1.30  #Strategies tried      : 1
% 2.07/1.30  
% 2.07/1.30  Timing (in seconds)
% 2.07/1.30  ----------------------
% 2.07/1.30  Preprocessing        : 0.27
% 2.07/1.30  Parsing              : 0.16
% 2.07/1.30  CNF conversion       : 0.02
% 2.07/1.30  Main loop            : 0.25
% 2.07/1.30  Inferencing          : 0.10
% 2.07/1.30  Reduction            : 0.07
% 2.07/1.30  Demodulation         : 0.05
% 2.07/1.30  BG Simplification    : 0.01
% 2.07/1.30  Subsumption          : 0.04
% 2.07/1.30  Abstraction          : 0.01
% 2.07/1.30  MUC search           : 0.00
% 2.07/1.30  Cooper               : 0.00
% 2.07/1.30  Total                : 0.54
% 2.07/1.30  Index Insertion      : 0.00
% 2.07/1.30  Index Deletion       : 0.00
% 2.07/1.30  Index Matching       : 0.00
% 2.07/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
