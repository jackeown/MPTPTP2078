%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:40 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 125 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_41,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_51,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_47])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_181,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_relat_1(A_59),k1_relat_1(B_60))
      | ~ r1_tarski(A_59,B_60)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_11,B_12)),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_40,A_11,B_12] :
      ( r1_tarski(A_40,A_11)
      | ~ r1_tarski(A_40,k1_relat_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_185,plain,(
    ! [A_59,A_11,B_12] :
      ( r1_tarski(k1_relat_1(A_59),A_11)
      | ~ r1_tarski(A_59,k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_181,c_77])).

tff(c_262,plain,(
    ! [A_72,A_73,B_74] :
      ( r1_tarski(k1_relat_1(A_72),A_73)
      | ~ r1_tarski(A_72,k2_zfmisc_1(A_73,B_74))
      | ~ v1_relat_1(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_185])).

tff(c_269,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_262])).

tff(c_277,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_269])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_78,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_3')
      | ~ r1_tarski(A_40,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_69])).

tff(c_293,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_277,c_78])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_314,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_293,c_18])).

tff(c_323,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_314])).

tff(c_409,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k5_relset_1(A_81,B_82,C_83,D_84) = k7_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_416,plain,(
    ! [D_84] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_84) = k7_relat_1('#skF_4',D_84) ),
    inference(resolution,[status(thm)],[c_28,c_409])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_418,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_24])).

tff(c_419,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_418])).

tff(c_479,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( r2_relset_1(A_89,B_90,C_91,C_91)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_523,plain,(
    ! [C_96] :
      ( r2_relset_1('#skF_2','#skF_1',C_96,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_479])).

tff(c_528,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_523])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:31:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.48  
% 2.71/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.48  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.48  
% 2.71/1.48  %Foreground sorts:
% 2.71/1.48  
% 2.71/1.48  
% 2.71/1.48  %Background operators:
% 2.71/1.48  
% 2.71/1.48  
% 2.71/1.48  %Foreground operators:
% 2.71/1.48  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.71/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.71/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.71/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.48  
% 2.71/1.50  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.71/1.50  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.71/1.50  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.71/1.50  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.71/1.50  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.71/1.50  tff(f_46, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 2.71/1.50  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.71/1.50  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.71/1.50  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.71/1.50  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.71/1.50  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.50  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.50  tff(c_41, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.50  tff(c_47, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.71/1.50  tff(c_51, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_47])).
% 2.71/1.50  tff(c_32, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.50  tff(c_40, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_32])).
% 2.71/1.50  tff(c_181, plain, (![A_59, B_60]: (r1_tarski(k1_relat_1(A_59), k1_relat_1(B_60)) | ~r1_tarski(A_59, B_60) | ~v1_relat_1(B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.71/1.50  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_11, B_12)), A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.50  tff(c_69, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.50  tff(c_77, plain, (![A_40, A_11, B_12]: (r1_tarski(A_40, A_11) | ~r1_tarski(A_40, k1_relat_1(k2_zfmisc_1(A_11, B_12))))), inference(resolution, [status(thm)], [c_12, c_69])).
% 2.71/1.50  tff(c_185, plain, (![A_59, A_11, B_12]: (r1_tarski(k1_relat_1(A_59), A_11) | ~r1_tarski(A_59, k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(A_59))), inference(resolution, [status(thm)], [c_181, c_77])).
% 2.71/1.50  tff(c_262, plain, (![A_72, A_73, B_74]: (r1_tarski(k1_relat_1(A_72), A_73) | ~r1_tarski(A_72, k2_zfmisc_1(A_73, B_74)) | ~v1_relat_1(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_185])).
% 2.71/1.50  tff(c_269, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_262])).
% 2.71/1.50  tff(c_277, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_269])).
% 2.71/1.50  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.50  tff(c_78, plain, (![A_40]: (r1_tarski(A_40, '#skF_3') | ~r1_tarski(A_40, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_69])).
% 2.71/1.50  tff(c_293, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_277, c_78])).
% 2.71/1.50  tff(c_18, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.50  tff(c_314, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_293, c_18])).
% 2.71/1.50  tff(c_323, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_314])).
% 2.71/1.50  tff(c_409, plain, (![A_81, B_82, C_83, D_84]: (k5_relset_1(A_81, B_82, C_83, D_84)=k7_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.71/1.50  tff(c_416, plain, (![D_84]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_84)=k7_relat_1('#skF_4', D_84))), inference(resolution, [status(thm)], [c_28, c_409])).
% 2.71/1.50  tff(c_24, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.50  tff(c_418, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_416, c_24])).
% 2.71/1.50  tff(c_419, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_418])).
% 2.71/1.50  tff(c_479, plain, (![A_89, B_90, C_91, D_92]: (r2_relset_1(A_89, B_90, C_91, C_91) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.50  tff(c_523, plain, (![C_96]: (r2_relset_1('#skF_2', '#skF_1', C_96, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_28, c_479])).
% 2.71/1.50  tff(c_528, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_523])).
% 2.71/1.50  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_528])).
% 2.71/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.50  
% 2.71/1.50  Inference rules
% 2.71/1.50  ----------------------
% 2.71/1.50  #Ref     : 0
% 2.71/1.50  #Sup     : 109
% 2.71/1.50  #Fact    : 0
% 2.71/1.50  #Define  : 0
% 2.71/1.50  #Split   : 4
% 2.71/1.50  #Chain   : 0
% 2.71/1.50  #Close   : 0
% 2.71/1.50  
% 2.71/1.50  Ordering : KBO
% 2.71/1.50  
% 2.71/1.50  Simplification rules
% 2.71/1.50  ----------------------
% 2.71/1.50  #Subsume      : 15
% 2.71/1.50  #Demod        : 27
% 2.71/1.50  #Tautology    : 15
% 2.71/1.50  #SimpNegUnit  : 1
% 2.71/1.50  #BackRed      : 1
% 2.71/1.50  
% 2.71/1.50  #Partial instantiations: 0
% 2.71/1.50  #Strategies tried      : 1
% 2.71/1.50  
% 2.71/1.50  Timing (in seconds)
% 2.71/1.50  ----------------------
% 2.71/1.50  Preprocessing        : 0.37
% 2.71/1.50  Parsing              : 0.20
% 2.71/1.50  CNF conversion       : 0.02
% 2.71/1.50  Main loop            : 0.33
% 2.71/1.50  Inferencing          : 0.13
% 2.71/1.50  Reduction            : 0.10
% 2.71/1.50  Demodulation         : 0.08
% 2.71/1.50  BG Simplification    : 0.02
% 2.71/1.50  Subsumption          : 0.06
% 2.71/1.50  Abstraction          : 0.02
% 2.71/1.50  MUC search           : 0.00
% 2.71/1.50  Cooper               : 0.00
% 2.71/1.50  Total                : 0.74
% 2.71/1.50  Index Insertion      : 0.00
% 2.71/1.50  Index Deletion       : 0.00
% 2.71/1.50  Index Matching       : 0.00
% 2.71/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
