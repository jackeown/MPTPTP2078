%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:39 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   49 (  84 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 132 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_24])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_27])).

tff(c_32,plain,(
    ! [C_28,A_29,B_30] :
      ( v4_relat_1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_32])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_8])).

tff(c_42,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_39])).

tff(c_52,plain,(
    ! [C_34,A_35,B_36] :
      ( k7_relat_1(k7_relat_1(C_34,A_35),B_36) = k7_relat_1(C_34,A_35)
      | ~ r1_tarski(A_35,B_36)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_67,plain,(
    ! [B_36] :
      ( k7_relat_1('#skF_4',B_36) = k7_relat_1('#skF_4','#skF_2')
      | ~ r1_tarski('#skF_2',B_36)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_52])).

tff(c_72,plain,(
    ! [B_37] :
      ( k7_relat_1('#skF_4',B_37) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42,c_67])).

tff(c_76,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_86,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k5_relset_1(A_38,B_39,C_40,D_41) = k7_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_89,plain,(
    ! [D_41] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_41) = k7_relat_1('#skF_4',D_41) ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_91,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_18])).

tff(c_92,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_91])).

tff(c_102,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( r2_relset_1(A_44,B_45,C_46,C_46)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_106,plain,(
    ! [C_48] :
      ( r2_relset_1('#skF_2','#skF_1',C_48,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_102])).

tff(c_108,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_106])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:45:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.94/1.19  
% 1.94/1.19  %Foreground sorts:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Background operators:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Foreground operators:
% 1.94/1.19  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.94/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.94/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.94/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.94/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.19  
% 2.00/1.21  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.00/1.21  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.00/1.21  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.00/1.21  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.00/1.21  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.00/1.21  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 2.00/1.21  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.00/1.21  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.00/1.21  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.21  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.21  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.21  tff(c_24, plain, (![B_24, A_25]: (v1_relat_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.00/1.21  tff(c_27, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_24])).
% 2.00/1.21  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_27])).
% 2.00/1.21  tff(c_32, plain, (![C_28, A_29, B_30]: (v4_relat_1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.21  tff(c_36, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_32])).
% 2.00/1.21  tff(c_8, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.00/1.21  tff(c_39, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_8])).
% 2.00/1.21  tff(c_42, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_39])).
% 2.00/1.21  tff(c_52, plain, (![C_34, A_35, B_36]: (k7_relat_1(k7_relat_1(C_34, A_35), B_36)=k7_relat_1(C_34, A_35) | ~r1_tarski(A_35, B_36) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.00/1.21  tff(c_67, plain, (![B_36]: (k7_relat_1('#skF_4', B_36)=k7_relat_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_2', B_36) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_52])).
% 2.00/1.21  tff(c_72, plain, (![B_37]: (k7_relat_1('#skF_4', B_37)='#skF_4' | ~r1_tarski('#skF_2', B_37))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42, c_67])).
% 2.00/1.21  tff(c_76, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_72])).
% 2.00/1.21  tff(c_86, plain, (![A_38, B_39, C_40, D_41]: (k5_relset_1(A_38, B_39, C_40, D_41)=k7_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.21  tff(c_89, plain, (![D_41]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_41)=k7_relat_1('#skF_4', D_41))), inference(resolution, [status(thm)], [c_22, c_86])).
% 2.00/1.21  tff(c_18, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.21  tff(c_91, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_18])).
% 2.00/1.21  tff(c_92, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_91])).
% 2.00/1.21  tff(c_102, plain, (![A_44, B_45, C_46, D_47]: (r2_relset_1(A_44, B_45, C_46, C_46) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.00/1.21  tff(c_106, plain, (![C_48]: (r2_relset_1('#skF_2', '#skF_1', C_48, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_102])).
% 2.00/1.21  tff(c_108, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_106])).
% 2.00/1.21  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_108])).
% 2.00/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  Inference rules
% 2.00/1.21  ----------------------
% 2.00/1.21  #Ref     : 0
% 2.00/1.21  #Sup     : 20
% 2.00/1.21  #Fact    : 0
% 2.00/1.21  #Define  : 0
% 2.00/1.21  #Split   : 0
% 2.00/1.21  #Chain   : 0
% 2.00/1.21  #Close   : 0
% 2.00/1.21  
% 2.00/1.21  Ordering : KBO
% 2.00/1.21  
% 2.00/1.21  Simplification rules
% 2.00/1.21  ----------------------
% 2.00/1.21  #Subsume      : 0
% 2.00/1.21  #Demod        : 8
% 2.00/1.21  #Tautology    : 8
% 2.00/1.21  #SimpNegUnit  : 1
% 2.00/1.21  #BackRed      : 1
% 2.00/1.21  
% 2.00/1.21  #Partial instantiations: 0
% 2.00/1.21  #Strategies tried      : 1
% 2.00/1.21  
% 2.00/1.21  Timing (in seconds)
% 2.00/1.21  ----------------------
% 2.00/1.21  Preprocessing        : 0.31
% 2.00/1.21  Parsing              : 0.17
% 2.00/1.21  CNF conversion       : 0.02
% 2.00/1.21  Main loop            : 0.13
% 2.00/1.21  Inferencing          : 0.05
% 2.00/1.21  Reduction            : 0.04
% 2.00/1.21  Demodulation         : 0.03
% 2.00/1.21  BG Simplification    : 0.01
% 2.00/1.21  Subsumption          : 0.01
% 2.00/1.21  Abstraction          : 0.01
% 2.00/1.21  MUC search           : 0.00
% 2.00/1.21  Cooper               : 0.00
% 2.00/1.21  Total                : 0.47
% 2.00/1.21  Index Insertion      : 0.00
% 2.00/1.21  Index Deletion       : 0.00
% 2.00/1.21  Index Matching       : 0.00
% 2.00/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
