%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:34 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   68 ( 108 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_51,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_85,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_98,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_85])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_12])).

tff(c_105,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_102])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_14])).

tff(c_113,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_109])).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_172,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(A_63,C_64)
      | ~ r1_tarski(B_65,C_64)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,'#skF_4')
      | ~ r1_tarski(A_66,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_172])).

tff(c_200,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_188])).

tff(c_253,plain,(
    ! [B_73,A_74] :
      ( k7_relat_1(B_73,A_74) = B_73
      | ~ r1_tarski(k1_relat_1(B_73),A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_260,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_200,c_253])).

tff(c_270,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_260])).

tff(c_382,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k5_relset_1(A_80,B_81,C_82,D_83) = k7_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_392,plain,(
    ! [D_83] : k5_relset_1('#skF_3','#skF_2','#skF_5',D_83) = k7_relat_1('#skF_5',D_83) ),
    inference(resolution,[status(thm)],[c_32,c_382])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k5_relset_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_423,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_28])).

tff(c_424,plain,(
    ~ r2_relset_1('#skF_3','#skF_2','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_423])).

tff(c_454,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( r2_relset_1(A_89,B_90,C_91,C_91)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_476,plain,(
    ! [C_95] :
      ( r2_relset_1('#skF_3','#skF_2',C_95,C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_454])).

tff(c_481,plain,(
    r2_relset_1('#skF_3','#skF_2','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_476])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_424,c_481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.58/1.35  
% 2.58/1.35  %Foreground sorts:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Background operators:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Foreground operators:
% 2.58/1.35  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.35  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.58/1.35  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.58/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.58/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.58/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.58/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.58/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.35  
% 2.58/1.37  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.58/1.37  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.58/1.37  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.58/1.37  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.58/1.37  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.58/1.37  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.58/1.37  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.58/1.37  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.58/1.37  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.58/1.37  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.58/1.37  tff(c_51, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.37  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_51])).
% 2.58/1.37  tff(c_85, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.37  tff(c_98, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_85])).
% 2.58/1.37  tff(c_12, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.37  tff(c_102, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_12])).
% 2.58/1.37  tff(c_105, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_102])).
% 2.58/1.37  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.58/1.37  tff(c_109, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_105, c_14])).
% 2.58/1.37  tff(c_113, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_109])).
% 2.58/1.37  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.58/1.37  tff(c_172, plain, (![A_63, C_64, B_65]: (r1_tarski(A_63, C_64) | ~r1_tarski(B_65, C_64) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.37  tff(c_188, plain, (![A_66]: (r1_tarski(A_66, '#skF_4') | ~r1_tarski(A_66, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_172])).
% 2.58/1.37  tff(c_200, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_113, c_188])).
% 2.58/1.37  tff(c_253, plain, (![B_73, A_74]: (k7_relat_1(B_73, A_74)=B_73 | ~r1_tarski(k1_relat_1(B_73), A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.58/1.37  tff(c_260, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_200, c_253])).
% 2.58/1.37  tff(c_270, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_260])).
% 2.58/1.37  tff(c_382, plain, (![A_80, B_81, C_82, D_83]: (k5_relset_1(A_80, B_81, C_82, D_83)=k7_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.37  tff(c_392, plain, (![D_83]: (k5_relset_1('#skF_3', '#skF_2', '#skF_5', D_83)=k7_relat_1('#skF_5', D_83))), inference(resolution, [status(thm)], [c_32, c_382])).
% 2.58/1.37  tff(c_28, plain, (~r2_relset_1('#skF_3', '#skF_2', k5_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.58/1.37  tff(c_423, plain, (~r2_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_392, c_28])).
% 2.58/1.37  tff(c_424, plain, (~r2_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_423])).
% 2.58/1.37  tff(c_454, plain, (![A_89, B_90, C_91, D_92]: (r2_relset_1(A_89, B_90, C_91, C_91) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.58/1.37  tff(c_476, plain, (![C_95]: (r2_relset_1('#skF_3', '#skF_2', C_95, C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_454])).
% 2.58/1.37  tff(c_481, plain, (r2_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_476])).
% 2.58/1.37  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_424, c_481])).
% 2.58/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  Inference rules
% 2.58/1.37  ----------------------
% 2.58/1.37  #Ref     : 0
% 2.58/1.37  #Sup     : 97
% 2.58/1.37  #Fact    : 0
% 2.58/1.37  #Define  : 0
% 2.58/1.37  #Split   : 0
% 2.58/1.37  #Chain   : 0
% 2.58/1.37  #Close   : 0
% 2.58/1.37  
% 2.58/1.37  Ordering : KBO
% 2.58/1.37  
% 2.58/1.37  Simplification rules
% 2.58/1.37  ----------------------
% 2.58/1.37  #Subsume      : 0
% 2.58/1.37  #Demod        : 19
% 2.58/1.37  #Tautology    : 17
% 2.58/1.37  #SimpNegUnit  : 1
% 2.58/1.37  #BackRed      : 1
% 2.58/1.37  
% 2.58/1.37  #Partial instantiations: 0
% 2.58/1.37  #Strategies tried      : 1
% 2.58/1.37  
% 2.58/1.37  Timing (in seconds)
% 2.58/1.37  ----------------------
% 2.58/1.37  Preprocessing        : 0.28
% 2.58/1.37  Parsing              : 0.15
% 2.58/1.37  CNF conversion       : 0.02
% 2.58/1.37  Main loop            : 0.27
% 2.58/1.37  Inferencing          : 0.11
% 2.58/1.37  Reduction            : 0.08
% 2.58/1.37  Demodulation         : 0.06
% 2.58/1.37  BG Simplification    : 0.01
% 2.58/1.37  Subsumption          : 0.05
% 2.58/1.37  Abstraction          : 0.02
% 2.58/1.37  MUC search           : 0.00
% 2.58/1.37  Cooper               : 0.00
% 2.58/1.37  Total                : 0.59
% 2.58/1.37  Index Insertion      : 0.00
% 2.58/1.37  Index Deletion       : 0.00
% 2.58/1.37  Index Matching       : 0.00
% 2.58/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
