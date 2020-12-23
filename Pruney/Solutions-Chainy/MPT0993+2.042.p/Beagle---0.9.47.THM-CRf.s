%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:48 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   53 (  72 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 128 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [B_25,A_26] :
      ( v1_relat_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_41,plain,(
    ! [C_32,A_33,B_34] :
      ( v4_relat_1(C_32,A_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_41])).

tff(c_56,plain,(
    ! [C_35,B_36,A_37] :
      ( v4_relat_1(C_35,B_36)
      | ~ v4_relat_1(C_35,A_37)
      | ~ v1_relat_1(C_35)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ! [B_36] :
      ( v4_relat_1('#skF_4',B_36)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_36) ) ),
    inference(resolution,[status(thm)],[c_45,c_56])).

tff(c_68,plain,(
    ! [B_42] :
      ( v4_relat_1('#skF_4',B_42)
      | ~ r1_tarski('#skF_1',B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_58])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [B_42] :
      ( k7_relat_1('#skF_4',B_42) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_42) ) ),
    inference(resolution,[status(thm)],[c_68,c_6])).

tff(c_80,plain,(
    ! [B_43] :
      ( k7_relat_1('#skF_4',B_43) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_73])).

tff(c_84,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k2_partfun1(A_38,B_39,C_40,D_41) = k7_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    ! [D_41] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_41) = k7_relat_1('#skF_4',D_41)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_62])).

tff(c_67,plain,(
    ! [D_41] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_41) = k7_relat_1('#skF_4',D_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_64])).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_89,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_18])).

tff(c_90,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_89])).

tff(c_105,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( r2_relset_1(A_47,B_48,C_49,C_49)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_109,plain,(
    ! [C_51] :
      ( r2_relset_1('#skF_1','#skF_2',C_51,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_105])).

tff(c_111,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_109])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n007.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 11:12:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.15  
% 1.77/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.15  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.77/1.15  
% 1.77/1.15  %Foreground sorts:
% 1.77/1.15  
% 1.77/1.15  
% 1.77/1.15  %Background operators:
% 1.77/1.15  
% 1.77/1.15  
% 1.77/1.15  %Foreground operators:
% 1.77/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.77/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.77/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.77/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.77/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.77/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.15  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.77/1.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.77/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.77/1.15  
% 1.77/1.16  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 1.77/1.16  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.77/1.16  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.77/1.16  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.77/1.16  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 1.77/1.16  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.77/1.16  tff(f_67, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.77/1.16  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 1.77/1.16  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.77/1.16  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.77/1.16  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.77/1.16  tff(c_28, plain, (![B_25, A_26]: (v1_relat_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.77/1.16  tff(c_31, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_28])).
% 1.77/1.16  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_31])).
% 1.77/1.16  tff(c_41, plain, (![C_32, A_33, B_34]: (v4_relat_1(C_32, A_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.77/1.16  tff(c_45, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_41])).
% 1.77/1.16  tff(c_56, plain, (![C_35, B_36, A_37]: (v4_relat_1(C_35, B_36) | ~v4_relat_1(C_35, A_37) | ~v1_relat_1(C_35) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.77/1.16  tff(c_58, plain, (![B_36]: (v4_relat_1('#skF_4', B_36) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_36))), inference(resolution, [status(thm)], [c_45, c_56])).
% 1.77/1.16  tff(c_68, plain, (![B_42]: (v4_relat_1('#skF_4', B_42) | ~r1_tarski('#skF_1', B_42))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_58])).
% 1.77/1.16  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.16  tff(c_73, plain, (![B_42]: (k7_relat_1('#skF_4', B_42)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_42))), inference(resolution, [status(thm)], [c_68, c_6])).
% 1.77/1.16  tff(c_80, plain, (![B_43]: (k7_relat_1('#skF_4', B_43)='#skF_4' | ~r1_tarski('#skF_1', B_43))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_73])).
% 1.77/1.16  tff(c_84, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_80])).
% 1.77/1.16  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.77/1.16  tff(c_62, plain, (![A_38, B_39, C_40, D_41]: (k2_partfun1(A_38, B_39, C_40, D_41)=k7_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(C_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.77/1.16  tff(c_64, plain, (![D_41]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_41)=k7_relat_1('#skF_4', D_41) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_62])).
% 1.77/1.16  tff(c_67, plain, (![D_41]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_41)=k7_relat_1('#skF_4', D_41))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_64])).
% 1.77/1.16  tff(c_18, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.77/1.16  tff(c_89, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_18])).
% 1.77/1.16  tff(c_90, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_89])).
% 1.77/1.16  tff(c_105, plain, (![A_47, B_48, C_49, D_50]: (r2_relset_1(A_47, B_48, C_49, C_49) | ~m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.77/1.16  tff(c_109, plain, (![C_51]: (r2_relset_1('#skF_1', '#skF_2', C_51, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_22, c_105])).
% 1.77/1.16  tff(c_111, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_109])).
% 1.77/1.16  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_111])).
% 1.77/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.16  
% 1.77/1.16  Inference rules
% 1.77/1.16  ----------------------
% 1.77/1.16  #Ref     : 0
% 1.77/1.16  #Sup     : 18
% 1.77/1.16  #Fact    : 0
% 1.77/1.16  #Define  : 0
% 1.77/1.16  #Split   : 1
% 1.77/1.16  #Chain   : 0
% 1.77/1.16  #Close   : 0
% 1.77/1.16  
% 1.77/1.16  Ordering : KBO
% 1.77/1.16  
% 1.77/1.16  Simplification rules
% 1.77/1.16  ----------------------
% 1.77/1.16  #Subsume      : 0
% 1.77/1.16  #Demod        : 8
% 1.77/1.16  #Tautology    : 6
% 1.77/1.16  #SimpNegUnit  : 1
% 1.77/1.16  #BackRed      : 1
% 1.77/1.16  
% 1.77/1.16  #Partial instantiations: 0
% 1.77/1.16  #Strategies tried      : 1
% 1.77/1.16  
% 1.77/1.16  Timing (in seconds)
% 1.77/1.16  ----------------------
% 1.77/1.16  Preprocessing        : 0.29
% 1.77/1.16  Parsing              : 0.16
% 1.77/1.16  CNF conversion       : 0.02
% 1.77/1.16  Main loop            : 0.12
% 1.77/1.16  Inferencing          : 0.05
% 1.77/1.16  Reduction            : 0.04
% 1.77/1.16  Demodulation         : 0.03
% 1.77/1.16  BG Simplification    : 0.01
% 1.77/1.16  Subsumption          : 0.02
% 1.77/1.16  Abstraction          : 0.01
% 1.77/1.16  MUC search           : 0.00
% 1.77/1.16  Cooper               : 0.00
% 1.77/1.16  Total                : 0.44
% 1.77/1.16  Index Insertion      : 0.00
% 1.77/1.16  Index Deletion       : 0.00
% 1.77/1.17  Index Matching       : 0.00
% 1.77/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
