%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:18 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   52 (  77 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 127 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_51,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_55,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_45,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_56,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_45])).

tff(c_23,plain,(
    ! [C_18,A_19,B_20] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_23])).

tff(c_34,plain,(
    ! [C_26,A_27,B_28] :
      ( v4_relat_1(C_26,A_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_34])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_44,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_41])).

tff(c_20,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,(
    ! [C_40,A_41,B_42,D_43] :
      ( r1_tarski(C_40,k1_relset_1(A_41,B_42,D_43))
      | ~ r1_tarski(k6_relat_1(C_40),D_43)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    ! [A_44,B_45] :
      ( r1_tarski('#skF_2',k1_relset_1(A_44,B_45,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_77,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_79,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_77])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k1_relat_1(k7_relat_1(B_4,A_3)) = A_3
      | ~ r1_tarski(A_3,k1_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_4])).

tff(c_85,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_44,c_82])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_85])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_157,plain,(
    ! [C_60,A_61,B_62,D_63] :
      ( r1_tarski(C_60,k2_relset_1(A_61,B_62,D_63))
      | ~ r1_tarski(k6_relat_1(C_60),D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_161,plain,(
    ! [A_64,B_65] :
      ( r1_tarski('#skF_2',k2_relset_1(A_64,B_65,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_164,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_161])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:56:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.19  
% 1.89/1.19  %Foreground sorts:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Background operators:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Foreground operators:
% 1.89/1.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.89/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.89/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.89/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.19  
% 1.89/1.20  tff(f_68, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relset_1)).
% 1.89/1.20  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.89/1.20  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.89/1.20  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.89/1.20  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.89/1.20  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 1.89/1.20  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.89/1.20  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.89/1.20  tff(c_51, plain, (![A_31, B_32, C_33]: (k1_relset_1(A_31, B_32, C_33)=k1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.20  tff(c_55, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_51])).
% 1.89/1.20  tff(c_18, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.89/1.20  tff(c_45, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_18])).
% 1.89/1.20  tff(c_56, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_45])).
% 1.89/1.20  tff(c_23, plain, (![C_18, A_19, B_20]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.89/1.20  tff(c_27, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_23])).
% 1.89/1.20  tff(c_34, plain, (![C_26, A_27, B_28]: (v4_relat_1(C_26, A_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.89/1.20  tff(c_38, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_34])).
% 1.89/1.20  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.20  tff(c_41, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_2])).
% 1.89/1.20  tff(c_44, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_27, c_41])).
% 1.89/1.20  tff(c_20, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.89/1.20  tff(c_70, plain, (![C_40, A_41, B_42, D_43]: (r1_tarski(C_40, k1_relset_1(A_41, B_42, D_43)) | ~r1_tarski(k6_relat_1(C_40), D_43) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.89/1.20  tff(c_74, plain, (![A_44, B_45]: (r1_tarski('#skF_2', k1_relset_1(A_44, B_45, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(resolution, [status(thm)], [c_20, c_70])).
% 1.89/1.20  tff(c_77, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_74])).
% 1.89/1.20  tff(c_79, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_77])).
% 1.89/1.20  tff(c_4, plain, (![B_4, A_3]: (k1_relat_1(k7_relat_1(B_4, A_3))=A_3 | ~r1_tarski(A_3, k1_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.20  tff(c_82, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_4])).
% 1.89/1.20  tff(c_85, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27, c_44, c_82])).
% 1.89/1.20  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_85])).
% 1.89/1.20  tff(c_88, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_18])).
% 1.89/1.20  tff(c_157, plain, (![C_60, A_61, B_62, D_63]: (r1_tarski(C_60, k2_relset_1(A_61, B_62, D_63)) | ~r1_tarski(k6_relat_1(C_60), D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.89/1.20  tff(c_161, plain, (![A_64, B_65]: (r1_tarski('#skF_2', k2_relset_1(A_64, B_65, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(resolution, [status(thm)], [c_20, c_157])).
% 1.89/1.20  tff(c_164, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_161])).
% 1.89/1.20  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_164])).
% 1.89/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  Inference rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Ref     : 0
% 1.89/1.20  #Sup     : 34
% 1.89/1.20  #Fact    : 0
% 1.89/1.20  #Define  : 0
% 1.89/1.20  #Split   : 1
% 1.89/1.20  #Chain   : 0
% 1.89/1.20  #Close   : 0
% 1.89/1.20  
% 1.89/1.20  Ordering : KBO
% 1.89/1.20  
% 1.89/1.20  Simplification rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Subsume      : 1
% 1.89/1.20  #Demod        : 11
% 1.89/1.20  #Tautology    : 15
% 1.89/1.20  #SimpNegUnit  : 2
% 1.89/1.20  #BackRed      : 1
% 1.89/1.20  
% 1.89/1.20  #Partial instantiations: 0
% 1.89/1.20  #Strategies tried      : 1
% 1.89/1.20  
% 1.89/1.20  Timing (in seconds)
% 1.89/1.20  ----------------------
% 1.89/1.20  Preprocessing        : 0.28
% 1.89/1.20  Parsing              : 0.15
% 1.89/1.20  CNF conversion       : 0.02
% 1.89/1.21  Main loop            : 0.16
% 1.89/1.21  Inferencing          : 0.07
% 1.89/1.21  Reduction            : 0.05
% 1.89/1.21  Demodulation         : 0.03
% 1.89/1.21  BG Simplification    : 0.01
% 1.89/1.21  Subsumption          : 0.02
% 1.89/1.21  Abstraction          : 0.01
% 1.89/1.21  MUC search           : 0.00
% 1.89/1.21  Cooper               : 0.00
% 1.89/1.21  Total                : 0.47
% 1.89/1.21  Index Insertion      : 0.00
% 1.89/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
