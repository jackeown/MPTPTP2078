%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:46 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   50 (  80 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 144 expanded)
%              Number of equality atoms :   13 (  17 expanded)
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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_25,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_29,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_35,plain,(
    ! [C_26,A_27,B_28] :
      ( v4_relat_1(C_26,A_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_40,plain,(
    ! [B_29,A_30] :
      ( k7_relat_1(B_29,A_30) = B_29
      | ~ v4_relat_1(B_29,A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_39,c_40])).

tff(c_46,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_43])).

tff(c_51,plain,(
    ! [C_31,A_32,B_33] :
      ( k7_relat_1(k7_relat_1(C_31,A_32),B_33) = k7_relat_1(C_31,A_32)
      | ~ r1_tarski(A_32,B_33)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [B_33] :
      ( k7_relat_1('#skF_4',B_33) = k7_relat_1('#skF_4','#skF_1')
      | ~ r1_tarski('#skF_1',B_33)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_51])).

tff(c_71,plain,(
    ! [B_34] :
      ( k7_relat_1('#skF_4',B_34) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_46,c_66])).

tff(c_75,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( k2_partfun1(A_35,B_36,C_37,D_38) = k7_relat_1(C_37,D_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_78,plain,(
    ! [D_38] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_38) = k7_relat_1('#skF_4',D_38)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_76])).

tff(c_81,plain,(
    ! [D_38] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_38) = k7_relat_1('#skF_4',D_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_78])).

tff(c_16,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_16])).

tff(c_93,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_92])).

tff(c_103,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( r2_relset_1(A_41,B_42,C_43,C_43)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    ! [C_45] :
      ( r2_relset_1('#skF_1','#skF_2',C_45,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_103])).

tff(c_109,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_107])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:25:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.16  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.89/1.16  
% 1.89/1.16  %Foreground sorts:
% 1.89/1.16  
% 1.89/1.16  
% 1.89/1.16  %Background operators:
% 1.89/1.16  
% 1.89/1.16  
% 1.89/1.16  %Foreground operators:
% 1.89/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.89/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.89/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.89/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.16  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.89/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.89/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.16  
% 1.89/1.17  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 1.89/1.17  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.89/1.17  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.89/1.17  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.89/1.17  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.89/1.17  tff(f_59, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.89/1.17  tff(f_53, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 1.89/1.17  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.89/1.17  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.89/1.17  tff(c_25, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.89/1.17  tff(c_29, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_25])).
% 1.89/1.17  tff(c_35, plain, (![C_26, A_27, B_28]: (v4_relat_1(C_26, A_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.89/1.17  tff(c_39, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_35])).
% 1.89/1.17  tff(c_40, plain, (![B_29, A_30]: (k7_relat_1(B_29, A_30)=B_29 | ~v4_relat_1(B_29, A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.17  tff(c_43, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_39, c_40])).
% 1.89/1.17  tff(c_46, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29, c_43])).
% 1.89/1.17  tff(c_51, plain, (![C_31, A_32, B_33]: (k7_relat_1(k7_relat_1(C_31, A_32), B_33)=k7_relat_1(C_31, A_32) | ~r1_tarski(A_32, B_33) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.17  tff(c_66, plain, (![B_33]: (k7_relat_1('#skF_4', B_33)=k7_relat_1('#skF_4', '#skF_1') | ~r1_tarski('#skF_1', B_33) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_51])).
% 1.89/1.17  tff(c_71, plain, (![B_34]: (k7_relat_1('#skF_4', B_34)='#skF_4' | ~r1_tarski('#skF_1', B_34))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_46, c_66])).
% 1.89/1.17  tff(c_75, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_18, c_71])).
% 1.89/1.17  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.89/1.17  tff(c_76, plain, (![A_35, B_36, C_37, D_38]: (k2_partfun1(A_35, B_36, C_37, D_38)=k7_relat_1(C_37, D_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.89/1.17  tff(c_78, plain, (![D_38]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_38)=k7_relat_1('#skF_4', D_38) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_76])).
% 1.89/1.17  tff(c_81, plain, (![D_38]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_38)=k7_relat_1('#skF_4', D_38))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_78])).
% 1.89/1.17  tff(c_16, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.89/1.17  tff(c_92, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_16])).
% 1.89/1.17  tff(c_93, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_92])).
% 1.89/1.17  tff(c_103, plain, (![A_41, B_42, C_43, D_44]: (r2_relset_1(A_41, B_42, C_43, C_43) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.17  tff(c_107, plain, (![C_45]: (r2_relset_1('#skF_1', '#skF_2', C_45, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_20, c_103])).
% 1.89/1.17  tff(c_109, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_107])).
% 1.89/1.17  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_109])).
% 1.89/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  Inference rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Ref     : 0
% 1.89/1.17  #Sup     : 20
% 1.89/1.17  #Fact    : 0
% 1.89/1.17  #Define  : 0
% 1.89/1.17  #Split   : 0
% 1.89/1.17  #Chain   : 0
% 1.89/1.17  #Close   : 0
% 1.89/1.17  
% 1.89/1.17  Ordering : KBO
% 1.89/1.17  
% 1.89/1.17  Simplification rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Subsume      : 0
% 1.89/1.17  #Demod        : 8
% 1.89/1.17  #Tautology    : 8
% 1.89/1.17  #SimpNegUnit  : 1
% 1.89/1.17  #BackRed      : 1
% 1.89/1.17  
% 1.89/1.17  #Partial instantiations: 0
% 1.89/1.17  #Strategies tried      : 1
% 1.89/1.17  
% 1.89/1.17  Timing (in seconds)
% 1.89/1.17  ----------------------
% 1.89/1.17  Preprocessing        : 0.29
% 1.89/1.17  Parsing              : 0.16
% 1.89/1.17  CNF conversion       : 0.02
% 1.89/1.17  Main loop            : 0.12
% 1.89/1.17  Inferencing          : 0.05
% 1.89/1.17  Reduction            : 0.04
% 1.89/1.17  Demodulation         : 0.03
% 1.89/1.17  BG Simplification    : 0.01
% 1.89/1.17  Subsumption          : 0.02
% 1.89/1.17  Abstraction          : 0.01
% 1.89/1.17  MUC search           : 0.00
% 1.89/1.17  Cooper               : 0.00
% 1.89/1.17  Total                : 0.44
% 1.89/1.17  Index Insertion      : 0.00
% 1.89/1.17  Index Deletion       : 0.00
% 1.89/1.17  Index Matching       : 0.00
% 1.89/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
