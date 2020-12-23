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
% DateTime   : Thu Dec  3 10:13:45 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   48 (  76 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 135 expanded)
%              Number of equality atoms :   14 (  18 expanded)
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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_53,plain,(
    ! [A_31,B_32,D_33] :
      ( r2_relset_1(A_31,B_32,D_33,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_27,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_31,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_27])).

tff(c_32,plain,(
    ! [C_23,A_24,B_25] :
      ( v4_relat_1(C_23,A_24)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_32])).

tff(c_37,plain,(
    ! [B_26,A_27] :
      ( k7_relat_1(B_26,A_27) = B_26
      | ~ v4_relat_1(B_26,A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_37])).

tff(c_43,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_40])).

tff(c_57,plain,(
    ! [C_34,A_35,B_36] :
      ( k7_relat_1(k7_relat_1(C_34,A_35),B_36) = k7_relat_1(C_34,A_35)
      | ~ r1_tarski(A_35,B_36)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [B_36] :
      ( k7_relat_1('#skF_4',B_36) = k7_relat_1('#skF_4','#skF_1')
      | ~ r1_tarski('#skF_1',B_36)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_57])).

tff(c_77,plain,(
    ! [B_37] :
      ( k7_relat_1('#skF_4',B_37) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_43,c_72])).

tff(c_81,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_92,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k2_partfun1(A_39,B_40,C_41,D_42) = k7_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [D_42] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_42) = k7_relat_1('#skF_4',D_42)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_92])).

tff(c_97,plain,(
    ! [D_42] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_42) = k7_relat_1('#skF_4',D_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_94])).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_98,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_18])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_81,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.15  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.15  
% 1.87/1.15  %Foreground sorts:
% 1.87/1.15  
% 1.87/1.15  
% 1.87/1.15  %Background operators:
% 1.87/1.15  
% 1.87/1.15  
% 1.87/1.15  %Foreground operators:
% 1.87/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.87/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.87/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.87/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.87/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.15  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.87/1.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.87/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.15  
% 1.87/1.17  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 1.87/1.17  tff(f_55, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.87/1.17  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.87/1.17  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.87/1.17  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.87/1.17  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.87/1.17  tff(f_61, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.87/1.17  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.17  tff(c_53, plain, (![A_31, B_32, D_33]: (r2_relset_1(A_31, B_32, D_33, D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.17  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_53])).
% 1.87/1.17  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.17  tff(c_27, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.17  tff(c_31, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_27])).
% 1.87/1.17  tff(c_32, plain, (![C_23, A_24, B_25]: (v4_relat_1(C_23, A_24) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.17  tff(c_36, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_32])).
% 1.87/1.17  tff(c_37, plain, (![B_26, A_27]: (k7_relat_1(B_26, A_27)=B_26 | ~v4_relat_1(B_26, A_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.17  tff(c_40, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_37])).
% 1.87/1.17  tff(c_43, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31, c_40])).
% 1.87/1.17  tff(c_57, plain, (![C_34, A_35, B_36]: (k7_relat_1(k7_relat_1(C_34, A_35), B_36)=k7_relat_1(C_34, A_35) | ~r1_tarski(A_35, B_36) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.17  tff(c_72, plain, (![B_36]: (k7_relat_1('#skF_4', B_36)=k7_relat_1('#skF_4', '#skF_1') | ~r1_tarski('#skF_1', B_36) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_57])).
% 1.87/1.17  tff(c_77, plain, (![B_37]: (k7_relat_1('#skF_4', B_37)='#skF_4' | ~r1_tarski('#skF_1', B_37))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_43, c_72])).
% 1.87/1.17  tff(c_81, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_77])).
% 1.87/1.17  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.17  tff(c_92, plain, (![A_39, B_40, C_41, D_42]: (k2_partfun1(A_39, B_40, C_41, D_42)=k7_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.87/1.17  tff(c_94, plain, (![D_42]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_42)=k7_relat_1('#skF_4', D_42) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_92])).
% 1.87/1.17  tff(c_97, plain, (![D_42]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_42)=k7_relat_1('#skF_4', D_42))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_94])).
% 1.87/1.17  tff(c_18, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.17  tff(c_98, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_18])).
% 1.87/1.17  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_81, c_98])).
% 1.87/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  Inference rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Ref     : 0
% 1.87/1.17  #Sup     : 17
% 1.87/1.17  #Fact    : 0
% 1.87/1.17  #Define  : 0
% 1.87/1.17  #Split   : 0
% 1.87/1.17  #Chain   : 0
% 1.87/1.17  #Close   : 0
% 1.87/1.17  
% 1.87/1.17  Ordering : KBO
% 1.87/1.17  
% 1.87/1.17  Simplification rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Subsume      : 0
% 1.87/1.17  #Demod        : 9
% 1.87/1.17  #Tautology    : 6
% 1.87/1.17  #SimpNegUnit  : 0
% 1.87/1.17  #BackRed      : 1
% 1.87/1.17  
% 1.87/1.17  #Partial instantiations: 0
% 1.87/1.17  #Strategies tried      : 1
% 1.87/1.17  
% 1.87/1.17  Timing (in seconds)
% 1.87/1.17  ----------------------
% 1.87/1.17  Preprocessing        : 0.29
% 1.87/1.17  Parsing              : 0.15
% 1.87/1.17  CNF conversion       : 0.02
% 1.87/1.17  Main loop            : 0.12
% 1.87/1.17  Inferencing          : 0.05
% 1.87/1.17  Reduction            : 0.04
% 1.87/1.17  Demodulation         : 0.03
% 1.87/1.17  BG Simplification    : 0.01
% 1.87/1.17  Subsumption          : 0.02
% 1.87/1.17  Abstraction          : 0.01
% 1.87/1.17  MUC search           : 0.00
% 1.87/1.17  Cooper               : 0.00
% 1.87/1.17  Total                : 0.44
% 1.87/1.17  Index Insertion      : 0.00
% 1.87/1.17  Index Deletion       : 0.00
% 1.87/1.17  Index Matching       : 0.00
% 1.87/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
