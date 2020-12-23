%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:48 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 119 expanded)
%              Number of equality atoms :   10 (  10 expanded)
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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,(
    ! [A_38,B_39,D_40] :
      ( r2_relset_1(A_38,B_39,D_40,D_40)
      | ~ m1_subset_1(D_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_67,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    ! [B_25,A_26] :
      ( v1_relat_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_33])).

tff(c_43,plain,(
    ! [C_32,A_33,B_34] :
      ( v4_relat_1(C_32,A_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_47,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_58,plain,(
    ! [C_35,B_36,A_37] :
      ( v4_relat_1(C_35,B_36)
      | ~ v4_relat_1(C_35,A_37)
      | ~ v1_relat_1(C_35)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [B_36] :
      ( v4_relat_1('#skF_4',B_36)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_36) ) ),
    inference(resolution,[status(thm)],[c_47,c_58])).

tff(c_68,plain,(
    ! [B_41] :
      ( v4_relat_1('#skF_4',B_41)
      | ~ r1_tarski('#skF_1',B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [B_41] :
      ( k7_relat_1('#skF_4',B_41) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_41) ) ),
    inference(resolution,[status(thm)],[c_68,c_6])).

tff(c_80,plain,(
    ! [B_42] :
      ( k7_relat_1('#skF_4',B_42) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_73])).

tff(c_84,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_94,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k2_partfun1(A_45,B_46,C_47,D_48) = k7_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_96,plain,(
    ! [D_48] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_48) = k7_relat_1('#skF_4',D_48)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_94])).

tff(c_99,plain,(
    ! [D_48] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_48) = k7_relat_1('#skF_4',D_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_96])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_20])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_84,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.20  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.83/1.20  
% 1.83/1.20  %Foreground sorts:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Background operators:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Foreground operators:
% 1.83/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.20  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.83/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.83/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.83/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.83/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.20  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.83/1.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.83/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.20  
% 1.83/1.22  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 1.83/1.22  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.83/1.22  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.83/1.22  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.83/1.22  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.83/1.22  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 1.83/1.22  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.83/1.22  tff(f_69, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.83/1.22  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.83/1.22  tff(c_64, plain, (![A_38, B_39, D_40]: (r2_relset_1(A_38, B_39, D_40, D_40) | ~m1_subset_1(D_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.83/1.22  tff(c_67, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_64])).
% 1.83/1.22  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.83/1.22  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.83/1.22  tff(c_30, plain, (![B_25, A_26]: (v1_relat_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.22  tff(c_33, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_30])).
% 1.83/1.22  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_33])).
% 1.83/1.22  tff(c_43, plain, (![C_32, A_33, B_34]: (v4_relat_1(C_32, A_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.22  tff(c_47, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_43])).
% 1.83/1.22  tff(c_58, plain, (![C_35, B_36, A_37]: (v4_relat_1(C_35, B_36) | ~v4_relat_1(C_35, A_37) | ~v1_relat_1(C_35) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.83/1.22  tff(c_60, plain, (![B_36]: (v4_relat_1('#skF_4', B_36) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_36))), inference(resolution, [status(thm)], [c_47, c_58])).
% 1.83/1.22  tff(c_68, plain, (![B_41]: (v4_relat_1('#skF_4', B_41) | ~r1_tarski('#skF_1', B_41))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60])).
% 1.83/1.22  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.22  tff(c_73, plain, (![B_41]: (k7_relat_1('#skF_4', B_41)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_41))), inference(resolution, [status(thm)], [c_68, c_6])).
% 1.83/1.22  tff(c_80, plain, (![B_42]: (k7_relat_1('#skF_4', B_42)='#skF_4' | ~r1_tarski('#skF_1', B_42))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_73])).
% 1.83/1.22  tff(c_84, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_22, c_80])).
% 1.83/1.22  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.83/1.22  tff(c_94, plain, (![A_45, B_46, C_47, D_48]: (k2_partfun1(A_45, B_46, C_47, D_48)=k7_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.83/1.22  tff(c_96, plain, (![D_48]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_48)=k7_relat_1('#skF_4', D_48) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_94])).
% 1.83/1.22  tff(c_99, plain, (![D_48]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_48)=k7_relat_1('#skF_4', D_48))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_96])).
% 1.83/1.22  tff(c_20, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.83/1.22  tff(c_100, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_20])).
% 1.83/1.22  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_84, c_100])).
% 1.83/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.22  
% 1.83/1.22  Inference rules
% 1.83/1.22  ----------------------
% 1.83/1.22  #Ref     : 0
% 1.83/1.22  #Sup     : 15
% 1.83/1.22  #Fact    : 0
% 1.83/1.22  #Define  : 0
% 1.83/1.22  #Split   : 1
% 1.83/1.22  #Chain   : 0
% 1.83/1.22  #Close   : 0
% 1.83/1.22  
% 1.83/1.22  Ordering : KBO
% 1.83/1.22  
% 1.83/1.22  Simplification rules
% 1.83/1.22  ----------------------
% 1.83/1.22  #Subsume      : 0
% 1.83/1.22  #Demod        : 9
% 1.83/1.22  #Tautology    : 4
% 1.83/1.22  #SimpNegUnit  : 0
% 1.83/1.22  #BackRed      : 1
% 1.83/1.22  
% 1.83/1.22  #Partial instantiations: 0
% 1.83/1.22  #Strategies tried      : 1
% 1.83/1.22  
% 1.83/1.22  Timing (in seconds)
% 1.83/1.22  ----------------------
% 1.83/1.22  Preprocessing        : 0.30
% 1.83/1.22  Parsing              : 0.16
% 1.83/1.22  CNF conversion       : 0.02
% 1.83/1.22  Main loop            : 0.14
% 1.83/1.22  Inferencing          : 0.05
% 1.83/1.22  Reduction            : 0.04
% 1.83/1.22  Demodulation         : 0.03
% 1.83/1.22  BG Simplification    : 0.01
% 1.83/1.22  Subsumption          : 0.03
% 1.83/1.22  Abstraction          : 0.01
% 1.83/1.22  MUC search           : 0.00
% 1.83/1.22  Cooper               : 0.00
% 1.83/1.22  Total                : 0.46
% 1.83/1.22  Index Insertion      : 0.00
% 1.83/1.22  Index Deletion       : 0.00
% 1.83/1.22  Index Matching       : 0.00
% 1.83/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
