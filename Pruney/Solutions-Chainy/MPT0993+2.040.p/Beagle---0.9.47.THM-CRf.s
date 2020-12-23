%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:48 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   51 (  85 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 153 expanded)
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

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_60,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    ! [A_34,B_35,D_36] :
      ( r2_relset_1(A_34,B_35,D_36,D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_58])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_33])).

tff(c_43,plain,(
    ! [C_31,A_32,B_33] :
      ( v4_relat_1(C_31,A_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_47,c_8])).

tff(c_53,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_50])).

tff(c_62,plain,(
    ! [C_37,A_38,B_39] :
      ( k7_relat_1(k7_relat_1(C_37,A_38),B_39) = k7_relat_1(C_37,A_38)
      | ~ r1_tarski(A_38,B_39)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_77,plain,(
    ! [B_39] :
      ( k7_relat_1('#skF_4',B_39) = k7_relat_1('#skF_4','#skF_1')
      | ~ r1_tarski('#skF_1',B_39)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_62])).

tff(c_82,plain,(
    ! [B_40] :
      ( k7_relat_1('#skF_4',B_40) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_53,c_77])).

tff(c_86,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_97,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k2_partfun1(A_42,B_43,C_44,D_45) = k7_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_99,plain,(
    ! [D_45] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_45) = k7_relat_1('#skF_4',D_45)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_97])).

tff(c_102,plain,(
    ! [D_45] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_45) = k7_relat_1('#skF_4',D_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_99])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_20])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_86,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.16  
% 2.02/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.17  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.17  
% 2.02/1.17  %Foreground sorts:
% 2.02/1.17  
% 2.02/1.17  
% 2.02/1.17  %Background operators:
% 2.02/1.17  
% 2.02/1.17  
% 2.02/1.17  %Foreground operators:
% 2.02/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.17  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.02/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.02/1.17  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.17  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.17  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.02/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.17  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.17  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.02/1.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.02/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.17  
% 2.13/1.18  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.13/1.18  tff(f_60, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.13/1.18  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.13/1.18  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.13/1.18  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.13/1.18  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.13/1.18  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 2.13/1.18  tff(f_66, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.13/1.18  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.13/1.18  tff(c_58, plain, (![A_34, B_35, D_36]: (r2_relset_1(A_34, B_35, D_36, D_36) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.18  tff(c_61, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_58])).
% 2.13/1.18  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.13/1.18  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.13/1.18  tff(c_30, plain, (![B_24, A_25]: (v1_relat_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.18  tff(c_33, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_30])).
% 2.13/1.18  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_33])).
% 2.13/1.18  tff(c_43, plain, (![C_31, A_32, B_33]: (v4_relat_1(C_31, A_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.13/1.18  tff(c_47, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_43])).
% 2.13/1.18  tff(c_8, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.18  tff(c_50, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_47, c_8])).
% 2.13/1.18  tff(c_53, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_50])).
% 2.13/1.18  tff(c_62, plain, (![C_37, A_38, B_39]: (k7_relat_1(k7_relat_1(C_37, A_38), B_39)=k7_relat_1(C_37, A_38) | ~r1_tarski(A_38, B_39) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.13/1.18  tff(c_77, plain, (![B_39]: (k7_relat_1('#skF_4', B_39)=k7_relat_1('#skF_4', '#skF_1') | ~r1_tarski('#skF_1', B_39) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_62])).
% 2.13/1.18  tff(c_82, plain, (![B_40]: (k7_relat_1('#skF_4', B_40)='#skF_4' | ~r1_tarski('#skF_1', B_40))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_53, c_77])).
% 2.13/1.18  tff(c_86, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_22, c_82])).
% 2.13/1.18  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.13/1.18  tff(c_97, plain, (![A_42, B_43, C_44, D_45]: (k2_partfun1(A_42, B_43, C_44, D_45)=k7_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.18  tff(c_99, plain, (![D_45]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_45)=k7_relat_1('#skF_4', D_45) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_97])).
% 2.13/1.18  tff(c_102, plain, (![D_45]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_45)=k7_relat_1('#skF_4', D_45))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_99])).
% 2.13/1.18  tff(c_20, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.13/1.18  tff(c_103, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_20])).
% 2.13/1.18  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_86, c_103])).
% 2.13/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.18  
% 2.13/1.18  Inference rules
% 2.13/1.18  ----------------------
% 2.13/1.18  #Ref     : 0
% 2.13/1.18  #Sup     : 17
% 2.13/1.18  #Fact    : 0
% 2.13/1.18  #Define  : 0
% 2.13/1.18  #Split   : 0
% 2.13/1.18  #Chain   : 0
% 2.13/1.18  #Close   : 0
% 2.13/1.18  
% 2.13/1.18  Ordering : KBO
% 2.13/1.18  
% 2.13/1.18  Simplification rules
% 2.13/1.18  ----------------------
% 2.13/1.18  #Subsume      : 0
% 2.13/1.18  #Demod        : 10
% 2.13/1.18  #Tautology    : 6
% 2.13/1.18  #SimpNegUnit  : 0
% 2.13/1.18  #BackRed      : 1
% 2.13/1.18  
% 2.13/1.18  #Partial instantiations: 0
% 2.13/1.18  #Strategies tried      : 1
% 2.13/1.18  
% 2.13/1.18  Timing (in seconds)
% 2.13/1.18  ----------------------
% 2.13/1.18  Preprocessing        : 0.30
% 2.13/1.18  Parsing              : 0.16
% 2.13/1.18  CNF conversion       : 0.02
% 2.13/1.18  Main loop            : 0.12
% 2.13/1.18  Inferencing          : 0.04
% 2.13/1.18  Reduction            : 0.04
% 2.13/1.18  Demodulation         : 0.03
% 2.13/1.18  BG Simplification    : 0.01
% 2.13/1.18  Subsumption          : 0.01
% 2.13/1.18  Abstraction          : 0.01
% 2.13/1.18  MUC search           : 0.00
% 2.13/1.18  Cooper               : 0.00
% 2.13/1.18  Total                : 0.44
% 2.13/1.18  Index Insertion      : 0.00
% 2.13/1.18  Index Deletion       : 0.00
% 2.13/1.18  Index Matching       : 0.00
% 2.13/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
