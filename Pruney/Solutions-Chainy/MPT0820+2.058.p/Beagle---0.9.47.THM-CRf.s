%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:08 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   63 (  81 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_16,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_64])).

tff(c_85,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_94,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_173,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1(k1_relset_1(A_63,B_64,C_65),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_190,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_173])).

tff(c_196,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_190])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_204,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_196,c_8])).

tff(c_105,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_114,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_105])).

tff(c_136,plain,(
    ! [A_60,B_61,C_62] :
      ( m1_subset_1(k2_relset_1(A_60,B_61,C_62),k1_zfmisc_1(B_61))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_153,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_136])).

tff(c_159,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_153])).

tff(c_167,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_159,c_8])).

tff(c_14,plain,(
    ! [A_14] :
      ( k2_xboole_0(k1_relat_1(A_14),k2_relat_1(A_14)) = k3_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    ! [A_56,C_57,B_58,D_59] :
      ( r1_tarski(k2_xboole_0(A_56,C_57),k2_xboole_0(B_58,D_59))
      | ~ r1_tarski(C_57,D_59)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_361,plain,(
    ! [A_94,B_95,D_96] :
      ( r1_tarski(k3_relat_1(A_94),k2_xboole_0(B_95,D_96))
      | ~ r1_tarski(k2_relat_1(A_94),D_96)
      | ~ r1_tarski(k1_relat_1(A_94),B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_125])).

tff(c_26,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_367,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_26])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_204,c_167,c_367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.31  
% 2.07/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.31  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.33/1.31  
% 2.33/1.31  %Foreground sorts:
% 2.33/1.31  
% 2.33/1.31  
% 2.33/1.31  %Background operators:
% 2.33/1.31  
% 2.33/1.31  
% 2.33/1.31  %Foreground operators:
% 2.33/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.33/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.31  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.33/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.33/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.33/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.31  
% 2.33/1.32  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.33/1.32  tff(f_73, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 2.33/1.32  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.33/1.32  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.33/1.32  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.33/1.32  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.33/1.32  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.33/1.32  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.33/1.32  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.33/1.32  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 2.33/1.32  tff(c_16, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.32  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.33/1.32  tff(c_58, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.33/1.32  tff(c_64, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_58])).
% 2.33/1.32  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_64])).
% 2.33/1.32  tff(c_85, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.32  tff(c_94, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_85])).
% 2.33/1.32  tff(c_173, plain, (![A_63, B_64, C_65]: (m1_subset_1(k1_relset_1(A_63, B_64, C_65), k1_zfmisc_1(A_63)) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.33/1.32  tff(c_190, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_173])).
% 2.33/1.32  tff(c_196, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_190])).
% 2.33/1.32  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.32  tff(c_204, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_196, c_8])).
% 2.33/1.32  tff(c_105, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.33/1.32  tff(c_114, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_105])).
% 2.33/1.32  tff(c_136, plain, (![A_60, B_61, C_62]: (m1_subset_1(k2_relset_1(A_60, B_61, C_62), k1_zfmisc_1(B_61)) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.32  tff(c_153, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_114, c_136])).
% 2.33/1.32  tff(c_159, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_153])).
% 2.33/1.32  tff(c_167, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_159, c_8])).
% 2.33/1.32  tff(c_14, plain, (![A_14]: (k2_xboole_0(k1_relat_1(A_14), k2_relat_1(A_14))=k3_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.32  tff(c_125, plain, (![A_56, C_57, B_58, D_59]: (r1_tarski(k2_xboole_0(A_56, C_57), k2_xboole_0(B_58, D_59)) | ~r1_tarski(C_57, D_59) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.32  tff(c_361, plain, (![A_94, B_95, D_96]: (r1_tarski(k3_relat_1(A_94), k2_xboole_0(B_95, D_96)) | ~r1_tarski(k2_relat_1(A_94), D_96) | ~r1_tarski(k1_relat_1(A_94), B_95) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_14, c_125])).
% 2.33/1.32  tff(c_26, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.33/1.32  tff(c_367, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_361, c_26])).
% 2.33/1.32  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_204, c_167, c_367])).
% 2.33/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.32  
% 2.33/1.32  Inference rules
% 2.33/1.32  ----------------------
% 2.33/1.32  #Ref     : 0
% 2.33/1.32  #Sup     : 74
% 2.33/1.32  #Fact    : 0
% 2.33/1.32  #Define  : 0
% 2.33/1.32  #Split   : 2
% 2.33/1.32  #Chain   : 0
% 2.33/1.32  #Close   : 0
% 2.33/1.32  
% 2.33/1.32  Ordering : KBO
% 2.33/1.32  
% 2.33/1.32  Simplification rules
% 2.33/1.32  ----------------------
% 2.33/1.32  #Subsume      : 8
% 2.33/1.32  #Demod        : 22
% 2.33/1.32  #Tautology    : 18
% 2.33/1.32  #SimpNegUnit  : 0
% 2.33/1.32  #BackRed      : 0
% 2.33/1.32  
% 2.33/1.32  #Partial instantiations: 0
% 2.33/1.32  #Strategies tried      : 1
% 2.33/1.32  
% 2.33/1.32  Timing (in seconds)
% 2.33/1.32  ----------------------
% 2.33/1.33  Preprocessing        : 0.30
% 2.33/1.33  Parsing              : 0.17
% 2.33/1.33  CNF conversion       : 0.02
% 2.33/1.33  Main loop            : 0.23
% 2.33/1.33  Inferencing          : 0.09
% 2.33/1.33  Reduction            : 0.06
% 2.33/1.33  Demodulation         : 0.05
% 2.33/1.33  BG Simplification    : 0.01
% 2.33/1.33  Subsumption          : 0.04
% 2.33/1.33  Abstraction          : 0.02
% 2.33/1.33  MUC search           : 0.00
% 2.33/1.33  Cooper               : 0.00
% 2.33/1.33  Total                : 0.56
% 2.33/1.33  Index Insertion      : 0.00
% 2.33/1.33  Index Deletion       : 0.00
% 2.33/1.33  Index Matching       : 0.00
% 2.33/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
