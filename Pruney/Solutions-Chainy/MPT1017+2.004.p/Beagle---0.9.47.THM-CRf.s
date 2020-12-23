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
% DateTime   : Thu Dec  3 10:15:45 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 ( 162 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( ( v2_funct_1(B)
            & k2_relset_1(A,A,B) = A )
         => ( v1_funct_1(B)
            & v1_funct_2(B,A,A)
            & v3_funct_2(B,A,A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) )
       => ( v1_funct_1(C)
          & v3_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_2)).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    ~ v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_26])).

tff(c_30,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53,plain,(
    ! [B_23,A_24] :
      ( v1_relat_1(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_24))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_59,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_56])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_87,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_relset_1(A_34,B_35,C_36) = k2_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_90,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_92,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_90])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_25,A_26] :
      ( v5_relat_1(B_25,A_26)
      | ~ r1_tarski(k2_relat_1(B_25),A_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,(
    ! [B_25] :
      ( v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_75,plain,(
    ! [B_30] :
      ( v2_funct_2(B_30,k2_relat_1(B_30))
      | ~ v5_relat_1(B_30,k2_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_79,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_65,c_75])).

tff(c_96,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_79])).

tff(c_109,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_96])).

tff(c_179,plain,(
    ! [C_42,A_43,B_44] :
      ( v3_funct_2(C_42,A_43,B_44)
      | ~ v2_funct_2(C_42,B_44)
      | ~ v2_funct_1(C_42)
      | ~ v1_funct_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_182,plain,
    ( v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_179])).

tff(c_185,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_109,c_182])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:02:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.21  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.94/1.21  
% 1.94/1.21  %Foreground sorts:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Background operators:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Foreground operators:
% 1.94/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.94/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.94/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.21  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 1.94/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.94/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.21  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 1.94/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.21  
% 1.94/1.22  tff(f_89, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((v2_funct_1(B) & (k2_relset_1(A, A, B) = A)) => (((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_funct_2)).
% 1.94/1.22  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.94/1.22  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.94/1.22  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.94/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.94/1.22  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.94/1.22  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 1.94/1.22  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B)) => (v1_funct_1(C) & v3_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_funct_2)).
% 1.94/1.22  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.22  tff(c_34, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.22  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.22  tff(c_26, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.22  tff(c_38, plain, (~v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_26])).
% 1.94/1.22  tff(c_30, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.22  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.22  tff(c_53, plain, (![B_23, A_24]: (v1_relat_1(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_24)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.22  tff(c_56, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_53])).
% 1.94/1.22  tff(c_59, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_56])).
% 1.94/1.22  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.22  tff(c_87, plain, (![A_34, B_35, C_36]: (k2_relset_1(A_34, B_35, C_36)=k2_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.94/1.22  tff(c_90, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_87])).
% 1.94/1.22  tff(c_92, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_90])).
% 1.94/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.22  tff(c_60, plain, (![B_25, A_26]: (v5_relat_1(B_25, A_26) | ~r1_tarski(k2_relat_1(B_25), A_26) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.94/1.22  tff(c_65, plain, (![B_25]: (v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_6, c_60])).
% 1.94/1.22  tff(c_75, plain, (![B_30]: (v2_funct_2(B_30, k2_relat_1(B_30)) | ~v5_relat_1(B_30, k2_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.22  tff(c_79, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_65, c_75])).
% 1.94/1.22  tff(c_96, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_79])).
% 1.94/1.22  tff(c_109, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_96])).
% 1.94/1.22  tff(c_179, plain, (![C_42, A_43, B_44]: (v3_funct_2(C_42, A_43, B_44) | ~v2_funct_2(C_42, B_44) | ~v2_funct_1(C_42) | ~v1_funct_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.94/1.22  tff(c_182, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v2_funct_2('#skF_2', '#skF_1') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_179])).
% 1.94/1.22  tff(c_185, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_109, c_182])).
% 1.94/1.22  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_185])).
% 1.94/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  Inference rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Ref     : 0
% 1.94/1.22  #Sup     : 27
% 1.94/1.22  #Fact    : 0
% 1.94/1.22  #Define  : 0
% 1.94/1.22  #Split   : 0
% 1.94/1.22  #Chain   : 0
% 1.94/1.22  #Close   : 0
% 1.94/1.22  
% 1.94/1.22  Ordering : KBO
% 1.94/1.22  
% 1.94/1.22  Simplification rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Subsume      : 1
% 1.94/1.22  #Demod        : 29
% 1.94/1.22  #Tautology    : 16
% 1.94/1.22  #SimpNegUnit  : 1
% 1.94/1.22  #BackRed      : 0
% 1.94/1.22  
% 1.94/1.22  #Partial instantiations: 0
% 1.94/1.22  #Strategies tried      : 1
% 1.94/1.22  
% 1.94/1.22  Timing (in seconds)
% 1.94/1.22  ----------------------
% 2.05/1.22  Preprocessing        : 0.30
% 2.05/1.22  Parsing              : 0.16
% 2.05/1.22  CNF conversion       : 0.02
% 2.05/1.22  Main loop            : 0.14
% 2.05/1.22  Inferencing          : 0.05
% 2.05/1.22  Reduction            : 0.05
% 2.05/1.22  Demodulation         : 0.04
% 2.05/1.22  BG Simplification    : 0.01
% 2.05/1.22  Subsumption          : 0.02
% 2.05/1.22  Abstraction          : 0.01
% 2.05/1.22  MUC search           : 0.00
% 2.05/1.22  Cooper               : 0.00
% 2.05/1.22  Total                : 0.47
% 2.05/1.22  Index Insertion      : 0.00
% 2.05/1.22  Index Deletion       : 0.00
% 2.05/1.22  Index Matching       : 0.00
% 2.05/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
