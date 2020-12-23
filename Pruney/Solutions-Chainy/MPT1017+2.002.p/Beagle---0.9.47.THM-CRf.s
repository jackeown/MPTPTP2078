%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:45 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 156 expanded)
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

tff(f_84,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) )
       => ( v1_funct_1(C)
          & v3_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_2)).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ~ v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_24])).

tff(c_28,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_43,plain,(
    ! [C_17,A_18,B_19] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_26,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_82,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_relset_1(A_31,B_32,C_33) = k2_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_87,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_85])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [B_24,A_25] :
      ( v5_relat_1(B_24,A_25)
      | ~ r1_tarski(k2_relat_1(B_24),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [B_24] :
      ( v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_70,plain,(
    ! [B_27] :
      ( v2_funct_2(B_27,k2_relat_1(B_27))
      | ~ v5_relat_1(B_27,k2_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_74,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_68,c_70])).

tff(c_91,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_74])).

tff(c_104,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_91])).

tff(c_193,plain,(
    ! [C_40,A_41,B_42] :
      ( v3_funct_2(C_40,A_41,B_42)
      | ~ v2_funct_2(C_40,B_42)
      | ~ v2_funct_1(C_40)
      | ~ v1_funct_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_196,plain,
    ( v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_193])).

tff(c_199,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_104,c_196])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:43:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.15  
% 1.83/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.15  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.83/1.15  
% 1.83/1.15  %Foreground sorts:
% 1.83/1.15  
% 1.83/1.15  
% 1.83/1.15  %Background operators:
% 1.83/1.15  
% 1.83/1.15  
% 1.83/1.15  %Foreground operators:
% 1.83/1.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.83/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.83/1.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.83/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.83/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.15  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 1.83/1.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.83/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.15  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 1.83/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.15  
% 1.83/1.16  tff(f_84, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((v2_funct_1(B) & (k2_relset_1(A, A, B) = A)) => (((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_funct_2)).
% 1.83/1.16  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.83/1.16  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.83/1.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.83/1.16  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.83/1.16  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 1.83/1.16  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B)) => (v1_funct_1(C) & v3_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_funct_2)).
% 1.83/1.16  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.83/1.16  tff(c_32, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.83/1.16  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.83/1.16  tff(c_24, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.83/1.16  tff(c_36, plain, (~v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_24])).
% 1.83/1.16  tff(c_28, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.83/1.16  tff(c_43, plain, (![C_17, A_18, B_19]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.83/1.16  tff(c_47, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_43])).
% 1.83/1.16  tff(c_26, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.83/1.16  tff(c_82, plain, (![A_31, B_32, C_33]: (k2_relset_1(A_31, B_32, C_33)=k2_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.16  tff(c_85, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_82])).
% 1.83/1.16  tff(c_87, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_85])).
% 1.83/1.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.16  tff(c_59, plain, (![B_24, A_25]: (v5_relat_1(B_24, A_25) | ~r1_tarski(k2_relat_1(B_24), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.16  tff(c_68, plain, (![B_24]: (v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_6, c_59])).
% 1.83/1.16  tff(c_70, plain, (![B_27]: (v2_funct_2(B_27, k2_relat_1(B_27)) | ~v5_relat_1(B_27, k2_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.83/1.16  tff(c_74, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_68, c_70])).
% 1.83/1.16  tff(c_91, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_87, c_74])).
% 1.83/1.16  tff(c_104, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_91])).
% 1.83/1.16  tff(c_193, plain, (![C_40, A_41, B_42]: (v3_funct_2(C_40, A_41, B_42) | ~v2_funct_2(C_40, B_42) | ~v2_funct_1(C_40) | ~v1_funct_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.83/1.16  tff(c_196, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v2_funct_2('#skF_2', '#skF_1') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_193])).
% 1.83/1.16  tff(c_199, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_104, c_196])).
% 1.83/1.16  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_199])).
% 1.83/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.16  
% 1.83/1.16  Inference rules
% 1.83/1.16  ----------------------
% 1.83/1.16  #Ref     : 0
% 1.83/1.16  #Sup     : 30
% 1.83/1.16  #Fact    : 0
% 1.83/1.16  #Define  : 0
% 1.83/1.16  #Split   : 0
% 1.83/1.16  #Chain   : 0
% 1.83/1.16  #Close   : 0
% 1.83/1.16  
% 1.83/1.16  Ordering : KBO
% 1.83/1.16  
% 1.83/1.16  Simplification rules
% 1.83/1.16  ----------------------
% 1.83/1.16  #Subsume      : 2
% 1.83/1.16  #Demod        : 33
% 1.83/1.16  #Tautology    : 18
% 1.83/1.16  #SimpNegUnit  : 1
% 1.83/1.16  #BackRed      : 0
% 1.83/1.16  
% 1.83/1.16  #Partial instantiations: 0
% 1.83/1.16  #Strategies tried      : 1
% 1.83/1.16  
% 1.83/1.16  Timing (in seconds)
% 1.83/1.16  ----------------------
% 1.83/1.17  Preprocessing        : 0.29
% 1.83/1.17  Parsing              : 0.16
% 1.83/1.17  CNF conversion       : 0.02
% 1.83/1.17  Main loop            : 0.14
% 1.83/1.17  Inferencing          : 0.05
% 1.83/1.17  Reduction            : 0.05
% 1.83/1.17  Demodulation         : 0.03
% 1.83/1.17  BG Simplification    : 0.01
% 1.83/1.17  Subsumption          : 0.02
% 1.83/1.17  Abstraction          : 0.01
% 1.83/1.17  MUC search           : 0.00
% 1.83/1.17  Cooper               : 0.00
% 1.83/1.17  Total                : 0.46
% 1.83/1.17  Index Insertion      : 0.00
% 1.83/1.17  Index Deletion       : 0.00
% 1.83/1.17  Index Matching       : 0.00
% 1.83/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
