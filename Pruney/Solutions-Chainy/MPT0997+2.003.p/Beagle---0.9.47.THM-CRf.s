%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:52 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   49 (  64 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  99 expanded)
%              Number of equality atoms :   20 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_29,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_35,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_32])).

tff(c_37,plain,(
    ! [C_26,A_27,B_28] :
      ( v4_relat_1(C_26,A_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_41,c_8])).

tff(c_47,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_44])).

tff(c_57,plain,(
    ! [B_32,A_33] :
      ( k2_relat_1(k7_relat_1(B_32,A_33)) = k9_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_57])).

tff(c_70,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_66])).

tff(c_85,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( k7_relset_1(A_37,B_38,C_39,D_40) = k9_relat_1(C_39,D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    ! [D_40] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_40) = k9_relat_1('#skF_3',D_40) ),
    inference(resolution,[status(thm)],[c_22,c_85])).

tff(c_75,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_relset_1(A_34,B_35,C_36) = k2_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_18,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_80,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_18])).

tff(c_89,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_80])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.23  
% 1.85/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.23  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.85/1.23  
% 1.85/1.23  %Foreground sorts:
% 1.85/1.23  
% 1.85/1.23  
% 1.85/1.23  %Background operators:
% 1.85/1.23  
% 1.85/1.23  
% 1.85/1.23  %Foreground operators:
% 1.85/1.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.85/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.85/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.85/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.23  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.85/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.85/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.85/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.85/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.85/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.85/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.23  
% 1.85/1.24  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.85/1.24  tff(f_71, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_funct_2)).
% 1.85/1.24  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.85/1.24  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.85/1.24  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.85/1.24  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.85/1.24  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.85/1.24  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.85/1.24  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.24  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.85/1.24  tff(c_29, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.24  tff(c_32, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_29])).
% 1.85/1.24  tff(c_35, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_32])).
% 1.85/1.24  tff(c_37, plain, (![C_26, A_27, B_28]: (v4_relat_1(C_26, A_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.85/1.24  tff(c_41, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_37])).
% 1.85/1.24  tff(c_8, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.24  tff(c_44, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_41, c_8])).
% 1.85/1.24  tff(c_47, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_44])).
% 1.85/1.24  tff(c_57, plain, (![B_32, A_33]: (k2_relat_1(k7_relat_1(B_32, A_33))=k9_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.24  tff(c_66, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_47, c_57])).
% 1.85/1.24  tff(c_70, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_66])).
% 1.85/1.24  tff(c_85, plain, (![A_37, B_38, C_39, D_40]: (k7_relset_1(A_37, B_38, C_39, D_40)=k9_relat_1(C_39, D_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.24  tff(c_88, plain, (![D_40]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_40)=k9_relat_1('#skF_3', D_40))), inference(resolution, [status(thm)], [c_22, c_85])).
% 1.85/1.24  tff(c_75, plain, (![A_34, B_35, C_36]: (k2_relset_1(A_34, B_35, C_36)=k2_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.24  tff(c_79, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_75])).
% 1.85/1.24  tff(c_18, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.85/1.24  tff(c_80, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_18])).
% 1.85/1.24  tff(c_89, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_80])).
% 1.85/1.24  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_89])).
% 1.85/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.24  
% 1.85/1.24  Inference rules
% 1.85/1.24  ----------------------
% 1.85/1.24  #Ref     : 0
% 1.85/1.24  #Sup     : 15
% 1.85/1.24  #Fact    : 0
% 1.85/1.24  #Define  : 0
% 1.85/1.24  #Split   : 1
% 1.85/1.24  #Chain   : 0
% 1.85/1.24  #Close   : 0
% 1.85/1.24  
% 1.85/1.24  Ordering : KBO
% 1.85/1.24  
% 1.85/1.24  Simplification rules
% 1.85/1.24  ----------------------
% 1.85/1.24  #Subsume      : 0
% 1.85/1.24  #Demod        : 6
% 1.85/1.24  #Tautology    : 8
% 1.85/1.24  #SimpNegUnit  : 0
% 1.85/1.24  #BackRed      : 2
% 1.85/1.24  
% 1.85/1.24  #Partial instantiations: 0
% 1.85/1.24  #Strategies tried      : 1
% 1.85/1.24  
% 1.85/1.24  Timing (in seconds)
% 1.85/1.24  ----------------------
% 1.85/1.25  Preprocessing        : 0.30
% 1.85/1.25  Parsing              : 0.17
% 1.85/1.25  CNF conversion       : 0.02
% 1.85/1.25  Main loop            : 0.11
% 1.85/1.25  Inferencing          : 0.04
% 1.85/1.25  Reduction            : 0.03
% 1.85/1.25  Demodulation         : 0.03
% 1.85/1.25  BG Simplification    : 0.01
% 1.85/1.25  Subsumption          : 0.01
% 1.85/1.25  Abstraction          : 0.00
% 1.85/1.25  MUC search           : 0.00
% 1.85/1.25  Cooper               : 0.00
% 1.85/1.25  Total                : 0.44
% 1.85/1.25  Index Insertion      : 0.00
% 1.85/1.25  Index Deletion       : 0.00
% 1.85/1.25  Index Matching       : 0.00
% 1.85/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
