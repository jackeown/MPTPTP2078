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
% DateTime   : Thu Dec  3 10:13:47 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   56 (  69 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 117 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_39,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_117,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_126,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_117])).

tff(c_143,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k1_relset_1(A_56,B_57,C_58),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_157,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_143])).

tff(c_162,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_157])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_162,c_4])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,'#skF_3')
      | ~ r1_tarski(A_35,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_55])).

tff(c_75,plain,(
    ! [B_41,A_42] :
      ( k7_relat_1(B_41,A_42) = B_41
      | ~ r1_tarski(k1_relat_1(B_41),A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    ! [B_41] :
      ( k7_relat_1(B_41,'#skF_3') = B_41
      | ~ v1_relat_1(B_41)
      | ~ r1_tarski(k1_relat_1(B_41),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_61,c_75])).

tff(c_171,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_166,c_85])).

tff(c_182,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_171])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_196,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k2_partfun1(A_59,B_60,C_61,D_62) = k7_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_204,plain,(
    ! [D_62] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_62) = k7_relat_1('#skF_4',D_62)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_196])).

tff(c_209,plain,(
    ! [D_62] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_62) = k7_relat_1('#skF_4',D_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_204])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_212,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_20])).

tff(c_213,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_212])).

tff(c_277,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( r2_relset_1(A_71,B_72,C_73,C_73)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_295,plain,(
    ! [C_77] :
      ( r2_relset_1('#skF_1','#skF_2',C_77,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_277])).

tff(c_303,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_295])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:15:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.37  
% 2.22/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.37  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.41/1.37  
% 2.41/1.37  %Foreground sorts:
% 2.41/1.37  
% 2.41/1.37  
% 2.41/1.37  %Background operators:
% 2.41/1.37  
% 2.41/1.37  
% 2.41/1.37  %Foreground operators:
% 2.41/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.41/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.37  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.41/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.41/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.41/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.41/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.37  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.41/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.41/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.37  
% 2.41/1.38  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.41/1.38  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.41/1.38  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.41/1.38  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.41/1.38  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.41/1.38  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.41/1.38  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.41/1.38  tff(f_65, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.41/1.38  tff(f_59, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.41/1.38  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.38  tff(c_39, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.41/1.38  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_39])).
% 2.41/1.38  tff(c_117, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.41/1.38  tff(c_126, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_117])).
% 2.41/1.38  tff(c_143, plain, (![A_56, B_57, C_58]: (m1_subset_1(k1_relset_1(A_56, B_57, C_58), k1_zfmisc_1(A_56)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.41/1.38  tff(c_157, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_126, c_143])).
% 2.41/1.38  tff(c_162, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_157])).
% 2.41/1.38  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.41/1.38  tff(c_166, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_162, c_4])).
% 2.41/1.38  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.38  tff(c_55, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.38  tff(c_61, plain, (![A_35]: (r1_tarski(A_35, '#skF_3') | ~r1_tarski(A_35, '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_55])).
% 2.41/1.38  tff(c_75, plain, (![B_41, A_42]: (k7_relat_1(B_41, A_42)=B_41 | ~r1_tarski(k1_relat_1(B_41), A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.38  tff(c_85, plain, (![B_41]: (k7_relat_1(B_41, '#skF_3')=B_41 | ~v1_relat_1(B_41) | ~r1_tarski(k1_relat_1(B_41), '#skF_1'))), inference(resolution, [status(thm)], [c_61, c_75])).
% 2.41/1.38  tff(c_171, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_166, c_85])).
% 2.41/1.38  tff(c_182, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_171])).
% 2.41/1.38  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.38  tff(c_196, plain, (![A_59, B_60, C_61, D_62]: (k2_partfun1(A_59, B_60, C_61, D_62)=k7_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.41/1.38  tff(c_204, plain, (![D_62]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_62)=k7_relat_1('#skF_4', D_62) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_196])).
% 2.41/1.38  tff(c_209, plain, (![D_62]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_62)=k7_relat_1('#skF_4', D_62))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_204])).
% 2.41/1.38  tff(c_20, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.38  tff(c_212, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_20])).
% 2.41/1.38  tff(c_213, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_212])).
% 2.41/1.38  tff(c_277, plain, (![A_71, B_72, C_73, D_74]: (r2_relset_1(A_71, B_72, C_73, C_73) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.41/1.38  tff(c_295, plain, (![C_77]: (r2_relset_1('#skF_1', '#skF_2', C_77, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_24, c_277])).
% 2.41/1.38  tff(c_303, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_295])).
% 2.41/1.38  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_303])).
% 2.41/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.38  
% 2.41/1.38  Inference rules
% 2.41/1.38  ----------------------
% 2.41/1.38  #Ref     : 0
% 2.41/1.38  #Sup     : 64
% 2.41/1.38  #Fact    : 0
% 2.41/1.38  #Define  : 0
% 2.41/1.38  #Split   : 4
% 2.41/1.38  #Chain   : 0
% 2.41/1.38  #Close   : 0
% 2.41/1.38  
% 2.41/1.38  Ordering : KBO
% 2.41/1.38  
% 2.41/1.38  Simplification rules
% 2.41/1.38  ----------------------
% 2.41/1.38  #Subsume      : 4
% 2.41/1.38  #Demod        : 14
% 2.41/1.38  #Tautology    : 15
% 2.41/1.38  #SimpNegUnit  : 1
% 2.41/1.38  #BackRed      : 1
% 2.41/1.38  
% 2.41/1.38  #Partial instantiations: 0
% 2.41/1.38  #Strategies tried      : 1
% 2.41/1.38  
% 2.41/1.38  Timing (in seconds)
% 2.41/1.38  ----------------------
% 2.41/1.39  Preprocessing        : 0.32
% 2.41/1.39  Parsing              : 0.18
% 2.41/1.39  CNF conversion       : 0.02
% 2.41/1.39  Main loop            : 0.23
% 2.41/1.39  Inferencing          : 0.09
% 2.41/1.39  Reduction            : 0.06
% 2.41/1.39  Demodulation         : 0.05
% 2.41/1.39  BG Simplification    : 0.01
% 2.41/1.39  Subsumption          : 0.05
% 2.41/1.39  Abstraction          : 0.01
% 2.41/1.39  MUC search           : 0.00
% 2.41/1.39  Cooper               : 0.00
% 2.41/1.39  Total                : 0.59
% 2.41/1.39  Index Insertion      : 0.00
% 2.41/1.39  Index Deletion       : 0.00
% 2.41/1.39  Index Matching       : 0.00
% 2.41/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
