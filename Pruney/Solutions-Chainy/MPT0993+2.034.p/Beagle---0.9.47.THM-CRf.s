%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:47 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   61 (  79 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 137 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_43,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_81,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_148,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k1_relset_1(A_56,B_57,C_58),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_162,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_148])).

tff(c_167,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_162])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_167,c_4])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_71,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,'#skF_3')
      | ~ r1_tarski(A_49,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_71])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( v4_relat_1(B_7,A_6)
      | ~ r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [B_7] :
      ( v4_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7)
      | ~ r1_tarski(k1_relat_1(B_7),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_174,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_171,c_99])).

tff(c_184,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_174])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_192,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_12])).

tff(c_195,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_192])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_217,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k2_partfun1(A_60,B_61,C_62,D_63) = k7_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_225,plain,(
    ! [D_63] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_63) = k7_relat_1('#skF_4',D_63)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_217])).

tff(c_230,plain,(
    ! [D_63] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_63) = k7_relat_1('#skF_4',D_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_225])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_231,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_24])).

tff(c_232,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_231])).

tff(c_276,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( r2_relset_1(A_69,B_70,C_71,C_71)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_290,plain,(
    ! [C_77] :
      ( r2_relset_1('#skF_1','#skF_2',C_77,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_276])).

tff(c_298,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_290])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  %$ r2_relset_1 > v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.30  
% 2.10/1.30  %Foreground sorts:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Background operators:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Foreground operators:
% 2.10/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.10/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.10/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.10/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.10/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.30  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.10/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.10/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.30  
% 2.37/1.31  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.37/1.31  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.37/1.31  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.37/1.31  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.37/1.31  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.37/1.31  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.37/1.31  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.37/1.31  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.37/1.31  tff(f_71, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.37/1.31  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.37/1.31  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.37/1.31  tff(c_43, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.37/1.31  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_43])).
% 2.37/1.31  tff(c_81, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.37/1.31  tff(c_90, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_81])).
% 2.37/1.31  tff(c_148, plain, (![A_56, B_57, C_58]: (m1_subset_1(k1_relset_1(A_56, B_57, C_58), k1_zfmisc_1(A_56)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.31  tff(c_162, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_148])).
% 2.37/1.31  tff(c_167, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_162])).
% 2.37/1.31  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.31  tff(c_171, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_167, c_4])).
% 2.37/1.31  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.37/1.31  tff(c_71, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.31  tff(c_91, plain, (![A_49]: (r1_tarski(A_49, '#skF_3') | ~r1_tarski(A_49, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_71])).
% 2.37/1.31  tff(c_8, plain, (![B_7, A_6]: (v4_relat_1(B_7, A_6) | ~r1_tarski(k1_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.37/1.31  tff(c_99, plain, (![B_7]: (v4_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7) | ~r1_tarski(k1_relat_1(B_7), '#skF_1'))), inference(resolution, [status(thm)], [c_91, c_8])).
% 2.37/1.31  tff(c_174, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_171, c_99])).
% 2.37/1.31  tff(c_184, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_174])).
% 2.37/1.31  tff(c_12, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.37/1.31  tff(c_192, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_184, c_12])).
% 2.37/1.31  tff(c_195, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_192])).
% 2.37/1.31  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.37/1.31  tff(c_217, plain, (![A_60, B_61, C_62, D_63]: (k2_partfun1(A_60, B_61, C_62, D_63)=k7_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.31  tff(c_225, plain, (![D_63]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_63)=k7_relat_1('#skF_4', D_63) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_217])).
% 2.37/1.31  tff(c_230, plain, (![D_63]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_63)=k7_relat_1('#skF_4', D_63))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_225])).
% 2.37/1.31  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.37/1.31  tff(c_231, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_24])).
% 2.37/1.31  tff(c_232, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_231])).
% 2.37/1.31  tff(c_276, plain, (![A_69, B_70, C_71, D_72]: (r2_relset_1(A_69, B_70, C_71, C_71) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.37/1.31  tff(c_290, plain, (![C_77]: (r2_relset_1('#skF_1', '#skF_2', C_77, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_28, c_276])).
% 2.37/1.31  tff(c_298, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_290])).
% 2.37/1.31  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_298])).
% 2.37/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.31  
% 2.37/1.31  Inference rules
% 2.37/1.31  ----------------------
% 2.37/1.31  #Ref     : 0
% 2.37/1.31  #Sup     : 61
% 2.37/1.31  #Fact    : 0
% 2.37/1.31  #Define  : 0
% 2.37/1.31  #Split   : 4
% 2.37/1.31  #Chain   : 0
% 2.37/1.31  #Close   : 0
% 2.37/1.31  
% 2.37/1.31  Ordering : KBO
% 2.37/1.31  
% 2.37/1.31  Simplification rules
% 2.37/1.31  ----------------------
% 2.37/1.31  #Subsume      : 2
% 2.37/1.31  #Demod        : 13
% 2.37/1.31  #Tautology    : 14
% 2.37/1.31  #SimpNegUnit  : 1
% 2.37/1.31  #BackRed      : 1
% 2.37/1.31  
% 2.37/1.31  #Partial instantiations: 0
% 2.37/1.31  #Strategies tried      : 1
% 2.37/1.31  
% 2.37/1.31  Timing (in seconds)
% 2.37/1.31  ----------------------
% 2.37/1.31  Preprocessing        : 0.31
% 2.37/1.31  Parsing              : 0.17
% 2.37/1.31  CNF conversion       : 0.02
% 2.37/1.31  Main loop            : 0.24
% 2.37/1.31  Inferencing          : 0.09
% 2.37/1.31  Reduction            : 0.07
% 2.37/1.31  Demodulation         : 0.05
% 2.37/1.31  BG Simplification    : 0.01
% 2.37/1.31  Subsumption          : 0.05
% 2.37/1.31  Abstraction          : 0.01
% 2.37/1.32  MUC search           : 0.00
% 2.37/1.32  Cooper               : 0.00
% 2.37/1.32  Total                : 0.58
% 2.37/1.32  Index Insertion      : 0.00
% 2.37/1.32  Index Deletion       : 0.00
% 2.37/1.32  Index Matching       : 0.00
% 2.37/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
