%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:02 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   61 (  74 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 142 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_56,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_72])).

tff(c_60,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_169,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_178,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_169])).

tff(c_757,plain,(
    ! [B_202,A_203,C_204] :
      ( k1_xboole_0 = B_202
      | k1_relset_1(A_203,B_202,C_204) = A_203
      | ~ v1_funct_2(C_204,A_203,B_202)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_772,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_757])).

tff(c_778,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_178,c_772])).

tff(c_779,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_778])).

tff(c_129,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_138,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_129])).

tff(c_203,plain,(
    ! [A_107,B_108,C_109] :
      ( m1_subset_1(k2_relset_1(A_107,B_108,C_109),k1_zfmisc_1(B_108))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_224,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_203])).

tff(c_230,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_234,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_230,c_8])).

tff(c_263,plain,(
    ! [A_115,D_116] :
      ( r2_hidden(k1_funct_1(A_115,D_116),k2_relat_1(A_115))
      | ~ r2_hidden(D_116,k1_relat_1(A_115))
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1480,plain,(
    ! [A_298,D_299,B_300] :
      ( r2_hidden(k1_funct_1(A_298,D_299),B_300)
      | ~ r1_tarski(k2_relat_1(A_298),B_300)
      | ~ r2_hidden(D_299,k1_relat_1(A_298))
      | ~ v1_funct_1(A_298)
      | ~ v1_relat_1(A_298) ) ),
    inference(resolution,[status(thm)],[c_263,c_2])).

tff(c_50,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1485,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1480,c_50])).

tff(c_1496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_60,c_54,c_779,c_234,c_1485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.62  
% 3.61/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.62  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.61/1.62  
% 3.61/1.62  %Foreground sorts:
% 3.61/1.62  
% 3.61/1.62  
% 3.61/1.62  %Background operators:
% 3.61/1.62  
% 3.61/1.62  
% 3.61/1.62  %Foreground operators:
% 3.61/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.61/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.61/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.61/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.61/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.61/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.61/1.62  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.61/1.62  tff('#skF_9', type, '#skF_9': $i).
% 3.61/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.61/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.61/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.61/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.61/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.61/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.61/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.62  
% 3.97/1.63  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.97/1.63  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.97/1.63  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.97/1.63  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.97/1.63  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.97/1.63  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.97/1.63  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.97/1.63  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.97/1.63  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.97/1.63  tff(c_56, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.97/1.63  tff(c_72, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.97/1.63  tff(c_81, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_72])).
% 3.97/1.63  tff(c_60, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.97/1.63  tff(c_54, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.97/1.63  tff(c_52, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.97/1.63  tff(c_58, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.97/1.63  tff(c_169, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.63  tff(c_178, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_169])).
% 3.97/1.63  tff(c_757, plain, (![B_202, A_203, C_204]: (k1_xboole_0=B_202 | k1_relset_1(A_203, B_202, C_204)=A_203 | ~v1_funct_2(C_204, A_203, B_202) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.97/1.63  tff(c_772, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_757])).
% 3.97/1.63  tff(c_778, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_178, c_772])).
% 3.97/1.63  tff(c_779, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52, c_778])).
% 3.97/1.63  tff(c_129, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.97/1.63  tff(c_138, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_129])).
% 3.97/1.63  tff(c_203, plain, (![A_107, B_108, C_109]: (m1_subset_1(k2_relset_1(A_107, B_108, C_109), k1_zfmisc_1(B_108)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.97/1.63  tff(c_224, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_138, c_203])).
% 3.97/1.63  tff(c_230, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224])).
% 3.97/1.63  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.97/1.63  tff(c_234, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_7')), inference(resolution, [status(thm)], [c_230, c_8])).
% 3.97/1.63  tff(c_263, plain, (![A_115, D_116]: (r2_hidden(k1_funct_1(A_115, D_116), k2_relat_1(A_115)) | ~r2_hidden(D_116, k1_relat_1(A_115)) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.97/1.63  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.97/1.63  tff(c_1480, plain, (![A_298, D_299, B_300]: (r2_hidden(k1_funct_1(A_298, D_299), B_300) | ~r1_tarski(k2_relat_1(A_298), B_300) | ~r2_hidden(D_299, k1_relat_1(A_298)) | ~v1_funct_1(A_298) | ~v1_relat_1(A_298))), inference(resolution, [status(thm)], [c_263, c_2])).
% 3.97/1.63  tff(c_50, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.97/1.63  tff(c_1485, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_7') | ~r2_hidden('#skF_8', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1480, c_50])).
% 3.97/1.63  tff(c_1496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_60, c_54, c_779, c_234, c_1485])).
% 3.97/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.63  
% 3.97/1.63  Inference rules
% 3.97/1.63  ----------------------
% 3.97/1.63  #Ref     : 0
% 3.97/1.63  #Sup     : 299
% 3.97/1.63  #Fact    : 0
% 3.97/1.63  #Define  : 0
% 3.97/1.63  #Split   : 9
% 3.97/1.63  #Chain   : 0
% 3.97/1.63  #Close   : 0
% 3.97/1.63  
% 3.97/1.63  Ordering : KBO
% 3.97/1.63  
% 3.97/1.63  Simplification rules
% 3.97/1.63  ----------------------
% 3.97/1.63  #Subsume      : 24
% 3.97/1.63  #Demod        : 79
% 3.97/1.63  #Tautology    : 70
% 3.97/1.63  #SimpNegUnit  : 8
% 3.97/1.63  #BackRed      : 7
% 3.97/1.63  
% 3.97/1.63  #Partial instantiations: 0
% 3.97/1.63  #Strategies tried      : 1
% 3.97/1.63  
% 3.97/1.63  Timing (in seconds)
% 3.97/1.63  ----------------------
% 3.97/1.64  Preprocessing        : 0.34
% 3.97/1.64  Parsing              : 0.17
% 3.97/1.64  CNF conversion       : 0.03
% 3.97/1.64  Main loop            : 0.56
% 3.97/1.64  Inferencing          : 0.21
% 3.97/1.64  Reduction            : 0.17
% 3.97/1.64  Demodulation         : 0.12
% 3.97/1.64  BG Simplification    : 0.03
% 3.97/1.64  Subsumption          : 0.11
% 3.97/1.64  Abstraction          : 0.03
% 3.97/1.64  MUC search           : 0.00
% 3.97/1.64  Cooper               : 0.00
% 3.97/1.64  Total                : 0.93
% 3.97/1.64  Index Insertion      : 0.00
% 3.97/1.64  Index Deletion       : 0.00
% 3.97/1.64  Index Matching       : 0.00
% 3.97/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
