%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:06 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   64 (  77 expanded)
%              Number of leaves         :   36 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :   90 ( 148 expanded)
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

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_74,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_58,c_74])).

tff(c_84,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_62,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_148,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_157,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_148])).

tff(c_626,plain,(
    ! [B_172,A_173,C_174] :
      ( k1_xboole_0 = B_172
      | k1_relset_1(A_173,B_172,C_174) = A_173
      | ~ v1_funct_2(C_174,A_173,B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_637,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_626])).

tff(c_642,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_157,c_637])).

tff(c_643,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_642])).

tff(c_138,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_147,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_138])).

tff(c_177,plain,(
    ! [A_100,B_101,C_102] :
      ( m1_subset_1(k2_relset_1(A_100,B_101,C_102),k1_zfmisc_1(B_101))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_194,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_177])).

tff(c_200,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_194])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_208,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_200,c_8])).

tff(c_238,plain,(
    ! [A_107,D_108] :
      ( r2_hidden(k1_funct_1(A_107,D_108),k2_relat_1(A_107))
      | ~ r2_hidden(D_108,k1_relat_1(A_107))
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1531,plain,(
    ! [A_307,D_308,B_309] :
      ( r2_hidden(k1_funct_1(A_307,D_308),B_309)
      | ~ r1_tarski(k2_relat_1(A_307),B_309)
      | ~ r2_hidden(D_308,k1_relat_1(A_307))
      | ~ v1_funct_1(A_307)
      | ~ v1_relat_1(A_307) ) ),
    inference(resolution,[status(thm)],[c_238,c_2])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1536,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1531,c_52])).

tff(c_1547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62,c_56,c_643,c_208,c_1536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.78  
% 4.08/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.78  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 4.15/1.78  
% 4.15/1.78  %Foreground sorts:
% 4.15/1.78  
% 4.15/1.78  
% 4.15/1.78  %Background operators:
% 4.15/1.78  
% 4.15/1.78  
% 4.15/1.78  %Foreground operators:
% 4.15/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.15/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.15/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.15/1.78  tff('#skF_7', type, '#skF_7': $i).
% 4.15/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.15/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.15/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.15/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.15/1.78  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.15/1.78  tff('#skF_9', type, '#skF_9': $i).
% 4.15/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.15/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.15/1.78  tff('#skF_8', type, '#skF_8': $i).
% 4.15/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.15/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.15/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.15/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.15/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.15/1.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.15/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.78  
% 4.15/1.80  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.15/1.80  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.15/1.80  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.15/1.80  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.15/1.80  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.15/1.80  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.15/1.80  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.15/1.80  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.15/1.80  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.15/1.80  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.15/1.80  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.15/1.80  tff(c_58, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.15/1.80  tff(c_74, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.15/1.80  tff(c_80, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_74])).
% 4.15/1.80  tff(c_84, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_80])).
% 4.15/1.80  tff(c_62, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.15/1.80  tff(c_56, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.15/1.80  tff(c_54, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.15/1.80  tff(c_60, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.15/1.80  tff(c_148, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.15/1.80  tff(c_157, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_148])).
% 4.15/1.80  tff(c_626, plain, (![B_172, A_173, C_174]: (k1_xboole_0=B_172 | k1_relset_1(A_173, B_172, C_174)=A_173 | ~v1_funct_2(C_174, A_173, B_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.15/1.80  tff(c_637, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_626])).
% 4.15/1.80  tff(c_642, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_157, c_637])).
% 4.15/1.80  tff(c_643, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_54, c_642])).
% 4.15/1.80  tff(c_138, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.15/1.80  tff(c_147, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_138])).
% 4.15/1.80  tff(c_177, plain, (![A_100, B_101, C_102]: (m1_subset_1(k2_relset_1(A_100, B_101, C_102), k1_zfmisc_1(B_101)) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.15/1.80  tff(c_194, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_147, c_177])).
% 4.15/1.80  tff(c_200, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_194])).
% 4.15/1.80  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.15/1.80  tff(c_208, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_7')), inference(resolution, [status(thm)], [c_200, c_8])).
% 4.15/1.80  tff(c_238, plain, (![A_107, D_108]: (r2_hidden(k1_funct_1(A_107, D_108), k2_relat_1(A_107)) | ~r2_hidden(D_108, k1_relat_1(A_107)) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.80  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.80  tff(c_1531, plain, (![A_307, D_308, B_309]: (r2_hidden(k1_funct_1(A_307, D_308), B_309) | ~r1_tarski(k2_relat_1(A_307), B_309) | ~r2_hidden(D_308, k1_relat_1(A_307)) | ~v1_funct_1(A_307) | ~v1_relat_1(A_307))), inference(resolution, [status(thm)], [c_238, c_2])).
% 4.15/1.80  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.15/1.80  tff(c_1536, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_7') | ~r2_hidden('#skF_8', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1531, c_52])).
% 4.15/1.80  tff(c_1547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_62, c_56, c_643, c_208, c_1536])).
% 4.15/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.80  
% 4.15/1.80  Inference rules
% 4.15/1.80  ----------------------
% 4.15/1.80  #Ref     : 0
% 4.15/1.80  #Sup     : 314
% 4.15/1.80  #Fact    : 0
% 4.15/1.80  #Define  : 0
% 4.15/1.80  #Split   : 10
% 4.15/1.80  #Chain   : 0
% 4.15/1.80  #Close   : 0
% 4.15/1.80  
% 4.15/1.80  Ordering : KBO
% 4.15/1.80  
% 4.15/1.80  Simplification rules
% 4.15/1.80  ----------------------
% 4.15/1.80  #Subsume      : 42
% 4.15/1.80  #Demod        : 78
% 4.15/1.80  #Tautology    : 65
% 4.15/1.80  #SimpNegUnit  : 8
% 4.15/1.80  #BackRed      : 7
% 4.15/1.80  
% 4.15/1.80  #Partial instantiations: 0
% 4.15/1.80  #Strategies tried      : 1
% 4.15/1.80  
% 4.15/1.80  Timing (in seconds)
% 4.15/1.80  ----------------------
% 4.15/1.80  Preprocessing        : 0.37
% 4.15/1.80  Parsing              : 0.18
% 4.15/1.80  CNF conversion       : 0.03
% 4.15/1.80  Main loop            : 0.58
% 4.15/1.80  Inferencing          : 0.21
% 4.15/1.80  Reduction            : 0.17
% 4.15/1.80  Demodulation         : 0.11
% 4.15/1.80  BG Simplification    : 0.03
% 4.15/1.80  Subsumption          : 0.12
% 4.15/1.80  Abstraction          : 0.03
% 4.15/1.80  MUC search           : 0.00
% 4.15/1.80  Cooper               : 0.00
% 4.15/1.80  Total                : 0.98
% 4.15/1.80  Index Insertion      : 0.00
% 4.15/1.80  Index Deletion       : 0.00
% 4.15/1.80  Index Matching       : 0.00
% 4.15/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
