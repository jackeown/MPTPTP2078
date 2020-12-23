%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:57 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 226 expanded)
%              Number of equality atoms :   34 (  83 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_85,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_89,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_135,plain,(
    ! [B_56,A_57,C_58] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_57,B_56,C_58) = A_57
      | ~ v1_funct_2(C_58,A_57,B_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_138,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_135])).

tff(c_141,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_89,c_138])).

tff(c_142,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_141])).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_50])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_53])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,k10_relat_1(B_10,k9_relat_1(B_10,A_9)))
      | ~ r1_tarski(A_9,k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k8_relset_1(A_47,B_48,C_49,D_50) = k10_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_116,plain,(
    ! [D_50] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_50) = k10_relat_1('#skF_4',D_50) ),
    inference(resolution,[status(thm)],[c_40,c_113])).

tff(c_98,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k7_relset_1(A_40,B_41,C_42,D_43) = k9_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_101,plain,(
    ! [D_43] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_43) = k9_relat_1('#skF_4',D_43) ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_102,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_34])).

tff(c_118,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_102])).

tff(c_130,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_133,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_130])).

tff(c_143,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_133])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_143])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_8])).

tff(c_163,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_163])).

tff(c_177,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_169])).

tff(c_149,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_155,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_149])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_177,c_155,c_155,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:30:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.12/1.28  
% 2.12/1.28  %Foreground sorts:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Background operators:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Foreground operators:
% 2.12/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.28  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.12/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.12/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.12/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.12/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.12/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.28  
% 2.12/1.30  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_2)).
% 2.12/1.30  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.12/1.30  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.12/1.30  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.12/1.30  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.12/1.30  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 2.12/1.30  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.12/1.30  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.12/1.30  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.12/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.12/1.30  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.12/1.30  tff(c_36, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.12/1.30  tff(c_49, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 2.12/1.30  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.12/1.30  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.12/1.30  tff(c_85, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.30  tff(c_89, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_85])).
% 2.12/1.30  tff(c_135, plain, (![B_56, A_57, C_58]: (k1_xboole_0=B_56 | k1_relset_1(A_57, B_56, C_58)=A_57 | ~v1_funct_2(C_58, A_57, B_56) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.30  tff(c_138, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_135])).
% 2.12/1.30  tff(c_141, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_89, c_138])).
% 2.12/1.30  tff(c_142, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_49, c_141])).
% 2.12/1.30  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.12/1.30  tff(c_50, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.12/1.30  tff(c_53, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_50])).
% 2.12/1.30  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_53])).
% 2.12/1.30  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, k10_relat_1(B_10, k9_relat_1(B_10, A_9))) | ~r1_tarski(A_9, k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.30  tff(c_113, plain, (![A_47, B_48, C_49, D_50]: (k8_relset_1(A_47, B_48, C_49, D_50)=k10_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.12/1.30  tff(c_116, plain, (![D_50]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_50)=k10_relat_1('#skF_4', D_50))), inference(resolution, [status(thm)], [c_40, c_113])).
% 2.12/1.30  tff(c_98, plain, (![A_40, B_41, C_42, D_43]: (k7_relset_1(A_40, B_41, C_42, D_43)=k9_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.30  tff(c_101, plain, (![D_43]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_43)=k9_relat_1('#skF_4', D_43))), inference(resolution, [status(thm)], [c_40, c_98])).
% 2.12/1.30  tff(c_34, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.12/1.30  tff(c_102, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_34])).
% 2.12/1.30  tff(c_118, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_102])).
% 2.12/1.30  tff(c_130, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_118])).
% 2.12/1.30  tff(c_133, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_130])).
% 2.12/1.30  tff(c_143, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_133])).
% 2.12/1.30  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_143])).
% 2.12/1.30  tff(c_148, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_36])).
% 2.12/1.30  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.30  tff(c_150, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_8])).
% 2.12/1.30  tff(c_163, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.30  tff(c_169, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_163])).
% 2.12/1.30  tff(c_177, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_169])).
% 2.12/1.30  tff(c_149, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 2.12/1.30  tff(c_155, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_149])).
% 2.12/1.30  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_177, c_155, c_155, c_34])).
% 2.12/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  Inference rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Ref     : 0
% 2.12/1.30  #Sup     : 27
% 2.12/1.30  #Fact    : 0
% 2.12/1.30  #Define  : 0
% 2.12/1.30  #Split   : 2
% 2.12/1.30  #Chain   : 0
% 2.12/1.30  #Close   : 0
% 2.12/1.30  
% 2.12/1.30  Ordering : KBO
% 2.12/1.30  
% 2.12/1.30  Simplification rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Subsume      : 0
% 2.12/1.30  #Demod        : 23
% 2.12/1.30  #Tautology    : 18
% 2.12/1.30  #SimpNegUnit  : 1
% 2.12/1.30  #BackRed      : 7
% 2.12/1.30  
% 2.12/1.30  #Partial instantiations: 0
% 2.12/1.30  #Strategies tried      : 1
% 2.12/1.30  
% 2.12/1.30  Timing (in seconds)
% 2.12/1.30  ----------------------
% 2.12/1.30  Preprocessing        : 0.33
% 2.12/1.30  Parsing              : 0.18
% 2.12/1.30  CNF conversion       : 0.02
% 2.12/1.30  Main loop            : 0.17
% 2.12/1.30  Inferencing          : 0.05
% 2.12/1.30  Reduction            : 0.06
% 2.12/1.30  Demodulation         : 0.04
% 2.12/1.30  BG Simplification    : 0.01
% 2.12/1.30  Subsumption          : 0.03
% 2.12/1.30  Abstraction          : 0.01
% 2.12/1.30  MUC search           : 0.00
% 2.12/1.30  Cooper               : 0.00
% 2.12/1.30  Total                : 0.53
% 2.12/1.31  Index Insertion      : 0.00
% 2.12/1.31  Index Deletion       : 0.00
% 2.12/1.31  Index Matching       : 0.00
% 2.12/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
