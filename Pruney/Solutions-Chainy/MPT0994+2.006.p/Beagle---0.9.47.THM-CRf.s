%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:49 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 124 expanded)
%              Number of leaves         :   29 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 322 expanded)
%              Number of equality atoms :   24 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( v1_funct_1(E)
          & v1_funct_2(E,A,B)
          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( r2_hidden(C,A)
            & r2_hidden(k1_funct_1(E,C),D) )
         => ( B = k1_xboole_0
            | k1_funct_1(k6_relset_1(A,B,D,E),C) = k1_funct_1(E,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
       => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_funct_1(k8_relat_1(A_11,B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k8_relat_1(A_11,B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_6,B_9] :
      ( k1_funct_1(A_6,B_9) = k1_xboole_0
      | r2_hidden(B_9,k1_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [A_38,C_39,B_40] :
      ( r2_hidden(A_38,k1_relat_1(C_39))
      | ~ r2_hidden(A_38,k1_relat_1(k8_relat_1(B_40,C_39)))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_169,plain,(
    ! [B_58,C_59,B_60] :
      ( r2_hidden(B_58,k1_relat_1(C_59))
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59)
      | k1_funct_1(k8_relat_1(B_60,C_59),B_58) = k1_xboole_0
      | ~ v1_funct_1(k8_relat_1(B_60,C_59))
      | ~ v1_relat_1(k8_relat_1(B_60,C_59)) ) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_173,plain,(
    ! [B_61,B_62,A_63] :
      ( r2_hidden(B_61,k1_relat_1(B_62))
      | k1_funct_1(k8_relat_1(A_63,B_62),B_61) = k1_xboole_0
      | ~ v1_funct_1(k8_relat_1(A_63,B_62))
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_16,c_169])).

tff(c_177,plain,(
    ! [B_64,B_65,A_66] :
      ( r2_hidden(B_64,k1_relat_1(B_65))
      | k1_funct_1(k8_relat_1(A_66,B_65),B_64) = k1_xboole_0
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_14,c_173])).

tff(c_52,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k6_relset_1(A_33,B_34,C_35,D_36) = k8_relat_1(C_35,D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_55,plain,(
    ! [C_35] : k6_relset_1('#skF_1','#skF_2',C_35,'#skF_5') = k8_relat_1(C_35,'#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_52])).

tff(c_28,plain,(
    k1_funct_1(k6_relset_1('#skF_1','#skF_2','#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_28])).

tff(c_32,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_111,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden(A_52,k1_relat_1(k8_relat_1(B_53,C_54)))
      | ~ r2_hidden(k1_funct_1(C_54,A_52),B_53)
      | ~ r2_hidden(A_52,k1_relat_1(C_54))
      | ~ v1_funct_1(C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    ! [B_17,C_18,A_16] :
      ( k1_funct_1(k8_relat_1(B_17,C_18),A_16) = k1_funct_1(C_18,A_16)
      | ~ r2_hidden(A_16,k1_relat_1(k8_relat_1(B_17,C_18)))
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_129,plain,(
    ! [B_55,C_56,A_57] :
      ( k1_funct_1(k8_relat_1(B_55,C_56),A_57) = k1_funct_1(C_56,A_57)
      | ~ r2_hidden(k1_funct_1(C_56,A_57),B_55)
      | ~ r2_hidden(A_57,k1_relat_1(C_56))
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(resolution,[status(thm)],[c_111,c_24])).

tff(c_140,plain,
    ( k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_129])).

tff(c_145,plain,
    ( k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_40,c_140])).

tff(c_146,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_145])).

tff(c_180,plain,(
    ! [A_66] :
      ( k1_funct_1(k8_relat_1(A_66,'#skF_5'),'#skF_3') = k1_xboole_0
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_177,c_146])).

tff(c_216,plain,(
    ! [A_66] : k1_funct_1(k8_relat_1(A_66,'#skF_5'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_40,c_180])).

tff(c_149,plain,
    ( k1_funct_1('#skF_5','#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_146])).

tff(c_152,plain,(
    k1_funct_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_40,c_149])).

tff(c_153,plain,(
    k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_56])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:03:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.11/1.25  
% 2.11/1.25  %Foreground sorts:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Background operators:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Foreground operators:
% 2.11/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.11/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.11/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.25  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.11/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.11/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.25  
% 2.11/1.26  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.11/1.26  tff(f_97, negated_conjecture, ~(![A, B, C, D, E]: (((v1_funct_1(E) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((r2_hidden(C, A) & r2_hidden(k1_funct_1(E, C), D)) => ((B = k1_xboole_0) | (k1_funct_1(k6_relset_1(A, B, D, E), C) = k1_funct_1(E, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_funct_2)).
% 2.11/1.26  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.11/1.26  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_funct_1)).
% 2.11/1.26  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.11/1.26  tff(f_70, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 2.11/1.26  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.11/1.26  tff(f_78, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 2.11/1.26  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.11/1.26  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_44, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.11/1.26  tff(c_47, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.11/1.26  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_47])).
% 2.11/1.26  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_14, plain, (![A_11, B_12]: (v1_funct_1(k8_relat_1(A_11, B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.26  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k8_relat_1(A_11, B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.26  tff(c_12, plain, (![A_6, B_9]: (k1_funct_1(A_6, B_9)=k1_xboole_0 | r2_hidden(B_9, k1_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.26  tff(c_66, plain, (![A_38, C_39, B_40]: (r2_hidden(A_38, k1_relat_1(C_39)) | ~r2_hidden(A_38, k1_relat_1(k8_relat_1(B_40, C_39))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.26  tff(c_169, plain, (![B_58, C_59, B_60]: (r2_hidden(B_58, k1_relat_1(C_59)) | ~v1_funct_1(C_59) | ~v1_relat_1(C_59) | k1_funct_1(k8_relat_1(B_60, C_59), B_58)=k1_xboole_0 | ~v1_funct_1(k8_relat_1(B_60, C_59)) | ~v1_relat_1(k8_relat_1(B_60, C_59)))), inference(resolution, [status(thm)], [c_12, c_66])).
% 2.11/1.26  tff(c_173, plain, (![B_61, B_62, A_63]: (r2_hidden(B_61, k1_relat_1(B_62)) | k1_funct_1(k8_relat_1(A_63, B_62), B_61)=k1_xboole_0 | ~v1_funct_1(k8_relat_1(A_63, B_62)) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_16, c_169])).
% 2.11/1.26  tff(c_177, plain, (![B_64, B_65, A_66]: (r2_hidden(B_64, k1_relat_1(B_65)) | k1_funct_1(k8_relat_1(A_66, B_65), B_64)=k1_xboole_0 | ~v1_funct_1(B_65) | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_14, c_173])).
% 2.11/1.26  tff(c_52, plain, (![A_33, B_34, C_35, D_36]: (k6_relset_1(A_33, B_34, C_35, D_36)=k8_relat_1(C_35, D_36) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.11/1.26  tff(c_55, plain, (![C_35]: (k6_relset_1('#skF_1', '#skF_2', C_35, '#skF_5')=k8_relat_1(C_35, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_52])).
% 2.11/1.26  tff(c_28, plain, (k1_funct_1(k6_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_56, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_28])).
% 2.11/1.26  tff(c_32, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_111, plain, (![A_52, B_53, C_54]: (r2_hidden(A_52, k1_relat_1(k8_relat_1(B_53, C_54))) | ~r2_hidden(k1_funct_1(C_54, A_52), B_53) | ~r2_hidden(A_52, k1_relat_1(C_54)) | ~v1_funct_1(C_54) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.26  tff(c_24, plain, (![B_17, C_18, A_16]: (k1_funct_1(k8_relat_1(B_17, C_18), A_16)=k1_funct_1(C_18, A_16) | ~r2_hidden(A_16, k1_relat_1(k8_relat_1(B_17, C_18))) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.11/1.26  tff(c_129, plain, (![B_55, C_56, A_57]: (k1_funct_1(k8_relat_1(B_55, C_56), A_57)=k1_funct_1(C_56, A_57) | ~r2_hidden(k1_funct_1(C_56, A_57), B_55) | ~r2_hidden(A_57, k1_relat_1(C_56)) | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(resolution, [status(thm)], [c_111, c_24])).
% 2.11/1.26  tff(c_140, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_129])).
% 2.11/1.26  tff(c_145, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_40, c_140])).
% 2.11/1.26  tff(c_146, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_145])).
% 2.11/1.26  tff(c_180, plain, (![A_66]: (k1_funct_1(k8_relat_1(A_66, '#skF_5'), '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_177, c_146])).
% 2.11/1.26  tff(c_216, plain, (![A_66]: (k1_funct_1(k8_relat_1(A_66, '#skF_5'), '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_40, c_180])).
% 2.11/1.26  tff(c_149, plain, (k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_146])).
% 2.11/1.26  tff(c_152, plain, (k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_40, c_149])).
% 2.11/1.26  tff(c_153, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_152, c_56])).
% 2.11/1.26  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_153])).
% 2.11/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  Inference rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Ref     : 0
% 2.11/1.26  #Sup     : 36
% 2.11/1.26  #Fact    : 0
% 2.11/1.26  #Define  : 0
% 2.11/1.26  #Split   : 0
% 2.11/1.26  #Chain   : 0
% 2.11/1.26  #Close   : 0
% 2.11/1.26  
% 2.11/1.26  Ordering : KBO
% 2.11/1.26  
% 2.11/1.26  Simplification rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Subsume      : 7
% 2.11/1.26  #Demod        : 16
% 2.11/1.26  #Tautology    : 9
% 2.11/1.26  #SimpNegUnit  : 1
% 2.11/1.26  #BackRed      : 4
% 2.11/1.26  
% 2.11/1.26  #Partial instantiations: 0
% 2.11/1.26  #Strategies tried      : 1
% 2.11/1.26  
% 2.11/1.26  Timing (in seconds)
% 2.11/1.26  ----------------------
% 2.11/1.26  Preprocessing        : 0.28
% 2.11/1.27  Parsing              : 0.15
% 2.11/1.27  CNF conversion       : 0.02
% 2.11/1.27  Main loop            : 0.19
% 2.11/1.27  Inferencing          : 0.07
% 2.11/1.27  Reduction            : 0.06
% 2.11/1.27  Demodulation         : 0.04
% 2.11/1.27  BG Simplification    : 0.01
% 2.11/1.27  Subsumption          : 0.04
% 2.11/1.27  Abstraction          : 0.01
% 2.11/1.27  MUC search           : 0.00
% 2.11/1.27  Cooper               : 0.00
% 2.11/1.27  Total                : 0.50
% 2.11/1.27  Index Insertion      : 0.00
% 2.11/1.27  Index Deletion       : 0.00
% 2.11/1.27  Index Matching       : 0.00
% 2.11/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
