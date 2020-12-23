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
% DateTime   : Thu Dec  3 10:07:43 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 174 expanded)
%              Number of leaves         :   29 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :   95 ( 302 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_13,B_14)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k8_relat_1(A_15,B_16),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_34])).

tff(c_86,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_182,plain,(
    ! [A_67,A_68,B_69] :
      ( v4_relat_1(A_67,A_68)
      | ~ r1_tarski(A_67,k2_zfmisc_1(A_68,B_69)) ) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_202,plain,(
    ! [A_48] :
      ( v4_relat_1(A_48,'#skF_3')
      | ~ r1_tarski(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_93,c_182])).

tff(c_115,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_51,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_127,plain,(
    ! [A_57] :
      ( v1_relat_1(A_57)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_115,c_51])).

tff(c_134,plain,(
    ! [A_58] :
      ( v1_relat_1(A_58)
      | ~ r1_tarski(A_58,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_127])).

tff(c_142,plain,(
    ! [A_15] :
      ( v1_relat_1(k8_relat_1(A_15,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_134])).

tff(c_146,plain,(
    ! [A_15] : v1_relat_1(k8_relat_1(A_15,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_142])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_293,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ r1_tarski(k2_relat_1(C_96),B_98)
      | ~ r1_tarski(k1_relat_1(C_96),A_97)
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_247,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k6_relset_1(A_85,B_86,C_87,D_88) = k8_relat_1(C_87,D_88)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_254,plain,(
    ! [C_87] : k6_relset_1('#skF_3','#skF_1',C_87,'#skF_4') = k8_relat_1(C_87,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_247])).

tff(c_28,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_256,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_28])).

tff(c_296,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_293,c_256])).

tff(c_313,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_296])).

tff(c_361,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_364,plain,
    ( ~ v4_relat_1(k8_relat_1('#skF_2','#skF_4'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_361])).

tff(c_367,plain,(
    ~ v4_relat_1(k8_relat_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_364])).

tff(c_371,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_202,c_367])).

tff(c_374,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_371])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_374])).

tff(c_379,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_383,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_379])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:37:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.18/1.30  
% 2.18/1.30  %Foreground sorts:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Background operators:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Foreground operators:
% 2.18/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.30  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.18/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.18/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.30  
% 2.18/1.32  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.18/1.32  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.18/1.32  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.18/1.32  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.18/1.32  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.18/1.32  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.18/1.32  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.18/1.32  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.18/1.32  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.18/1.32  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.18/1.32  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.18/1.32  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.32  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.18/1.32  tff(c_44, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.18/1.32  tff(c_50, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_44])).
% 2.18/1.32  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 2.18/1.32  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k2_relat_1(k8_relat_1(A_13, B_14)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.32  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k8_relat_1(A_15, B_16), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.32  tff(c_34, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.32  tff(c_42, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_34])).
% 2.18/1.32  tff(c_86, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.32  tff(c_93, plain, (![A_48]: (r1_tarski(A_48, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_86])).
% 2.18/1.32  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.32  tff(c_150, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.32  tff(c_182, plain, (![A_67, A_68, B_69]: (v4_relat_1(A_67, A_68) | ~r1_tarski(A_67, k2_zfmisc_1(A_68, B_69)))), inference(resolution, [status(thm)], [c_6, c_150])).
% 2.18/1.32  tff(c_202, plain, (![A_48]: (v4_relat_1(A_48, '#skF_3') | ~r1_tarski(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_93, c_182])).
% 2.18/1.32  tff(c_115, plain, (![A_57]: (r1_tarski(A_57, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_86])).
% 2.18/1.32  tff(c_51, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_44])).
% 2.18/1.32  tff(c_127, plain, (![A_57]: (v1_relat_1(A_57) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_115, c_51])).
% 2.18/1.32  tff(c_134, plain, (![A_58]: (v1_relat_1(A_58) | ~r1_tarski(A_58, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_127])).
% 2.18/1.32  tff(c_142, plain, (![A_15]: (v1_relat_1(k8_relat_1(A_15, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_134])).
% 2.18/1.32  tff(c_146, plain, (![A_15]: (v1_relat_1(k8_relat_1(A_15, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_142])).
% 2.18/1.32  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.18/1.32  tff(c_293, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~r1_tarski(k2_relat_1(C_96), B_98) | ~r1_tarski(k1_relat_1(C_96), A_97) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.18/1.32  tff(c_247, plain, (![A_85, B_86, C_87, D_88]: (k6_relset_1(A_85, B_86, C_87, D_88)=k8_relat_1(C_87, D_88) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.18/1.32  tff(c_254, plain, (![C_87]: (k6_relset_1('#skF_3', '#skF_1', C_87, '#skF_4')=k8_relat_1(C_87, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_247])).
% 2.18/1.32  tff(c_28, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.18/1.32  tff(c_256, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_28])).
% 2.18/1.32  tff(c_296, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_293, c_256])).
% 2.18/1.32  tff(c_313, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_296])).
% 2.18/1.32  tff(c_361, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_313])).
% 2.18/1.32  tff(c_364, plain, (~v4_relat_1(k8_relat_1('#skF_2', '#skF_4'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_361])).
% 2.18/1.32  tff(c_367, plain, (~v4_relat_1(k8_relat_1('#skF_2', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_364])).
% 2.18/1.32  tff(c_371, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_202, c_367])).
% 2.18/1.32  tff(c_374, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_371])).
% 2.18/1.32  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_374])).
% 2.18/1.32  tff(c_379, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_313])).
% 2.18/1.32  tff(c_383, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_379])).
% 2.18/1.32  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_383])).
% 2.18/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  Inference rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Ref     : 0
% 2.18/1.32  #Sup     : 71
% 2.18/1.32  #Fact    : 0
% 2.18/1.32  #Define  : 0
% 2.18/1.32  #Split   : 2
% 2.18/1.32  #Chain   : 0
% 2.18/1.32  #Close   : 0
% 2.18/1.32  
% 2.18/1.32  Ordering : KBO
% 2.18/1.32  
% 2.18/1.32  Simplification rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Subsume      : 7
% 2.18/1.32  #Demod        : 19
% 2.18/1.32  #Tautology    : 9
% 2.18/1.32  #SimpNegUnit  : 0
% 2.18/1.32  #BackRed      : 2
% 2.18/1.32  
% 2.18/1.32  #Partial instantiations: 0
% 2.18/1.32  #Strategies tried      : 1
% 2.18/1.32  
% 2.18/1.32  Timing (in seconds)
% 2.18/1.32  ----------------------
% 2.18/1.32  Preprocessing        : 0.31
% 2.18/1.32  Parsing              : 0.17
% 2.18/1.32  CNF conversion       : 0.02
% 2.18/1.32  Main loop            : 0.25
% 2.18/1.32  Inferencing          : 0.10
% 2.18/1.32  Reduction            : 0.07
% 2.18/1.32  Demodulation         : 0.05
% 2.18/1.32  BG Simplification    : 0.01
% 2.18/1.32  Subsumption          : 0.05
% 2.18/1.32  Abstraction          : 0.01
% 2.18/1.32  MUC search           : 0.00
% 2.18/1.32  Cooper               : 0.00
% 2.18/1.32  Total                : 0.59
% 2.18/1.32  Index Insertion      : 0.00
% 2.18/1.32  Index Deletion       : 0.00
% 2.18/1.32  Index Matching       : 0.00
% 2.18/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
