%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:20 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   70 (  97 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 164 expanded)
%              Number of equality atoms :   25 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_178,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_182,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_178])).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_65,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_183,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_65])).

tff(c_10,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_64,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_61])).

tff(c_93,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_93])).

tff(c_34,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_209,plain,(
    ! [C_69,A_70,B_71,D_72] :
      ( r1_tarski(C_69,k1_relset_1(A_70,B_71,D_72))
      | ~ r1_tarski(k6_relat_1(C_69),D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_221,plain,(
    ! [A_75,B_76] :
      ( r1_tarski('#skF_2',k1_relset_1(A_75,B_76,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(resolution,[status(thm)],[c_34,c_209])).

tff(c_224,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_221])).

tff(c_226,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_224])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_139,plain,(
    ! [B_52,A_53] :
      ( k5_relat_1(B_52,k6_relat_1(A_53)) = B_52
      | ~ r1_tarski(k2_relat_1(B_52),A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_142,plain,(
    ! [A_8,A_53] :
      ( k5_relat_1(k6_relat_1(A_8),k6_relat_1(A_53)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_53)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_139])).

tff(c_145,plain,(
    ! [A_54,A_55] :
      ( k5_relat_1(k6_relat_1(A_54),k6_relat_1(A_55)) = k6_relat_1(A_54)
      | ~ r1_tarski(A_54,A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_142])).

tff(c_98,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = B_47
      | ~ r1_tarski(k1_relat_1(B_47),A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_104,plain,(
    ! [A_46,A_8] :
      ( k5_relat_1(k6_relat_1(A_46),k6_relat_1(A_8)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_46)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_98])).

tff(c_107,plain,(
    ! [A_46,A_8] :
      ( k5_relat_1(k6_relat_1(A_46),k6_relat_1(A_8)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_104])).

tff(c_171,plain,(
    ! [A_57,A_56] :
      ( k6_relat_1(A_57) = k6_relat_1(A_56)
      | ~ r1_tarski(A_56,A_57)
      | ~ r1_tarski(A_57,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_107])).

tff(c_176,plain,(
    ! [B_5,A_4] :
      ( k6_relat_1(k1_relat_1(B_5)) = k6_relat_1(A_4)
      | ~ r1_tarski(A_4,k1_relat_1(B_5))
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_171])).

tff(c_229,plain,
    ( k6_relat_1(k1_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_226,c_176])).

tff(c_234,plain,(
    k6_relat_1(k1_relat_1('#skF_3')) = k6_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_97,c_229])).

tff(c_267,plain,(
    k1_relat_1(k6_relat_1('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_10])).

tff(c_280,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_267])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_280])).

tff(c_283,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_508,plain,(
    ! [C_120,A_121,B_122,D_123] :
      ( r1_tarski(C_120,k2_relset_1(A_121,B_122,D_123))
      | ~ r1_tarski(k6_relat_1(C_120),D_123)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_512,plain,(
    ! [A_124,B_125] :
      ( r1_tarski('#skF_2',k2_relset_1(A_124,B_125,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(resolution,[status(thm)],[c_34,c_508])).

tff(c_515,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_512])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.37  
% 2.36/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.37  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.36/1.37  
% 2.36/1.37  %Foreground sorts:
% 2.36/1.37  
% 2.36/1.37  
% 2.36/1.37  %Background operators:
% 2.36/1.37  
% 2.36/1.37  
% 2.36/1.37  %Foreground operators:
% 2.36/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.36/1.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.36/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.36/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.36/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.36/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.36/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.36/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.37  
% 2.70/1.39  tff(f_87, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 2.70/1.39  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.70/1.39  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.70/1.39  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.70/1.39  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.70/1.39  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.70/1.39  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.70/1.39  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.70/1.39  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.70/1.39  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.70/1.39  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.70/1.39  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.39  tff(c_178, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.70/1.39  tff(c_182, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_178])).
% 2.70/1.39  tff(c_32, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.39  tff(c_65, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.70/1.39  tff(c_183, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_65])).
% 2.70/1.39  tff(c_10, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.70/1.39  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.70/1.39  tff(c_58, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.39  tff(c_61, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_58])).
% 2.70/1.39  tff(c_64, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_61])).
% 2.70/1.39  tff(c_93, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.70/1.39  tff(c_97, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_93])).
% 2.70/1.39  tff(c_34, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.39  tff(c_209, plain, (![C_69, A_70, B_71, D_72]: (r1_tarski(C_69, k1_relset_1(A_70, B_71, D_72)) | ~r1_tarski(k6_relat_1(C_69), D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.70/1.39  tff(c_221, plain, (![A_75, B_76]: (r1_tarski('#skF_2', k1_relset_1(A_75, B_76, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(resolution, [status(thm)], [c_34, c_209])).
% 2.70/1.39  tff(c_224, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_221])).
% 2.70/1.39  tff(c_226, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_224])).
% 2.70/1.39  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.70/1.39  tff(c_18, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.39  tff(c_12, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.70/1.39  tff(c_139, plain, (![B_52, A_53]: (k5_relat_1(B_52, k6_relat_1(A_53))=B_52 | ~r1_tarski(k2_relat_1(B_52), A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.39  tff(c_142, plain, (![A_8, A_53]: (k5_relat_1(k6_relat_1(A_8), k6_relat_1(A_53))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_53) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_139])).
% 2.70/1.39  tff(c_145, plain, (![A_54, A_55]: (k5_relat_1(k6_relat_1(A_54), k6_relat_1(A_55))=k6_relat_1(A_54) | ~r1_tarski(A_54, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_142])).
% 2.70/1.39  tff(c_98, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=B_47 | ~r1_tarski(k1_relat_1(B_47), A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.39  tff(c_104, plain, (![A_46, A_8]: (k5_relat_1(k6_relat_1(A_46), k6_relat_1(A_8))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_46) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_98])).
% 2.70/1.39  tff(c_107, plain, (![A_46, A_8]: (k5_relat_1(k6_relat_1(A_46), k6_relat_1(A_8))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_104])).
% 2.70/1.39  tff(c_171, plain, (![A_57, A_56]: (k6_relat_1(A_57)=k6_relat_1(A_56) | ~r1_tarski(A_56, A_57) | ~r1_tarski(A_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_145, c_107])).
% 2.70/1.39  tff(c_176, plain, (![B_5, A_4]: (k6_relat_1(k1_relat_1(B_5))=k6_relat_1(A_4) | ~r1_tarski(A_4, k1_relat_1(B_5)) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_171])).
% 2.70/1.39  tff(c_229, plain, (k6_relat_1(k1_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_226, c_176])).
% 2.70/1.39  tff(c_234, plain, (k6_relat_1(k1_relat_1('#skF_3'))=k6_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_97, c_229])).
% 2.70/1.39  tff(c_267, plain, (k1_relat_1(k6_relat_1('#skF_2'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_234, c_10])).
% 2.70/1.39  tff(c_280, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_267])).
% 2.70/1.39  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_280])).
% 2.70/1.39  tff(c_283, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 2.70/1.39  tff(c_508, plain, (![C_120, A_121, B_122, D_123]: (r1_tarski(C_120, k2_relset_1(A_121, B_122, D_123)) | ~r1_tarski(k6_relat_1(C_120), D_123) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.70/1.39  tff(c_512, plain, (![A_124, B_125]: (r1_tarski('#skF_2', k2_relset_1(A_124, B_125, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(resolution, [status(thm)], [c_34, c_508])).
% 2.70/1.39  tff(c_515, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_512])).
% 2.70/1.39  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_283, c_515])).
% 2.70/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.39  
% 2.70/1.39  Inference rules
% 2.70/1.39  ----------------------
% 2.70/1.39  #Ref     : 0
% 2.70/1.39  #Sup     : 105
% 2.70/1.39  #Fact    : 0
% 2.70/1.39  #Define  : 0
% 2.70/1.39  #Split   : 3
% 2.70/1.39  #Chain   : 0
% 2.70/1.39  #Close   : 0
% 2.70/1.39  
% 2.70/1.39  Ordering : KBO
% 2.70/1.39  
% 2.70/1.39  Simplification rules
% 2.70/1.39  ----------------------
% 2.70/1.39  #Subsume      : 9
% 2.70/1.39  #Demod        : 41
% 2.70/1.39  #Tautology    : 39
% 2.70/1.39  #SimpNegUnit  : 2
% 2.70/1.39  #BackRed      : 1
% 2.70/1.39  
% 2.70/1.39  #Partial instantiations: 0
% 2.70/1.39  #Strategies tried      : 1
% 2.70/1.39  
% 2.70/1.39  Timing (in seconds)
% 2.70/1.39  ----------------------
% 2.70/1.39  Preprocessing        : 0.32
% 2.70/1.39  Parsing              : 0.18
% 2.70/1.39  CNF conversion       : 0.02
% 2.70/1.39  Main loop            : 0.28
% 2.70/1.39  Inferencing          : 0.11
% 2.70/1.39  Reduction            : 0.08
% 2.70/1.39  Demodulation         : 0.06
% 2.70/1.39  BG Simplification    : 0.02
% 2.70/1.39  Subsumption          : 0.05
% 2.70/1.39  Abstraction          : 0.02
% 2.70/1.39  MUC search           : 0.00
% 2.70/1.39  Cooper               : 0.00
% 2.70/1.39  Total                : 0.64
% 2.70/1.39  Index Insertion      : 0.00
% 2.70/1.39  Index Deletion       : 0.00
% 2.70/1.39  Index Matching       : 0.00
% 2.70/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
