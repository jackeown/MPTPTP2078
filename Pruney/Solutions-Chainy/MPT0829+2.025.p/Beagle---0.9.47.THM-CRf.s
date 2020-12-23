%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:24 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 102 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 177 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_60])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_66])).

tff(c_780,plain,(
    ! [C_138,B_139,A_140] :
      ( v5_relat_1(C_138,B_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_788,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_780])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_902,plain,(
    ! [A_157,B_158,C_159] :
      ( k2_relset_1(A_157,B_158,C_159) = k2_relat_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_911,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_902])).

tff(c_34,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_686,plain,(
    ! [C_115,A_116,B_117,D_118] :
      ( r1_tarski(C_115,k1_relset_1(A_116,B_117,D_118))
      | ~ r1_tarski(k6_relat_1(C_115),D_118)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_712,plain,(
    ! [A_121,B_122] :
      ( r1_tarski('#skF_2',k1_relset_1(A_121,B_122,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(resolution,[status(thm)],[c_36,c_686])).

tff(c_715,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_712])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_715])).

tff(c_720,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_921,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_720])).

tff(c_1091,plain,(
    ! [C_176,A_177,B_178,D_179] :
      ( r1_tarski(C_176,k2_relset_1(A_177,B_178,D_179))
      | ~ r1_tarski(k6_relat_1(C_176),D_179)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1111,plain,(
    ! [A_182,B_183] :
      ( r1_tarski('#skF_2',k2_relset_1(A_182,B_183,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(resolution,[status(thm)],[c_36,c_1091])).

tff(c_1114,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_1111])).

tff(c_1116,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_1114])).

tff(c_16,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_722,plain,(
    ! [C_123,A_124,B_125] :
      ( v4_relat_1(C_123,A_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_729,plain,(
    ! [A_24] : v4_relat_1(k6_relat_1(A_24),A_24) ),
    inference(resolution,[status(thm)],[c_28,c_722])).

tff(c_846,plain,(
    ! [C_148,B_149,A_150] :
      ( v4_relat_1(C_148,B_149)
      | ~ v4_relat_1(C_148,A_150)
      | ~ v1_relat_1(C_148)
      | ~ r1_tarski(A_150,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_848,plain,(
    ! [A_24,B_149] :
      ( v4_relat_1(k6_relat_1(A_24),B_149)
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ r1_tarski(A_24,B_149) ) ),
    inference(resolution,[status(thm)],[c_729,c_846])).

tff(c_869,plain,(
    ! [A_152,B_153] :
      ( v4_relat_1(k6_relat_1(A_152),B_153)
      | ~ r1_tarski(A_152,B_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_848])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_874,plain,(
    ! [A_152,B_153] :
      ( k7_relat_1(k6_relat_1(A_152),B_153) = k6_relat_1(A_152)
      | ~ v1_relat_1(k6_relat_1(A_152))
      | ~ r1_tarski(A_152,B_153) ) ),
    inference(resolution,[status(thm)],[c_869,c_12])).

tff(c_964,plain,(
    ! [A_162,B_163] :
      ( k7_relat_1(k6_relat_1(A_162),B_163) = k6_relat_1(A_162)
      | ~ r1_tarski(A_162,B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_874])).

tff(c_794,plain,(
    ! [B_142,A_143] :
      ( k1_relat_1(k7_relat_1(B_142,A_143)) = A_143
      | ~ r1_tarski(A_143,k1_relat_1(B_142))
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_801,plain,(
    ! [A_15,A_143] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_15),A_143)) = A_143
      | ~ r1_tarski(A_143,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_794])).

tff(c_804,plain,(
    ! [A_15,A_143] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_15),A_143)) = A_143
      | ~ r1_tarski(A_143,A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_801])).

tff(c_974,plain,(
    ! [A_162,B_163] :
      ( k1_relat_1(k6_relat_1(A_162)) = B_163
      | ~ r1_tarski(B_163,A_162)
      | ~ r1_tarski(A_162,B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_804])).

tff(c_988,plain,(
    ! [B_163,A_162] :
      ( B_163 = A_162
      | ~ r1_tarski(B_163,A_162)
      | ~ r1_tarski(A_162,B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_974])).

tff(c_1120,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1116,c_988])).

tff(c_1126,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_921,c_1120])).

tff(c_1136,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1126])).

tff(c_1140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_788,c_1136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.57  
% 3.44/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.57  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.44/1.57  
% 3.44/1.57  %Foreground sorts:
% 3.44/1.57  
% 3.44/1.57  
% 3.44/1.57  %Background operators:
% 3.44/1.57  
% 3.44/1.57  
% 3.44/1.57  %Foreground operators:
% 3.44/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.44/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.44/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.44/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.44/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.44/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.44/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.57  
% 3.52/1.59  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.52/1.59  tff(f_96, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 3.52/1.59  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.52/1.59  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.52/1.59  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.52/1.59  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.52/1.59  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 3.52/1.59  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.52/1.59  tff(f_40, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.52/1.59  tff(f_79, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.52/1.59  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 3.52/1.59  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.52/1.59  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.52/1.59  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.52/1.59  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.52/1.59  tff(c_60, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.59  tff(c_66, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_60])).
% 3.52/1.59  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_66])).
% 3.52/1.59  tff(c_780, plain, (![C_138, B_139, A_140]: (v5_relat_1(C_138, B_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.52/1.59  tff(c_788, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_780])).
% 3.52/1.59  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.52/1.59  tff(c_902, plain, (![A_157, B_158, C_159]: (k2_relset_1(A_157, B_158, C_159)=k2_relat_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.52/1.59  tff(c_911, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_902])).
% 3.52/1.59  tff(c_34, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.52/1.59  tff(c_73, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_34])).
% 3.52/1.59  tff(c_36, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.52/1.59  tff(c_686, plain, (![C_115, A_116, B_117, D_118]: (r1_tarski(C_115, k1_relset_1(A_116, B_117, D_118)) | ~r1_tarski(k6_relat_1(C_115), D_118) | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.52/1.59  tff(c_712, plain, (![A_121, B_122]: (r1_tarski('#skF_2', k1_relset_1(A_121, B_122, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(resolution, [status(thm)], [c_36, c_686])).
% 3.52/1.59  tff(c_715, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_712])).
% 3.52/1.59  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_715])).
% 3.52/1.59  tff(c_720, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 3.52/1.59  tff(c_921, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_911, c_720])).
% 3.52/1.59  tff(c_1091, plain, (![C_176, A_177, B_178, D_179]: (r1_tarski(C_176, k2_relset_1(A_177, B_178, D_179)) | ~r1_tarski(k6_relat_1(C_176), D_179) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.52/1.59  tff(c_1111, plain, (![A_182, B_183]: (r1_tarski('#skF_2', k2_relset_1(A_182, B_183, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(resolution, [status(thm)], [c_36, c_1091])).
% 3.52/1.59  tff(c_1114, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_1111])).
% 3.52/1.59  tff(c_1116, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_911, c_1114])).
% 3.52/1.59  tff(c_16, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.52/1.59  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.52/1.59  tff(c_28, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.52/1.59  tff(c_722, plain, (![C_123, A_124, B_125]: (v4_relat_1(C_123, A_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.52/1.59  tff(c_729, plain, (![A_24]: (v4_relat_1(k6_relat_1(A_24), A_24))), inference(resolution, [status(thm)], [c_28, c_722])).
% 3.52/1.59  tff(c_846, plain, (![C_148, B_149, A_150]: (v4_relat_1(C_148, B_149) | ~v4_relat_1(C_148, A_150) | ~v1_relat_1(C_148) | ~r1_tarski(A_150, B_149))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.59  tff(c_848, plain, (![A_24, B_149]: (v4_relat_1(k6_relat_1(A_24), B_149) | ~v1_relat_1(k6_relat_1(A_24)) | ~r1_tarski(A_24, B_149))), inference(resolution, [status(thm)], [c_729, c_846])).
% 3.52/1.59  tff(c_869, plain, (![A_152, B_153]: (v4_relat_1(k6_relat_1(A_152), B_153) | ~r1_tarski(A_152, B_153))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_848])).
% 3.52/1.59  tff(c_12, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.52/1.59  tff(c_874, plain, (![A_152, B_153]: (k7_relat_1(k6_relat_1(A_152), B_153)=k6_relat_1(A_152) | ~v1_relat_1(k6_relat_1(A_152)) | ~r1_tarski(A_152, B_153))), inference(resolution, [status(thm)], [c_869, c_12])).
% 3.52/1.59  tff(c_964, plain, (![A_162, B_163]: (k7_relat_1(k6_relat_1(A_162), B_163)=k6_relat_1(A_162) | ~r1_tarski(A_162, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_874])).
% 3.52/1.59  tff(c_794, plain, (![B_142, A_143]: (k1_relat_1(k7_relat_1(B_142, A_143))=A_143 | ~r1_tarski(A_143, k1_relat_1(B_142)) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.52/1.59  tff(c_801, plain, (![A_15, A_143]: (k1_relat_1(k7_relat_1(k6_relat_1(A_15), A_143))=A_143 | ~r1_tarski(A_143, A_15) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_794])).
% 3.52/1.59  tff(c_804, plain, (![A_15, A_143]: (k1_relat_1(k7_relat_1(k6_relat_1(A_15), A_143))=A_143 | ~r1_tarski(A_143, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_801])).
% 3.52/1.59  tff(c_974, plain, (![A_162, B_163]: (k1_relat_1(k6_relat_1(A_162))=B_163 | ~r1_tarski(B_163, A_162) | ~r1_tarski(A_162, B_163))), inference(superposition, [status(thm), theory('equality')], [c_964, c_804])).
% 3.52/1.59  tff(c_988, plain, (![B_163, A_162]: (B_163=A_162 | ~r1_tarski(B_163, A_162) | ~r1_tarski(A_162, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_974])).
% 3.52/1.59  tff(c_1120, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_1116, c_988])).
% 3.52/1.59  tff(c_1126, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_921, c_1120])).
% 3.52/1.59  tff(c_1136, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1126])).
% 3.52/1.59  tff(c_1140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_788, c_1136])).
% 3.52/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.59  
% 3.52/1.59  Inference rules
% 3.52/1.59  ----------------------
% 3.52/1.59  #Ref     : 0
% 3.52/1.59  #Sup     : 228
% 3.52/1.59  #Fact    : 0
% 3.52/1.59  #Define  : 0
% 3.52/1.59  #Split   : 7
% 3.52/1.59  #Chain   : 0
% 3.52/1.59  #Close   : 0
% 3.52/1.59  
% 3.52/1.59  Ordering : KBO
% 3.52/1.59  
% 3.52/1.59  Simplification rules
% 3.52/1.59  ----------------------
% 3.52/1.59  #Subsume      : 15
% 3.52/1.59  #Demod        : 159
% 3.52/1.59  #Tautology    : 87
% 3.52/1.59  #SimpNegUnit  : 2
% 3.52/1.59  #BackRed      : 3
% 3.52/1.59  
% 3.52/1.59  #Partial instantiations: 0
% 3.52/1.59  #Strategies tried      : 1
% 3.52/1.59  
% 3.52/1.59  Timing (in seconds)
% 3.52/1.59  ----------------------
% 3.52/1.59  Preprocessing        : 0.35
% 3.52/1.59  Parsing              : 0.19
% 3.52/1.59  CNF conversion       : 0.02
% 3.52/1.59  Main loop            : 0.44
% 3.52/1.59  Inferencing          : 0.17
% 3.52/1.59  Reduction            : 0.14
% 3.52/1.59  Demodulation         : 0.10
% 3.52/1.59  BG Simplification    : 0.02
% 3.52/1.59  Subsumption          : 0.08
% 3.52/1.59  Abstraction          : 0.02
% 3.52/1.59  MUC search           : 0.00
% 3.52/1.59  Cooper               : 0.00
% 3.52/1.59  Total                : 0.82
% 3.52/1.59  Index Insertion      : 0.00
% 3.52/1.59  Index Deletion       : 0.00
% 3.52/1.59  Index Matching       : 0.00
% 3.52/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
