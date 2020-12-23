%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:15 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 466 expanded)
%              Number of leaves         :   43 ( 190 expanded)
%              Depth                    :   16
%              Number of atoms          :  268 (1459 expanded)
%              Number of equality atoms :   60 ( 298 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_48,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_67,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_67])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_465,plain,(
    ! [C_131,A_132,B_133] :
      ( v2_funct_1(C_131)
      | ~ v3_funct_2(C_131,A_132,B_133)
      | ~ v1_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_468,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_465])).

tff(c_471,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_468])).

tff(c_331,plain,(
    ! [C_100,B_101,A_102] :
      ( v5_relat_1(C_100,B_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_335,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_331])).

tff(c_340,plain,(
    ! [B_104,A_105] :
      ( k2_relat_1(B_104) = A_105
      | ~ v2_funct_2(B_104,A_105)
      | ~ v5_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_343,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_335,c_340])).

tff(c_346,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_343])).

tff(c_356,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_411,plain,(
    ! [C_123,B_124,A_125] :
      ( v2_funct_2(C_123,B_124)
      | ~ v3_funct_2(C_123,A_125,B_124)
      | ~ v1_funct_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_414,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_411])).

tff(c_417,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_414])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_417])).

tff(c_420,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_8,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_429,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_8])).

tff(c_435,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_429])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_592,plain,(
    ! [A_152,B_153] :
      ( k2_funct_2(A_152,B_153) = k2_funct_1(B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_zfmisc_1(A_152,A_152)))
      | ~ v3_funct_2(B_153,A_152,A_152)
      | ~ v1_funct_2(B_153,A_152,A_152)
      | ~ v1_funct_1(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_595,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_592])).

tff(c_598,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_595])).

tff(c_683,plain,(
    ! [A_163,B_164] :
      ( m1_subset_1(k2_funct_2(A_163,B_164),k1_zfmisc_1(k2_zfmisc_1(A_163,A_163)))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(k2_zfmisc_1(A_163,A_163)))
      | ~ v3_funct_2(B_164,A_163,A_163)
      | ~ v1_funct_2(B_164,A_163,A_163)
      | ~ v1_funct_1(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_715,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_683])).

tff(c_730,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_715])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_759,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_730,c_2])).

tff(c_784,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_759])).

tff(c_575,plain,(
    ! [A_149,B_150] :
      ( v1_funct_1(k2_funct_2(A_149,B_150))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_zfmisc_1(A_149,A_149)))
      | ~ v3_funct_2(B_150,A_149,A_149)
      | ~ v1_funct_2(B_150,A_149,A_149)
      | ~ v1_funct_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_578,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_575])).

tff(c_581,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_578])).

tff(c_599,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_581])).

tff(c_618,plain,(
    ! [A_156,B_157] :
      ( v3_funct_2(k2_funct_2(A_156,B_157),A_156,A_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_zfmisc_1(A_156,A_156)))
      | ~ v3_funct_2(B_157,A_156,A_156)
      | ~ v1_funct_2(B_157,A_156,A_156)
      | ~ v1_funct_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_620,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_618])).

tff(c_623,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_598,c_620])).

tff(c_26,plain,(
    ! [C_30,B_29,A_28] :
      ( v2_funct_2(C_30,B_29)
      | ~ v3_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_743,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_730,c_26])).

tff(c_774,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_623,c_743])).

tff(c_18,plain,(
    ! [C_19,B_18,A_17] :
      ( v5_relat_1(C_19,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_780,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_730,c_18])).

tff(c_34,plain,(
    ! [B_32,A_31] :
      ( k2_relat_1(B_32) = A_31
      | ~ v2_funct_2(B_32,A_31)
      | ~ v5_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_804,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_780,c_34])).

tff(c_807,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_774,c_804])).

tff(c_20,plain,(
    ! [C_19,A_17,B_18] :
      ( v4_relat_1(C_19,A_17)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_781,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_730,c_20])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_810,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_781,c_10])).

tff(c_813,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_810])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_856,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_6])).

tff(c_868,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_807,c_856])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k9_relat_1(k2_funct_1(B_14),A_13) = k10_relat_1(B_14,A_13)
      | ~ v2_funct_1(B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_879,plain,
    ( k10_relat_1('#skF_3','#skF_1') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_14])).

tff(c_890,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56,c_471,c_435,c_879])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k10_relat_1(B_16,k9_relat_1(B_16,A_15)) = A_15
      | ~ v2_funct_1(B_16)
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_897,plain,(
    ! [A_15] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_15)) = A_15
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_16])).

tff(c_1432,plain,(
    ! [A_185] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_185)) = A_185
      | ~ r1_tarski(A_185,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56,c_471,c_897])).

tff(c_498,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k7_relset_1(A_137,B_138,C_139,D_140) = k9_relat_1(C_139,D_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_501,plain,(
    ! [D_140] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_140) = k9_relat_1('#skF_3',D_140) ),
    inference(resolution,[status(thm)],[c_50,c_498])).

tff(c_442,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( k8_relset_1(A_126,B_127,C_128,D_129) = k10_relat_1(C_128,D_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_445,plain,(
    ! [D_129] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_129) = k10_relat_1('#skF_3',D_129) ),
    inference(resolution,[status(thm)],[c_50,c_442])).

tff(c_108,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_121,plain,(
    ! [B_53,A_54] :
      ( k2_relat_1(B_53) = A_54
      | ~ v2_funct_2(B_53,A_54)
      | ~ v5_relat_1(B_53,A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_124,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_121])).

tff(c_127,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_124])).

tff(c_128,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_176,plain,(
    ! [C_72,B_73,A_74] :
      ( v2_funct_2(C_72,B_73)
      | ~ v3_funct_2(C_72,A_74,B_73)
      | ~ v1_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_179,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_176])).

tff(c_182,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_179])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_182])).

tff(c_185,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_220,plain,(
    ! [B_77,A_78] :
      ( k9_relat_1(B_77,k10_relat_1(B_77,A_78)) = A_78
      | ~ r1_tarski(A_78,k2_relat_1(B_77))
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_222,plain,(
    ! [A_78] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_78)) = A_78
      | ~ r1_tarski(A_78,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_220])).

tff(c_226,plain,(
    ! [A_78] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_78)) = A_78
      | ~ r1_tarski(A_78,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56,c_222])).

tff(c_267,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k7_relset_1(A_88,B_89,C_90,D_91) = k9_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_270,plain,(
    ! [D_91] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_91) = k9_relat_1('#skF_3',D_91) ),
    inference(resolution,[status(thm)],[c_50,c_267])).

tff(c_253,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k8_relset_1(A_83,B_84,C_85,D_86) = k10_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_256,plain,(
    ! [D_86] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_86) = k10_relat_1('#skF_3',D_86) ),
    inference(resolution,[status(thm)],[c_50,c_253])).

tff(c_46,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_74,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_257,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_74])).

tff(c_271,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_257])).

tff(c_283,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_271])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_283])).

tff(c_288,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_450,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_288])).

tff(c_502,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_450])).

tff(c_1449,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1432,c_502])).

tff(c_1469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:28:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.61  
% 3.53/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.61  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.53/1.61  
% 3.53/1.61  %Foreground sorts:
% 3.53/1.61  
% 3.53/1.61  
% 3.53/1.61  %Background operators:
% 3.53/1.61  
% 3.53/1.61  
% 3.53/1.61  %Foreground operators:
% 3.53/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.53/1.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.53/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.53/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.53/1.61  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.53/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.53/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.53/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.61  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.53/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.53/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.53/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.53/1.61  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.53/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.61  
% 3.91/1.64  tff(f_149, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 3.91/1.64  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.91/1.64  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.91/1.64  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.91/1.64  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.91/1.64  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 3.91/1.64  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.91/1.64  tff(f_134, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.91/1.64  tff(f_124, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 3.91/1.64  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.91/1.64  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.91/1.64  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 3.91/1.64  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 3.91/1.64  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.91/1.64  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.91/1.64  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.91/1.64  tff(c_48, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.91/1.64  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.91/1.64  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.91/1.64  tff(c_67, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.64  tff(c_70, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_67])).
% 3.91/1.64  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_70])).
% 3.91/1.64  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.91/1.64  tff(c_52, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.91/1.64  tff(c_465, plain, (![C_131, A_132, B_133]: (v2_funct_1(C_131) | ~v3_funct_2(C_131, A_132, B_133) | ~v1_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.91/1.64  tff(c_468, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_465])).
% 3.91/1.64  tff(c_471, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_468])).
% 3.91/1.64  tff(c_331, plain, (![C_100, B_101, A_102]: (v5_relat_1(C_100, B_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.64  tff(c_335, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_331])).
% 3.91/1.64  tff(c_340, plain, (![B_104, A_105]: (k2_relat_1(B_104)=A_105 | ~v2_funct_2(B_104, A_105) | ~v5_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.91/1.64  tff(c_343, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_335, c_340])).
% 3.91/1.64  tff(c_346, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_343])).
% 3.91/1.64  tff(c_356, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_346])).
% 3.91/1.64  tff(c_411, plain, (![C_123, B_124, A_125]: (v2_funct_2(C_123, B_124) | ~v3_funct_2(C_123, A_125, B_124) | ~v1_funct_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.91/1.64  tff(c_414, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_411])).
% 3.91/1.64  tff(c_417, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_414])).
% 3.91/1.64  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_356, c_417])).
% 3.91/1.64  tff(c_420, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_346])).
% 3.91/1.64  tff(c_8, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.91/1.64  tff(c_429, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_420, c_8])).
% 3.91/1.64  tff(c_435, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_429])).
% 3.91/1.64  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.91/1.64  tff(c_592, plain, (![A_152, B_153]: (k2_funct_2(A_152, B_153)=k2_funct_1(B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(k2_zfmisc_1(A_152, A_152))) | ~v3_funct_2(B_153, A_152, A_152) | ~v1_funct_2(B_153, A_152, A_152) | ~v1_funct_1(B_153))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.91/1.64  tff(c_595, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_592])).
% 3.91/1.64  tff(c_598, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_595])).
% 3.91/1.64  tff(c_683, plain, (![A_163, B_164]: (m1_subset_1(k2_funct_2(A_163, B_164), k1_zfmisc_1(k2_zfmisc_1(A_163, A_163))) | ~m1_subset_1(B_164, k1_zfmisc_1(k2_zfmisc_1(A_163, A_163))) | ~v3_funct_2(B_164, A_163, A_163) | ~v1_funct_2(B_164, A_163, A_163) | ~v1_funct_1(B_164))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.91/1.64  tff(c_715, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_598, c_683])).
% 3.91/1.64  tff(c_730, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_715])).
% 3.91/1.64  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.64  tff(c_759, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_730, c_2])).
% 3.91/1.64  tff(c_784, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_759])).
% 3.91/1.64  tff(c_575, plain, (![A_149, B_150]: (v1_funct_1(k2_funct_2(A_149, B_150)) | ~m1_subset_1(B_150, k1_zfmisc_1(k2_zfmisc_1(A_149, A_149))) | ~v3_funct_2(B_150, A_149, A_149) | ~v1_funct_2(B_150, A_149, A_149) | ~v1_funct_1(B_150))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.91/1.64  tff(c_578, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_575])).
% 3.91/1.64  tff(c_581, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_578])).
% 3.91/1.64  tff(c_599, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_598, c_581])).
% 3.91/1.64  tff(c_618, plain, (![A_156, B_157]: (v3_funct_2(k2_funct_2(A_156, B_157), A_156, A_156) | ~m1_subset_1(B_157, k1_zfmisc_1(k2_zfmisc_1(A_156, A_156))) | ~v3_funct_2(B_157, A_156, A_156) | ~v1_funct_2(B_157, A_156, A_156) | ~v1_funct_1(B_157))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.91/1.64  tff(c_620, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_618])).
% 3.91/1.64  tff(c_623, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_598, c_620])).
% 3.91/1.64  tff(c_26, plain, (![C_30, B_29, A_28]: (v2_funct_2(C_30, B_29) | ~v3_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.91/1.64  tff(c_743, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_730, c_26])).
% 3.91/1.64  tff(c_774, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_623, c_743])).
% 3.91/1.64  tff(c_18, plain, (![C_19, B_18, A_17]: (v5_relat_1(C_19, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.64  tff(c_780, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_730, c_18])).
% 3.91/1.64  tff(c_34, plain, (![B_32, A_31]: (k2_relat_1(B_32)=A_31 | ~v2_funct_2(B_32, A_31) | ~v5_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.91/1.64  tff(c_804, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_780, c_34])).
% 3.91/1.64  tff(c_807, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_784, c_774, c_804])).
% 3.91/1.64  tff(c_20, plain, (![C_19, A_17, B_18]: (v4_relat_1(C_19, A_17) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.64  tff(c_781, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_730, c_20])).
% 3.91/1.64  tff(c_10, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.91/1.64  tff(c_810, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_781, c_10])).
% 3.91/1.64  tff(c_813, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_784, c_810])).
% 3.91/1.64  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.91/1.64  tff(c_856, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_813, c_6])).
% 3.91/1.64  tff(c_868, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_784, c_807, c_856])).
% 3.91/1.64  tff(c_14, plain, (![B_14, A_13]: (k9_relat_1(k2_funct_1(B_14), A_13)=k10_relat_1(B_14, A_13) | ~v2_funct_1(B_14) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.91/1.64  tff(c_879, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_868, c_14])).
% 3.91/1.64  tff(c_890, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56, c_471, c_435, c_879])).
% 3.91/1.64  tff(c_16, plain, (![B_16, A_15]: (k10_relat_1(B_16, k9_relat_1(B_16, A_15))=A_15 | ~v2_funct_1(B_16) | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.64  tff(c_897, plain, (![A_15]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_15))=A_15 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_15, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_890, c_16])).
% 3.91/1.64  tff(c_1432, plain, (![A_185]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_185))=A_185 | ~r1_tarski(A_185, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56, c_471, c_897])).
% 3.91/1.64  tff(c_498, plain, (![A_137, B_138, C_139, D_140]: (k7_relset_1(A_137, B_138, C_139, D_140)=k9_relat_1(C_139, D_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.91/1.64  tff(c_501, plain, (![D_140]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_140)=k9_relat_1('#skF_3', D_140))), inference(resolution, [status(thm)], [c_50, c_498])).
% 3.91/1.64  tff(c_442, plain, (![A_126, B_127, C_128, D_129]: (k8_relset_1(A_126, B_127, C_128, D_129)=k10_relat_1(C_128, D_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.91/1.64  tff(c_445, plain, (![D_129]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_129)=k10_relat_1('#skF_3', D_129))), inference(resolution, [status(thm)], [c_50, c_442])).
% 3.91/1.64  tff(c_108, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.64  tff(c_112, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_108])).
% 3.91/1.64  tff(c_121, plain, (![B_53, A_54]: (k2_relat_1(B_53)=A_54 | ~v2_funct_2(B_53, A_54) | ~v5_relat_1(B_53, A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.91/1.64  tff(c_124, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_121])).
% 3.91/1.64  tff(c_127, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_124])).
% 3.91/1.64  tff(c_128, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_127])).
% 3.91/1.64  tff(c_176, plain, (![C_72, B_73, A_74]: (v2_funct_2(C_72, B_73) | ~v3_funct_2(C_72, A_74, B_73) | ~v1_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.91/1.64  tff(c_179, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_176])).
% 3.91/1.64  tff(c_182, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_179])).
% 3.91/1.64  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_182])).
% 3.91/1.64  tff(c_185, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_127])).
% 3.91/1.64  tff(c_220, plain, (![B_77, A_78]: (k9_relat_1(B_77, k10_relat_1(B_77, A_78))=A_78 | ~r1_tarski(A_78, k2_relat_1(B_77)) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.91/1.64  tff(c_222, plain, (![A_78]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_78))=A_78 | ~r1_tarski(A_78, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_220])).
% 3.91/1.64  tff(c_226, plain, (![A_78]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_78))=A_78 | ~r1_tarski(A_78, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56, c_222])).
% 3.91/1.64  tff(c_267, plain, (![A_88, B_89, C_90, D_91]: (k7_relset_1(A_88, B_89, C_90, D_91)=k9_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.91/1.64  tff(c_270, plain, (![D_91]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_91)=k9_relat_1('#skF_3', D_91))), inference(resolution, [status(thm)], [c_50, c_267])).
% 3.91/1.64  tff(c_253, plain, (![A_83, B_84, C_85, D_86]: (k8_relset_1(A_83, B_84, C_85, D_86)=k10_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.91/1.64  tff(c_256, plain, (![D_86]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_86)=k10_relat_1('#skF_3', D_86))), inference(resolution, [status(thm)], [c_50, c_253])).
% 3.91/1.64  tff(c_46, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.91/1.64  tff(c_74, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_46])).
% 3.91/1.64  tff(c_257, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_74])).
% 3.91/1.64  tff(c_271, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_270, c_257])).
% 3.91/1.64  tff(c_283, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_226, c_271])).
% 3.91/1.64  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_283])).
% 3.91/1.64  tff(c_288, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_46])).
% 3.91/1.64  tff(c_450, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_288])).
% 3.91/1.64  tff(c_502, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_501, c_450])).
% 3.91/1.64  tff(c_1449, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1432, c_502])).
% 3.91/1.64  tff(c_1469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1449])).
% 3.91/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.64  
% 3.91/1.64  Inference rules
% 3.91/1.64  ----------------------
% 3.91/1.64  #Ref     : 0
% 3.91/1.64  #Sup     : 315
% 3.91/1.64  #Fact    : 0
% 3.91/1.64  #Define  : 0
% 3.91/1.64  #Split   : 6
% 3.91/1.64  #Chain   : 0
% 3.91/1.64  #Close   : 0
% 3.91/1.64  
% 3.91/1.64  Ordering : KBO
% 3.91/1.64  
% 3.91/1.64  Simplification rules
% 3.91/1.64  ----------------------
% 3.91/1.64  #Subsume      : 18
% 3.91/1.64  #Demod        : 556
% 3.91/1.64  #Tautology    : 135
% 3.91/1.64  #SimpNegUnit  : 2
% 3.91/1.64  #BackRed      : 24
% 3.91/1.64  
% 3.91/1.64  #Partial instantiations: 0
% 3.91/1.64  #Strategies tried      : 1
% 3.91/1.64  
% 3.91/1.64  Timing (in seconds)
% 3.91/1.64  ----------------------
% 3.91/1.64  Preprocessing        : 0.35
% 3.91/1.64  Parsing              : 0.18
% 3.91/1.64  CNF conversion       : 0.02
% 3.91/1.64  Main loop            : 0.52
% 3.91/1.64  Inferencing          : 0.19
% 3.91/1.64  Reduction            : 0.19
% 3.91/1.64  Demodulation         : 0.14
% 3.91/1.64  BG Simplification    : 0.03
% 3.91/1.64  Subsumption          : 0.07
% 3.91/1.64  Abstraction          : 0.03
% 3.91/1.64  MUC search           : 0.00
% 3.91/1.64  Cooper               : 0.00
% 3.91/1.64  Total                : 0.92
% 3.91/1.64  Index Insertion      : 0.00
% 3.91/1.64  Index Deletion       : 0.00
% 3.91/1.64  Index Matching       : 0.00
% 3.91/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
