%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:55 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 193 expanded)
%              Number of leaves         :   34 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 430 expanded)
%              Number of equality atoms :   42 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & k8_relset_1(A,B,C,k1_tarski(D)) = k1_xboole_0 )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_659,plain,(
    ! [C_139,A_140,B_141] :
      ( v1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_663,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_659])).

tff(c_405,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_409,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_405])).

tff(c_44,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_410,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_69])).

tff(c_78,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_96,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_100,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_96])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_392,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(A_99,k2_relat_1(B_100))
      | k10_relat_1(B_100,k1_tarski(A_99)) = k1_xboole_0
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_459,plain,(
    ! [A_120,B_121,B_122] :
      ( r2_hidden(A_120,B_121)
      | ~ r1_tarski(k2_relat_1(B_122),B_121)
      | k10_relat_1(B_122,k1_tarski(A_120)) = k1_xboole_0
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_392,c_2])).

tff(c_467,plain,(
    ! [A_123,A_124,B_125] :
      ( r2_hidden(A_123,A_124)
      | k10_relat_1(B_125,k1_tarski(A_123)) = k1_xboole_0
      | ~ v5_relat_1(B_125,A_124)
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_18,c_459])).

tff(c_471,plain,(
    ! [A_123] :
      ( r2_hidden(A_123,'#skF_3')
      | k10_relat_1('#skF_4',k1_tarski(A_123)) = k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_467])).

tff(c_476,plain,(
    ! [A_126] :
      ( r2_hidden(A_126,'#skF_3')
      | k10_relat_1('#skF_4',k1_tarski(A_126)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_471])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_381,plain,(
    ! [B_97,A_98] :
      ( k10_relat_1(B_97,k1_tarski(A_98)) != k1_xboole_0
      | ~ r2_hidden(A_98,k2_relat_1(B_97))
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_391,plain,(
    ! [B_97,B_2] :
      ( k10_relat_1(B_97,k1_tarski('#skF_1'(k2_relat_1(B_97),B_2))) != k1_xboole_0
      | ~ v1_relat_1(B_97)
      | r1_tarski(k2_relat_1(B_97),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_381])).

tff(c_483,plain,(
    ! [B_2] :
      ( ~ v1_relat_1('#skF_4')
      | r1_tarski(k2_relat_1('#skF_4'),B_2)
      | r2_hidden('#skF_1'(k2_relat_1('#skF_4'),B_2),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_391])).

tff(c_496,plain,(
    ! [B_127] :
      ( r1_tarski(k2_relat_1('#skF_4'),B_127)
      | r2_hidden('#skF_1'(k2_relat_1('#skF_4'),B_127),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_483])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_504,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_496,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_513,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_504,c_8])).

tff(c_524,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_513])).

tff(c_562,plain,(
    ! [A_131,B_132] :
      ( r1_tarski(A_131,k2_relat_1(B_132))
      | k10_relat_1(B_132,k1_tarski('#skF_1'(A_131,k2_relat_1(B_132)))) = k1_xboole_0
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_392,c_4])).

tff(c_443,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k8_relset_1(A_112,B_113,C_114,D_115) = k10_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_446,plain,(
    ! [D_115] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_115) = k10_relat_1('#skF_4',D_115) ),
    inference(resolution,[status(thm)],[c_34,c_443])).

tff(c_50,plain,(
    ! [D_28] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_28)) != k1_xboole_0
      | ~ r2_hidden(D_28,'#skF_3')
      | k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_361,plain,(
    ! [D_28] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_28)) != k1_xboole_0
      | ~ r2_hidden(D_28,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_50])).

tff(c_447,plain,(
    ! [D_28] :
      ( k10_relat_1('#skF_4',k1_tarski(D_28)) != k1_xboole_0
      | ~ r2_hidden(D_28,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_361])).

tff(c_577,plain,(
    ! [A_131] :
      ( ~ r2_hidden('#skF_1'(A_131,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_131,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_447])).

tff(c_604,plain,(
    ! [A_134] :
      ( ~ r2_hidden('#skF_1'(A_134,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_134,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_577])).

tff(c_620,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_604])).

tff(c_630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_524,c_620])).

tff(c_632,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_748,plain,(
    ! [A_167,B_168,C_169] :
      ( k2_relset_1(A_167,B_168,C_169) = k2_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_751,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_748])).

tff(c_753,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_751])).

tff(c_631,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_690,plain,(
    ! [C_153,B_154,A_155] :
      ( r2_hidden(C_153,B_154)
      | ~ r2_hidden(C_153,A_155)
      | ~ r1_tarski(A_155,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_696,plain,(
    ! [B_154] :
      ( r2_hidden('#skF_5',B_154)
      | ~ r1_tarski('#skF_3',B_154) ) ),
    inference(resolution,[status(thm)],[c_631,c_690])).

tff(c_709,plain,(
    ! [B_159,A_160] :
      ( k10_relat_1(B_159,k1_tarski(A_160)) != k1_xboole_0
      | ~ r2_hidden(A_160,k2_relat_1(B_159))
      | ~ v1_relat_1(B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_718,plain,(
    ! [B_159] :
      ( k10_relat_1(B_159,k1_tarski('#skF_5')) != k1_xboole_0
      | ~ v1_relat_1(B_159)
      | ~ r1_tarski('#skF_3',k2_relat_1(B_159)) ) ),
    inference(resolution,[status(thm)],[c_696,c_709])).

tff(c_757,plain,
    ( k10_relat_1('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_718])).

tff(c_776,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_663,c_757])).

tff(c_862,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k8_relset_1(A_177,B_178,C_179,D_180) = k10_relat_1(C_179,D_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_866,plain,(
    ! [D_181] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_181) = k10_relat_1('#skF_4',D_181) ),
    inference(resolution,[status(thm)],[c_34,c_862])).

tff(c_40,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_633,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_633])).

tff(c_640,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_872,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_640])).

tff(c_881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_776,c_872])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.48  
% 2.92/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.92/1.48  
% 2.92/1.48  %Foreground sorts:
% 2.92/1.48  
% 2.92/1.48  
% 2.92/1.48  %Background operators:
% 2.92/1.48  
% 2.92/1.48  
% 2.92/1.48  %Foreground operators:
% 2.92/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.92/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.92/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.48  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.92/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.92/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.92/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.92/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.92/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.92/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.92/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.92/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.48  
% 3.10/1.50  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.10/1.50  tff(f_86, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (k8_relset_1(A, B, C, k1_tarski(D)) = k1_xboole_0))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_2)).
% 3.10/1.50  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.10/1.50  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.10/1.50  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.50  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.10/1.50  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 3.10/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.10/1.50  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.10/1.50  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.10/1.50  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.10/1.50  tff(c_659, plain, (![C_139, A_140, B_141]: (v1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.10/1.50  tff(c_663, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_659])).
% 3.10/1.50  tff(c_405, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.50  tff(c_409, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_405])).
% 3.10/1.50  tff(c_44, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.10/1.50  tff(c_69, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_44])).
% 3.10/1.50  tff(c_410, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_409, c_69])).
% 3.10/1.50  tff(c_78, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.10/1.50  tff(c_82, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_78])).
% 3.10/1.50  tff(c_96, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.10/1.50  tff(c_100, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_96])).
% 3.10/1.50  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.10/1.50  tff(c_392, plain, (![A_99, B_100]: (r2_hidden(A_99, k2_relat_1(B_100)) | k10_relat_1(B_100, k1_tarski(A_99))=k1_xboole_0 | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.10/1.50  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.50  tff(c_459, plain, (![A_120, B_121, B_122]: (r2_hidden(A_120, B_121) | ~r1_tarski(k2_relat_1(B_122), B_121) | k10_relat_1(B_122, k1_tarski(A_120))=k1_xboole_0 | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_392, c_2])).
% 3.10/1.50  tff(c_467, plain, (![A_123, A_124, B_125]: (r2_hidden(A_123, A_124) | k10_relat_1(B_125, k1_tarski(A_123))=k1_xboole_0 | ~v5_relat_1(B_125, A_124) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_18, c_459])).
% 3.10/1.50  tff(c_471, plain, (![A_123]: (r2_hidden(A_123, '#skF_3') | k10_relat_1('#skF_4', k1_tarski(A_123))=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_467])).
% 3.10/1.50  tff(c_476, plain, (![A_126]: (r2_hidden(A_126, '#skF_3') | k10_relat_1('#skF_4', k1_tarski(A_126))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_471])).
% 3.10/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.50  tff(c_381, plain, (![B_97, A_98]: (k10_relat_1(B_97, k1_tarski(A_98))!=k1_xboole_0 | ~r2_hidden(A_98, k2_relat_1(B_97)) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.10/1.50  tff(c_391, plain, (![B_97, B_2]: (k10_relat_1(B_97, k1_tarski('#skF_1'(k2_relat_1(B_97), B_2)))!=k1_xboole_0 | ~v1_relat_1(B_97) | r1_tarski(k2_relat_1(B_97), B_2))), inference(resolution, [status(thm)], [c_6, c_381])).
% 3.10/1.50  tff(c_483, plain, (![B_2]: (~v1_relat_1('#skF_4') | r1_tarski(k2_relat_1('#skF_4'), B_2) | r2_hidden('#skF_1'(k2_relat_1('#skF_4'), B_2), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_476, c_391])).
% 3.10/1.50  tff(c_496, plain, (![B_127]: (r1_tarski(k2_relat_1('#skF_4'), B_127) | r2_hidden('#skF_1'(k2_relat_1('#skF_4'), B_127), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_483])).
% 3.10/1.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.50  tff(c_504, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_496, c_4])).
% 3.10/1.50  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.10/1.50  tff(c_513, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_504, c_8])).
% 3.10/1.50  tff(c_524, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_410, c_513])).
% 3.10/1.50  tff(c_562, plain, (![A_131, B_132]: (r1_tarski(A_131, k2_relat_1(B_132)) | k10_relat_1(B_132, k1_tarski('#skF_1'(A_131, k2_relat_1(B_132))))=k1_xboole_0 | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_392, c_4])).
% 3.10/1.50  tff(c_443, plain, (![A_112, B_113, C_114, D_115]: (k8_relset_1(A_112, B_113, C_114, D_115)=k10_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.50  tff(c_446, plain, (![D_115]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_115)=k10_relat_1('#skF_4', D_115))), inference(resolution, [status(thm)], [c_34, c_443])).
% 3.10/1.50  tff(c_50, plain, (![D_28]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_28))!=k1_xboole_0 | ~r2_hidden(D_28, '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.10/1.50  tff(c_361, plain, (![D_28]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_28))!=k1_xboole_0 | ~r2_hidden(D_28, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_69, c_50])).
% 3.10/1.50  tff(c_447, plain, (![D_28]: (k10_relat_1('#skF_4', k1_tarski(D_28))!=k1_xboole_0 | ~r2_hidden(D_28, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_446, c_361])).
% 3.10/1.50  tff(c_577, plain, (![A_131]: (~r2_hidden('#skF_1'(A_131, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_131, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_562, c_447])).
% 3.10/1.50  tff(c_604, plain, (![A_134]: (~r2_hidden('#skF_1'(A_134, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_134, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_577])).
% 3.10/1.50  tff(c_620, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_604])).
% 3.10/1.50  tff(c_630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_524, c_620])).
% 3.10/1.50  tff(c_632, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 3.10/1.50  tff(c_748, plain, (![A_167, B_168, C_169]: (k2_relset_1(A_167, B_168, C_169)=k2_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.50  tff(c_751, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_748])).
% 3.10/1.50  tff(c_753, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_632, c_751])).
% 3.10/1.50  tff(c_631, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.10/1.50  tff(c_690, plain, (![C_153, B_154, A_155]: (r2_hidden(C_153, B_154) | ~r2_hidden(C_153, A_155) | ~r1_tarski(A_155, B_154))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.50  tff(c_696, plain, (![B_154]: (r2_hidden('#skF_5', B_154) | ~r1_tarski('#skF_3', B_154))), inference(resolution, [status(thm)], [c_631, c_690])).
% 3.10/1.50  tff(c_709, plain, (![B_159, A_160]: (k10_relat_1(B_159, k1_tarski(A_160))!=k1_xboole_0 | ~r2_hidden(A_160, k2_relat_1(B_159)) | ~v1_relat_1(B_159))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.10/1.50  tff(c_718, plain, (![B_159]: (k10_relat_1(B_159, k1_tarski('#skF_5'))!=k1_xboole_0 | ~v1_relat_1(B_159) | ~r1_tarski('#skF_3', k2_relat_1(B_159)))), inference(resolution, [status(thm)], [c_696, c_709])).
% 3.10/1.50  tff(c_757, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_753, c_718])).
% 3.10/1.50  tff(c_776, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_663, c_757])).
% 3.10/1.50  tff(c_862, plain, (![A_177, B_178, C_179, D_180]: (k8_relset_1(A_177, B_178, C_179, D_180)=k10_relat_1(C_179, D_180) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.50  tff(c_866, plain, (![D_181]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_181)=k10_relat_1('#skF_4', D_181))), inference(resolution, [status(thm)], [c_34, c_862])).
% 3.10/1.50  tff(c_40, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.10/1.50  tff(c_633, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_40])).
% 3.10/1.50  tff(c_639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_632, c_633])).
% 3.10/1.50  tff(c_640, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.10/1.50  tff(c_872, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_866, c_640])).
% 3.10/1.50  tff(c_881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_776, c_872])).
% 3.10/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  Inference rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Ref     : 0
% 3.10/1.50  #Sup     : 165
% 3.10/1.50  #Fact    : 0
% 3.10/1.50  #Define  : 0
% 3.10/1.50  #Split   : 3
% 3.10/1.50  #Chain   : 0
% 3.10/1.50  #Close   : 0
% 3.10/1.50  
% 3.10/1.50  Ordering : KBO
% 3.10/1.50  
% 3.10/1.50  Simplification rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Subsume      : 14
% 3.10/1.50  #Demod        : 68
% 3.10/1.50  #Tautology    : 73
% 3.10/1.50  #SimpNegUnit  : 7
% 3.10/1.50  #BackRed      : 4
% 3.10/1.50  
% 3.10/1.50  #Partial instantiations: 0
% 3.10/1.50  #Strategies tried      : 1
% 3.10/1.50  
% 3.10/1.50  Timing (in seconds)
% 3.10/1.50  ----------------------
% 3.10/1.51  Preprocessing        : 0.31
% 3.10/1.51  Parsing              : 0.16
% 3.10/1.51  CNF conversion       : 0.02
% 3.10/1.51  Main loop            : 0.35
% 3.10/1.51  Inferencing          : 0.14
% 3.10/1.51  Reduction            : 0.10
% 3.10/1.51  Demodulation         : 0.07
% 3.10/1.51  BG Simplification    : 0.02
% 3.10/1.51  Subsumption          : 0.07
% 3.10/1.51  Abstraction          : 0.02
% 3.10/1.51  MUC search           : 0.00
% 3.10/1.51  Cooper               : 0.00
% 3.10/1.51  Total                : 0.70
% 3.10/1.51  Index Insertion      : 0.00
% 3.10/1.51  Index Deletion       : 0.00
% 3.10/1.51  Index Matching       : 0.00
% 3.10/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
