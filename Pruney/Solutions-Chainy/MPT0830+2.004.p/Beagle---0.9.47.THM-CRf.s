%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:26 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 225 expanded)
%              Number of leaves         :   29 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  116 ( 391 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_relset_1,type,(
    r1_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

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

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k7_relat_1(B_12,A_11),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_38])).

tff(c_109,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_tarski(A_64,C_65)
      | ~ r1_tarski(B_66,C_65)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_69] :
      ( r1_tarski(A_69,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_69,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_109])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_4,A_49,B_50] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_49,B_50)) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_148,plain,(
    ! [A_70] :
      ( v1_relat_1(A_70)
      | ~ r1_tarski(A_70,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_131,c_56])).

tff(c_156,plain,(
    ! [A_11] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_11))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_148])).

tff(c_160,plain,(
    ! [A_11] : v1_relat_1(k7_relat_1('#skF_4',A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_156])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_235,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_244,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_235])).

tff(c_249,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1(k1_relset_1(A_98,B_99,C_100),k1_zfmisc_1(A_98))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_269,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_249])).

tff(c_276,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_269])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_284,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_276,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_449,plain,(
    ! [A_106] :
      ( r1_tarski(A_106,'#skF_1')
      | ~ r1_tarski(A_106,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_284,c_2])).

tff(c_456,plain,(
    ! [A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_13)),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_449])).

tff(c_483,plain,(
    ! [A_108] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_108)),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_456])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_488,plain,(
    ! [A_108] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_108),'#skF_1') = k7_relat_1('#skF_4',A_108)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_108)) ) ),
    inference(resolution,[status(thm)],[c_483,c_16])).

tff(c_510,plain,(
    ! [A_109] : k7_relat_1(k7_relat_1('#skF_4',A_109),'#skF_1') = k7_relat_1('#skF_4',A_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_488])).

tff(c_537,plain,(
    ! [A_109] :
      ( r1_tarski(k7_relat_1('#skF_4',A_109),k7_relat_1('#skF_4',A_109))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_109)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_12])).

tff(c_579,plain,(
    ! [A_114] : r1_tarski(k7_relat_1('#skF_4',A_114),k7_relat_1('#skF_4',A_114)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_537])).

tff(c_120,plain,(
    ! [A_64,B_12,A_11] :
      ( r1_tarski(A_64,B_12)
      | ~ r1_tarski(A_64,k7_relat_1(B_12,A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_109])).

tff(c_584,plain,(
    ! [A_114] :
      ( r1_tarski(k7_relat_1('#skF_4',A_114),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_579,c_120])).

tff(c_605,plain,(
    ! [A_114] : r1_tarski(k7_relat_1('#skF_4',A_114),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_584])).

tff(c_528,plain,(
    ! [A_109] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_109)),k1_relat_1(k7_relat_1('#skF_4',A_109)))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_109)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_14])).

tff(c_813,plain,(
    ! [A_133] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_133)),k1_relat_1(k7_relat_1('#skF_4',A_133))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_528])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_119,plain,(
    ! [A_64,A_9,B_10] :
      ( r1_tarski(A_64,A_9)
      | ~ r1_tarski(A_64,k1_relat_1(k7_relat_1(B_10,A_9)))
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_819,plain,(
    ! [A_133] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_133)),A_133)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_813,c_119])).

tff(c_846,plain,(
    ! [A_133] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_133)),A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_819])).

tff(c_121,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_64,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_109])).

tff(c_930,plain,(
    ! [D_135,B_136,C_137,A_138] :
      ( m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(B_136,C_137)))
      | ~ r1_tarski(k1_relat_1(D_135),B_136)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(A_138,C_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3381,plain,(
    ! [A_245,B_246,C_247,A_248] :
      ( m1_subset_1(A_245,k1_zfmisc_1(k2_zfmisc_1(B_246,C_247)))
      | ~ r1_tarski(k1_relat_1(A_245),B_246)
      | ~ r1_tarski(A_245,k2_zfmisc_1(A_248,C_247)) ) ),
    inference(resolution,[status(thm)],[c_6,c_930])).

tff(c_8916,plain,(
    ! [A_414,B_415] :
      ( m1_subset_1(A_414,k1_zfmisc_1(k2_zfmisc_1(B_415,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(A_414),B_415)
      | ~ r1_tarski(A_414,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_121,c_3381])).

tff(c_390,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k5_relset_1(A_102,B_103,C_104,D_105) = k7_relat_1(C_104,D_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_401,plain,(
    ! [D_105] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_105) = k7_relat_1('#skF_4',D_105) ),
    inference(resolution,[status(thm)],[c_36,c_390])).

tff(c_34,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_473,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_34])).

tff(c_8941,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8916,c_473])).

tff(c_8969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_846,c_8941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.22/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.67  
% 7.22/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.67  %$ r1_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.22/2.67  
% 7.22/2.67  %Foreground sorts:
% 7.22/2.67  
% 7.22/2.67  
% 7.22/2.67  %Background operators:
% 7.22/2.67  
% 7.22/2.67  
% 7.22/2.67  %Foreground operators:
% 7.22/2.67  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 7.22/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.22/2.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.22/2.67  tff(r1_relset_1, type, r1_relset_1: ($i * $i * $i * $i) > $o).
% 7.22/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.22/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.22/2.67  tff('#skF_3', type, '#skF_3': $i).
% 7.22/2.67  tff('#skF_1', type, '#skF_1': $i).
% 7.22/2.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.22/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.22/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.22/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.22/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.22/2.67  tff('#skF_4', type, '#skF_4': $i).
% 7.22/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.22/2.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.22/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.22/2.67  
% 7.22/2.69  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 7.22/2.69  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.22/2.69  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 7.22/2.69  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.22/2.69  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.22/2.69  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 7.22/2.69  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.22/2.69  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 7.22/2.69  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 7.22/2.69  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 7.22/2.69  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 7.22/2.69  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 7.22/2.69  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.22/2.69  tff(c_48, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.22/2.69  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_48])).
% 7.22/2.69  tff(c_12, plain, (![B_12, A_11]: (r1_tarski(k7_relat_1(B_12, A_11), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.22/2.69  tff(c_38, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.22/2.69  tff(c_46, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_38])).
% 7.22/2.69  tff(c_109, plain, (![A_64, C_65, B_66]: (r1_tarski(A_64, C_65) | ~r1_tarski(B_66, C_65) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.22/2.69  tff(c_131, plain, (![A_69]: (r1_tarski(A_69, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_69, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_109])).
% 7.22/2.69  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.22/2.69  tff(c_56, plain, (![A_4, A_49, B_50]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_49, B_50)))), inference(resolution, [status(thm)], [c_6, c_48])).
% 7.22/2.69  tff(c_148, plain, (![A_70]: (v1_relat_1(A_70) | ~r1_tarski(A_70, '#skF_4'))), inference(resolution, [status(thm)], [c_131, c_56])).
% 7.22/2.69  tff(c_156, plain, (![A_11]: (v1_relat_1(k7_relat_1('#skF_4', A_11)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_148])).
% 7.22/2.69  tff(c_160, plain, (![A_11]: (v1_relat_1(k7_relat_1('#skF_4', A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_156])).
% 7.22/2.69  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.22/2.69  tff(c_235, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.22/2.69  tff(c_244, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_235])).
% 7.22/2.69  tff(c_249, plain, (![A_98, B_99, C_100]: (m1_subset_1(k1_relset_1(A_98, B_99, C_100), k1_zfmisc_1(A_98)) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.22/2.69  tff(c_269, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_244, c_249])).
% 7.22/2.69  tff(c_276, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_269])).
% 7.22/2.69  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.22/2.69  tff(c_284, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_276, c_4])).
% 7.22/2.69  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.22/2.69  tff(c_449, plain, (![A_106]: (r1_tarski(A_106, '#skF_1') | ~r1_tarski(A_106, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_284, c_2])).
% 7.22/2.69  tff(c_456, plain, (![A_13]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_13)), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_449])).
% 7.22/2.69  tff(c_483, plain, (![A_108]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_108)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_456])).
% 7.22/2.69  tff(c_16, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~r1_tarski(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.22/2.69  tff(c_488, plain, (![A_108]: (k7_relat_1(k7_relat_1('#skF_4', A_108), '#skF_1')=k7_relat_1('#skF_4', A_108) | ~v1_relat_1(k7_relat_1('#skF_4', A_108)))), inference(resolution, [status(thm)], [c_483, c_16])).
% 7.22/2.69  tff(c_510, plain, (![A_109]: (k7_relat_1(k7_relat_1('#skF_4', A_109), '#skF_1')=k7_relat_1('#skF_4', A_109))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_488])).
% 7.22/2.69  tff(c_537, plain, (![A_109]: (r1_tarski(k7_relat_1('#skF_4', A_109), k7_relat_1('#skF_4', A_109)) | ~v1_relat_1(k7_relat_1('#skF_4', A_109)))), inference(superposition, [status(thm), theory('equality')], [c_510, c_12])).
% 7.22/2.69  tff(c_579, plain, (![A_114]: (r1_tarski(k7_relat_1('#skF_4', A_114), k7_relat_1('#skF_4', A_114)))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_537])).
% 7.22/2.69  tff(c_120, plain, (![A_64, B_12, A_11]: (r1_tarski(A_64, B_12) | ~r1_tarski(A_64, k7_relat_1(B_12, A_11)) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_12, c_109])).
% 7.22/2.69  tff(c_584, plain, (![A_114]: (r1_tarski(k7_relat_1('#skF_4', A_114), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_579, c_120])).
% 7.22/2.69  tff(c_605, plain, (![A_114]: (r1_tarski(k7_relat_1('#skF_4', A_114), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_584])).
% 7.22/2.69  tff(c_528, plain, (![A_109]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_109)), k1_relat_1(k7_relat_1('#skF_4', A_109))) | ~v1_relat_1(k7_relat_1('#skF_4', A_109)))), inference(superposition, [status(thm), theory('equality')], [c_510, c_14])).
% 7.22/2.69  tff(c_813, plain, (![A_133]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_133)), k1_relat_1(k7_relat_1('#skF_4', A_133))))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_528])).
% 7.22/2.69  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.22/2.69  tff(c_119, plain, (![A_64, A_9, B_10]: (r1_tarski(A_64, A_9) | ~r1_tarski(A_64, k1_relat_1(k7_relat_1(B_10, A_9))) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_10, c_109])).
% 7.22/2.69  tff(c_819, plain, (![A_133]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_133)), A_133) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_813, c_119])).
% 7.22/2.69  tff(c_846, plain, (![A_133]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_133)), A_133))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_819])).
% 7.22/2.69  tff(c_121, plain, (![A_64]: (r1_tarski(A_64, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_64, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_109])).
% 7.22/2.69  tff(c_930, plain, (![D_135, B_136, C_137, A_138]: (m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(B_136, C_137))) | ~r1_tarski(k1_relat_1(D_135), B_136) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(A_138, C_137))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.22/2.69  tff(c_3381, plain, (![A_245, B_246, C_247, A_248]: (m1_subset_1(A_245, k1_zfmisc_1(k2_zfmisc_1(B_246, C_247))) | ~r1_tarski(k1_relat_1(A_245), B_246) | ~r1_tarski(A_245, k2_zfmisc_1(A_248, C_247)))), inference(resolution, [status(thm)], [c_6, c_930])).
% 7.22/2.69  tff(c_8916, plain, (![A_414, B_415]: (m1_subset_1(A_414, k1_zfmisc_1(k2_zfmisc_1(B_415, '#skF_3'))) | ~r1_tarski(k1_relat_1(A_414), B_415) | ~r1_tarski(A_414, '#skF_4'))), inference(resolution, [status(thm)], [c_121, c_3381])).
% 7.22/2.69  tff(c_390, plain, (![A_102, B_103, C_104, D_105]: (k5_relset_1(A_102, B_103, C_104, D_105)=k7_relat_1(C_104, D_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.22/2.69  tff(c_401, plain, (![D_105]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_105)=k7_relat_1('#skF_4', D_105))), inference(resolution, [status(thm)], [c_36, c_390])).
% 7.22/2.69  tff(c_34, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.22/2.69  tff(c_473, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_34])).
% 7.22/2.69  tff(c_8941, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_8916, c_473])).
% 7.22/2.69  tff(c_8969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_605, c_846, c_8941])).
% 7.22/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.69  
% 7.22/2.69  Inference rules
% 7.22/2.69  ----------------------
% 7.22/2.69  #Ref     : 0
% 7.22/2.69  #Sup     : 1980
% 7.22/2.69  #Fact    : 0
% 7.22/2.69  #Define  : 0
% 7.22/2.69  #Split   : 4
% 7.22/2.69  #Chain   : 0
% 7.22/2.69  #Close   : 0
% 7.22/2.69  
% 7.22/2.69  Ordering : KBO
% 7.22/2.69  
% 7.22/2.69  Simplification rules
% 7.22/2.69  ----------------------
% 7.22/2.69  #Subsume      : 262
% 7.22/2.69  #Demod        : 1440
% 7.22/2.69  #Tautology    : 800
% 7.22/2.69  #SimpNegUnit  : 11
% 7.22/2.69  #BackRed      : 2
% 7.22/2.69  
% 7.22/2.69  #Partial instantiations: 0
% 7.22/2.69  #Strategies tried      : 1
% 7.22/2.69  
% 7.22/2.69  Timing (in seconds)
% 7.22/2.69  ----------------------
% 7.22/2.69  Preprocessing        : 0.30
% 7.22/2.69  Parsing              : 0.16
% 7.22/2.69  CNF conversion       : 0.02
% 7.22/2.69  Main loop            : 1.58
% 7.22/2.69  Inferencing          : 0.45
% 7.22/2.69  Reduction            : 0.60
% 7.22/2.69  Demodulation         : 0.46
% 7.22/2.69  BG Simplification    : 0.05
% 7.22/2.69  Subsumption          : 0.38
% 7.22/2.69  Abstraction          : 0.07
% 7.22/2.69  MUC search           : 0.00
% 7.22/2.69  Cooper               : 0.00
% 7.22/2.69  Total                : 1.92
% 7.22/2.69  Index Insertion      : 0.00
% 7.22/2.69  Index Deletion       : 0.00
% 7.22/2.69  Index Matching       : 0.00
% 7.22/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
