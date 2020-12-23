%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:15 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 129 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  152 ( 231 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_947,plain,(
    ! [A_170,B_171,C_172] :
      ( k2_relset_1(A_170,B_171,C_172) = k2_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_956,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_947])).

tff(c_564,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_573,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_564])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_574,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_73])).

tff(c_22,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_80,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_80])).

tff(c_40,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_146,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,k2_zfmisc_1(k1_relat_1(A_59),k2_relat_1(A_59)))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_155,plain,(
    ! [A_22] :
      ( r1_tarski(k6_relat_1(A_22),k2_zfmisc_1(A_22,k2_relat_1(k6_relat_1(A_22))))
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_146])).

tff(c_167,plain,(
    ! [A_60] : r1_tarski(k6_relat_1(A_60),k2_zfmisc_1(A_60,A_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28,c_155])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [C_47,B_48,A_49] :
      ( v5_relat_1(C_47,B_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_116,plain,(
    ! [A_1,B_48,A_49] :
      ( v5_relat_1(A_1,B_48)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_49,B_48)) ) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_178,plain,(
    ! [A_61] : v5_relat_1(k6_relat_1(A_61),A_61) ),
    inference(resolution,[status(thm)],[c_167,c_116])).

tff(c_98,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k2_relat_1(B_45),A_46)
      | ~ v5_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104,plain,(
    ! [A_22,A_46] :
      ( r1_tarski(A_22,A_46)
      | ~ v5_relat_1(k6_relat_1(A_22),A_46)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_107,plain,(
    ! [A_22,A_46] :
      ( r1_tarski(A_22,A_46)
      | ~ v5_relat_1(k6_relat_1(A_22),A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_182,plain,(
    ! [A_61] : r1_tarski(A_61,A_61) ),
    inference(resolution,[status(thm)],[c_178,c_107])).

tff(c_228,plain,(
    ! [B_68,A_69] :
      ( v4_relat_1(B_68,A_69)
      | ~ r1_tarski(k1_relat_1(B_68),A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_243,plain,(
    ! [B_68] :
      ( v4_relat_1(B_68,k1_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_182,c_228])).

tff(c_318,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(B_86))
      | ~ v4_relat_1(B_86,A_85)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_517,plain,(
    ! [A_110,A_111,B_112] :
      ( v4_relat_1(A_110,A_111)
      | ~ v4_relat_1(B_112,A_111)
      | ~ v1_relat_1(B_112)
      | ~ r1_tarski(A_110,B_112) ) ),
    inference(resolution,[status(thm)],[c_4,c_318])).

tff(c_605,plain,(
    ! [A_120,B_121] :
      ( v4_relat_1(A_120,k1_relat_1(B_121))
      | ~ r1_tarski(A_120,B_121)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_243,c_517])).

tff(c_130,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k1_relat_1(B_55),A_56)
      | ~ v4_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    ! [A_22,A_56] :
      ( r1_tarski(A_22,A_56)
      | ~ v4_relat_1(k6_relat_1(A_22),A_56)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_130])).

tff(c_144,plain,(
    ! [A_22,A_56] :
      ( r1_tarski(A_22,A_56)
      | ~ v4_relat_1(k6_relat_1(A_22),A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_140])).

tff(c_658,plain,(
    ! [A_126,B_127] :
      ( r1_tarski(A_126,k1_relat_1(B_127))
      | ~ r1_tarski(k6_relat_1(A_126),B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(resolution,[status(thm)],[c_605,c_144])).

tff(c_672,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_658])).

tff(c_684,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_672])).

tff(c_686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_684])).

tff(c_687,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_957,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_687])).

tff(c_689,plain,(
    ! [B_128,A_129] :
      ( v1_relat_1(B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_129))
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_695,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_689])).

tff(c_699,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_695])).

tff(c_792,plain,(
    ! [A_152] :
      ( r1_tarski(A_152,k2_zfmisc_1(k1_relat_1(A_152),k2_relat_1(A_152)))
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_766,plain,(
    ! [C_146,B_147,A_148] :
      ( v5_relat_1(C_146,B_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_774,plain,(
    ! [A_1,B_147,A_148] :
      ( v5_relat_1(A_1,B_147)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_148,B_147)) ) ),
    inference(resolution,[status(thm)],[c_4,c_766])).

tff(c_808,plain,(
    ! [A_152] :
      ( v5_relat_1(A_152,k2_relat_1(A_152))
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_792,c_774])).

tff(c_972,plain,(
    ! [C_177,A_178,B_179] :
      ( v5_relat_1(C_177,A_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(B_179))
      | ~ v5_relat_1(B_179,A_178)
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1330,plain,(
    ! [A_216,A_217,B_218] :
      ( v5_relat_1(A_216,A_217)
      | ~ v5_relat_1(B_218,A_217)
      | ~ v1_relat_1(B_218)
      | ~ r1_tarski(A_216,B_218) ) ),
    inference(resolution,[status(thm)],[c_4,c_972])).

tff(c_1427,plain,(
    ! [A_225,A_226] :
      ( v5_relat_1(A_225,k2_relat_1(A_226))
      | ~ r1_tarski(A_225,A_226)
      | ~ v1_relat_1(A_226) ) ),
    inference(resolution,[status(thm)],[c_808,c_1330])).

tff(c_700,plain,(
    ! [B_130,A_131] :
      ( r1_tarski(k2_relat_1(B_130),A_131)
      | ~ v5_relat_1(B_130,A_131)
      | ~ v1_relat_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_703,plain,(
    ! [A_22,A_131] :
      ( r1_tarski(A_22,A_131)
      | ~ v5_relat_1(k6_relat_1(A_22),A_131)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_700])).

tff(c_705,plain,(
    ! [A_22,A_131] :
      ( r1_tarski(A_22,A_131)
      | ~ v5_relat_1(k6_relat_1(A_22),A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_703])).

tff(c_1978,plain,(
    ! [A_269,A_270] :
      ( r1_tarski(A_269,k2_relat_1(A_270))
      | ~ r1_tarski(k6_relat_1(A_269),A_270)
      | ~ v1_relat_1(A_270) ) ),
    inference(resolution,[status(thm)],[c_1427,c_705])).

tff(c_1996,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1978])).

tff(c_2009,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_1996])).

tff(c_2011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_957,c_2009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.72  
% 3.51/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.73  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.51/1.73  
% 3.51/1.73  %Foreground sorts:
% 3.51/1.73  
% 3.51/1.73  
% 3.51/1.73  %Background operators:
% 3.51/1.73  
% 3.51/1.73  
% 3.51/1.73  %Foreground operators:
% 3.51/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.51/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.51/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.51/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.51/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.51/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.51/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.51/1.73  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.51/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.51/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.51/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.73  
% 3.51/1.74  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 3.51/1.74  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.51/1.74  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.51/1.74  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.51/1.74  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.51/1.74  tff(f_68, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.51/1.74  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.51/1.74  tff(f_74, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.51/1.74  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.51/1.74  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.51/1.74  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.51/1.74  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.51/1.74  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_relat_1)).
% 3.51/1.74  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 3.51/1.74  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.51/1.74  tff(c_947, plain, (![A_170, B_171, C_172]: (k2_relset_1(A_170, B_171, C_172)=k2_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.51/1.74  tff(c_956, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_947])).
% 3.51/1.74  tff(c_564, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.51/1.74  tff(c_573, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_564])).
% 3.51/1.74  tff(c_38, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.51/1.74  tff(c_73, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_38])).
% 3.51/1.74  tff(c_574, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_73])).
% 3.51/1.74  tff(c_22, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.51/1.74  tff(c_74, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.51/1.74  tff(c_80, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_74])).
% 3.51/1.74  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_80])).
% 3.51/1.74  tff(c_40, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.51/1.74  tff(c_20, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.51/1.74  tff(c_28, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.51/1.74  tff(c_26, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.51/1.74  tff(c_146, plain, (![A_59]: (r1_tarski(A_59, k2_zfmisc_1(k1_relat_1(A_59), k2_relat_1(A_59))) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.51/1.74  tff(c_155, plain, (![A_22]: (r1_tarski(k6_relat_1(A_22), k2_zfmisc_1(A_22, k2_relat_1(k6_relat_1(A_22)))) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_146])).
% 3.51/1.74  tff(c_167, plain, (![A_60]: (r1_tarski(k6_relat_1(A_60), k2_zfmisc_1(A_60, A_60)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28, c_155])).
% 3.51/1.74  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.51/1.74  tff(c_108, plain, (![C_47, B_48, A_49]: (v5_relat_1(C_47, B_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.51/1.74  tff(c_116, plain, (![A_1, B_48, A_49]: (v5_relat_1(A_1, B_48) | ~r1_tarski(A_1, k2_zfmisc_1(A_49, B_48)))), inference(resolution, [status(thm)], [c_4, c_108])).
% 3.51/1.74  tff(c_178, plain, (![A_61]: (v5_relat_1(k6_relat_1(A_61), A_61))), inference(resolution, [status(thm)], [c_167, c_116])).
% 3.51/1.74  tff(c_98, plain, (![B_45, A_46]: (r1_tarski(k2_relat_1(B_45), A_46) | ~v5_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.51/1.74  tff(c_104, plain, (![A_22, A_46]: (r1_tarski(A_22, A_46) | ~v5_relat_1(k6_relat_1(A_22), A_46) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_98])).
% 3.51/1.74  tff(c_107, plain, (![A_22, A_46]: (r1_tarski(A_22, A_46) | ~v5_relat_1(k6_relat_1(A_22), A_46))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_104])).
% 3.51/1.74  tff(c_182, plain, (![A_61]: (r1_tarski(A_61, A_61))), inference(resolution, [status(thm)], [c_178, c_107])).
% 3.51/1.74  tff(c_228, plain, (![B_68, A_69]: (v4_relat_1(B_68, A_69) | ~r1_tarski(k1_relat_1(B_68), A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.51/1.74  tff(c_243, plain, (![B_68]: (v4_relat_1(B_68, k1_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_182, c_228])).
% 3.51/1.74  tff(c_318, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(B_86)) | ~v4_relat_1(B_86, A_85) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.51/1.74  tff(c_517, plain, (![A_110, A_111, B_112]: (v4_relat_1(A_110, A_111) | ~v4_relat_1(B_112, A_111) | ~v1_relat_1(B_112) | ~r1_tarski(A_110, B_112))), inference(resolution, [status(thm)], [c_4, c_318])).
% 3.51/1.74  tff(c_605, plain, (![A_120, B_121]: (v4_relat_1(A_120, k1_relat_1(B_121)) | ~r1_tarski(A_120, B_121) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_243, c_517])).
% 3.51/1.74  tff(c_130, plain, (![B_55, A_56]: (r1_tarski(k1_relat_1(B_55), A_56) | ~v4_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.51/1.74  tff(c_140, plain, (![A_22, A_56]: (r1_tarski(A_22, A_56) | ~v4_relat_1(k6_relat_1(A_22), A_56) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_130])).
% 3.51/1.74  tff(c_144, plain, (![A_22, A_56]: (r1_tarski(A_22, A_56) | ~v4_relat_1(k6_relat_1(A_22), A_56))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_140])).
% 3.51/1.74  tff(c_658, plain, (![A_126, B_127]: (r1_tarski(A_126, k1_relat_1(B_127)) | ~r1_tarski(k6_relat_1(A_126), B_127) | ~v1_relat_1(B_127))), inference(resolution, [status(thm)], [c_605, c_144])).
% 3.51/1.74  tff(c_672, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_658])).
% 3.51/1.74  tff(c_684, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_672])).
% 3.51/1.74  tff(c_686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_574, c_684])).
% 3.51/1.74  tff(c_687, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_38])).
% 3.51/1.74  tff(c_957, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_956, c_687])).
% 3.51/1.74  tff(c_689, plain, (![B_128, A_129]: (v1_relat_1(B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(A_129)) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.51/1.74  tff(c_695, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_689])).
% 3.51/1.74  tff(c_699, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_695])).
% 3.51/1.74  tff(c_792, plain, (![A_152]: (r1_tarski(A_152, k2_zfmisc_1(k1_relat_1(A_152), k2_relat_1(A_152))) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.51/1.74  tff(c_766, plain, (![C_146, B_147, A_148]: (v5_relat_1(C_146, B_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.51/1.74  tff(c_774, plain, (![A_1, B_147, A_148]: (v5_relat_1(A_1, B_147) | ~r1_tarski(A_1, k2_zfmisc_1(A_148, B_147)))), inference(resolution, [status(thm)], [c_4, c_766])).
% 3.51/1.74  tff(c_808, plain, (![A_152]: (v5_relat_1(A_152, k2_relat_1(A_152)) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_792, c_774])).
% 3.51/1.74  tff(c_972, plain, (![C_177, A_178, B_179]: (v5_relat_1(C_177, A_178) | ~m1_subset_1(C_177, k1_zfmisc_1(B_179)) | ~v5_relat_1(B_179, A_178) | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.51/1.74  tff(c_1330, plain, (![A_216, A_217, B_218]: (v5_relat_1(A_216, A_217) | ~v5_relat_1(B_218, A_217) | ~v1_relat_1(B_218) | ~r1_tarski(A_216, B_218))), inference(resolution, [status(thm)], [c_4, c_972])).
% 3.51/1.74  tff(c_1427, plain, (![A_225, A_226]: (v5_relat_1(A_225, k2_relat_1(A_226)) | ~r1_tarski(A_225, A_226) | ~v1_relat_1(A_226))), inference(resolution, [status(thm)], [c_808, c_1330])).
% 3.51/1.74  tff(c_700, plain, (![B_130, A_131]: (r1_tarski(k2_relat_1(B_130), A_131) | ~v5_relat_1(B_130, A_131) | ~v1_relat_1(B_130))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.51/1.74  tff(c_703, plain, (![A_22, A_131]: (r1_tarski(A_22, A_131) | ~v5_relat_1(k6_relat_1(A_22), A_131) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_700])).
% 3.51/1.74  tff(c_705, plain, (![A_22, A_131]: (r1_tarski(A_22, A_131) | ~v5_relat_1(k6_relat_1(A_22), A_131))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_703])).
% 3.51/1.74  tff(c_1978, plain, (![A_269, A_270]: (r1_tarski(A_269, k2_relat_1(A_270)) | ~r1_tarski(k6_relat_1(A_269), A_270) | ~v1_relat_1(A_270))), inference(resolution, [status(thm)], [c_1427, c_705])).
% 3.51/1.74  tff(c_1996, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_1978])).
% 3.51/1.74  tff(c_2009, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_1996])).
% 3.51/1.74  tff(c_2011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_957, c_2009])).
% 3.51/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.74  
% 3.51/1.74  Inference rules
% 3.51/1.74  ----------------------
% 3.51/1.74  #Ref     : 0
% 3.51/1.74  #Sup     : 388
% 3.51/1.74  #Fact    : 0
% 3.51/1.74  #Define  : 0
% 3.51/1.74  #Split   : 8
% 3.51/1.75  #Chain   : 0
% 3.51/1.75  #Close   : 0
% 3.51/1.75  
% 3.51/1.75  Ordering : KBO
% 3.51/1.75  
% 3.51/1.75  Simplification rules
% 3.51/1.75  ----------------------
% 3.51/1.75  #Subsume      : 54
% 3.51/1.75  #Demod        : 294
% 3.51/1.75  #Tautology    : 120
% 3.51/1.75  #SimpNegUnit  : 5
% 3.51/1.75  #BackRed      : 4
% 3.51/1.75  
% 3.51/1.75  #Partial instantiations: 0
% 3.51/1.75  #Strategies tried      : 1
% 3.51/1.75  
% 3.51/1.75  Timing (in seconds)
% 3.51/1.75  ----------------------
% 3.51/1.75  Preprocessing        : 0.37
% 3.51/1.75  Parsing              : 0.20
% 3.51/1.75  CNF conversion       : 0.03
% 3.51/1.75  Main loop            : 0.55
% 3.51/1.75  Inferencing          : 0.21
% 3.51/1.75  Reduction            : 0.19
% 3.51/1.75  Demodulation         : 0.13
% 3.51/1.75  BG Simplification    : 0.02
% 3.51/1.75  Subsumption          : 0.09
% 3.51/1.75  Abstraction          : 0.03
% 3.51/1.75  MUC search           : 0.00
% 3.51/1.75  Cooper               : 0.00
% 3.51/1.75  Total                : 0.96
% 3.51/1.75  Index Insertion      : 0.00
% 3.51/1.75  Index Deletion       : 0.00
% 3.51/1.75  Index Matching       : 0.00
% 3.51/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
