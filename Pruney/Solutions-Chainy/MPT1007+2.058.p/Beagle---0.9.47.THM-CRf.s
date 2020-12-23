%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:19 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 154 expanded)
%              Number of leaves         :   59 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 264 expanded)
%              Number of equality atoms :   51 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_ordinal1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_121,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_34,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_179,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_155,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_118,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(c_68,plain,(
    ! [A_61] : k1_ordinal1(A_61) != A_61 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_347,plain,(
    ! [C_118,A_119,B_120] :
      ( v1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_360,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_347])).

tff(c_100,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_429,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_relset_1(A_137,B_138,C_139) = k2_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_442,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_429])).

tff(c_518,plain,(
    ! [A_161,B_162,C_163] :
      ( m1_subset_1(k2_relset_1(A_161,B_162,C_163),k1_zfmisc_1(B_162))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_539,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_518])).

tff(c_547,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_539])).

tff(c_40,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_551,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_547,c_40])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( k8_relat_1(A_46,B_47) = B_47
      | ~ r1_tarski(k2_relat_1(B_47),A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_554,plain,
    ( k8_relat_1('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_551,c_44])).

tff(c_557,plain,(
    k8_relat_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_554])).

tff(c_887,plain,(
    ! [C_200,A_201,B_202] :
      ( r2_hidden(k1_funct_1(C_200,A_201),B_202)
      | ~ r2_hidden(A_201,k1_relat_1(k8_relat_1(B_202,C_200)))
      | ~ v1_funct_1(C_200)
      | ~ v1_relat_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_893,plain,(
    ! [A_201] :
      ( r2_hidden(k1_funct_1('#skF_5',A_201),'#skF_4')
      | ~ r2_hidden(A_201,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_887])).

tff(c_908,plain,(
    ! [A_203] :
      ( r2_hidden(k1_funct_1('#skF_5',A_203),'#skF_4')
      | ~ r2_hidden(A_203,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_100,c_893])).

tff(c_92,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_916,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_908,c_92])).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_98,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_470,plain,(
    ! [A_146,B_147,C_148] :
      ( k1_relset_1(A_146,B_147,C_148) = k1_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_483,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_470])).

tff(c_1078,plain,(
    ! [B_227,A_228,C_229] :
      ( k1_xboole_0 = B_227
      | k1_relset_1(A_228,B_227,C_229) = A_228
      | ~ v1_funct_2(C_229,A_228,B_227)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_228,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1089,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_1078])).

tff(c_1098,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_483,c_1089])).

tff(c_1099,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1098])).

tff(c_288,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(A_110,k1_tarski(B_111)) = A_110
      | r2_hidden(B_111,A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_255,plain,(
    ! [A_105,B_106] : k3_xboole_0(k1_tarski(A_105),k2_tarski(A_105,B_106)) = k1_tarski(A_105) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_2,B_3] : k5_xboole_0(A_2,k3_xboole_0(A_2,B_3)) = k4_xboole_0(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [A_105,B_106] : k5_xboole_0(k1_tarski(A_105),k1_tarski(A_105)) = k4_xboole_0(k1_tarski(A_105),k2_tarski(A_105,B_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_6])).

tff(c_271,plain,(
    ! [A_107,B_108] : k4_xboole_0(k1_tarski(A_107),k2_tarski(A_107,B_108)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_261])).

tff(c_278,plain,(
    ! [A_6] : k4_xboole_0(k1_tarski(A_6),k1_tarski(A_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_271])).

tff(c_295,plain,(
    ! [B_111] :
      ( k1_tarski(B_111) = k1_xboole_0
      | r2_hidden(B_111,k1_tarski(B_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_278])).

tff(c_1119,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1099,c_295])).

tff(c_1156,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_1119])).

tff(c_1157,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_916,c_1156])).

tff(c_1182,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_1099])).

tff(c_66,plain,(
    ! [A_60] : k2_xboole_0(A_60,k1_tarski(A_60)) = k1_ordinal1(A_60) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1250,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k1_ordinal1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1182,c_66])).

tff(c_1262,plain,(
    k1_ordinal1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1250])).

tff(c_1264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.63  
% 3.47/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.64  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_ordinal1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.47/1.64  
% 3.47/1.64  %Foreground sorts:
% 3.47/1.64  
% 3.47/1.64  
% 3.47/1.64  %Background operators:
% 3.47/1.64  
% 3.47/1.64  
% 3.47/1.64  %Foreground operators:
% 3.47/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.47/1.64  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.47/1.64  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.47/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.47/1.64  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.47/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.64  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 3.47/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.47/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.47/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.47/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.47/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.47/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.47/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.47/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.47/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.47/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.47/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.47/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.47/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.47/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.47/1.64  
% 3.80/1.65  tff(f_121, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 3.80/1.65  tff(f_34, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.80/1.65  tff(f_179, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.80/1.65  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.80/1.65  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.80/1.65  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.80/1.65  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.80/1.65  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 3.80/1.65  tff(f_116, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_funct_1)).
% 3.80/1.65  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.80/1.65  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.80/1.65  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.80/1.65  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.80/1.65  tff(f_36, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.80/1.65  tff(f_54, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.80/1.65  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.80/1.65  tff(f_118, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.80/1.65  tff(c_68, plain, (![A_61]: (k1_ordinal1(A_61)!=A_61)), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.80/1.65  tff(c_8, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.80/1.65  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.80/1.65  tff(c_347, plain, (![C_118, A_119, B_120]: (v1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.80/1.65  tff(c_360, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_347])).
% 3.80/1.65  tff(c_100, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.80/1.65  tff(c_429, plain, (![A_137, B_138, C_139]: (k2_relset_1(A_137, B_138, C_139)=k2_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.80/1.65  tff(c_442, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_429])).
% 3.80/1.65  tff(c_518, plain, (![A_161, B_162, C_163]: (m1_subset_1(k2_relset_1(A_161, B_162, C_163), k1_zfmisc_1(B_162)) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.80/1.65  tff(c_539, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_442, c_518])).
% 3.80/1.65  tff(c_547, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_539])).
% 3.80/1.65  tff(c_40, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.80/1.65  tff(c_551, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_547, c_40])).
% 3.80/1.65  tff(c_44, plain, (![A_46, B_47]: (k8_relat_1(A_46, B_47)=B_47 | ~r1_tarski(k2_relat_1(B_47), A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.65  tff(c_554, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_551, c_44])).
% 3.80/1.65  tff(c_557, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_360, c_554])).
% 3.80/1.65  tff(c_887, plain, (![C_200, A_201, B_202]: (r2_hidden(k1_funct_1(C_200, A_201), B_202) | ~r2_hidden(A_201, k1_relat_1(k8_relat_1(B_202, C_200))) | ~v1_funct_1(C_200) | ~v1_relat_1(C_200))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.80/1.65  tff(c_893, plain, (![A_201]: (r2_hidden(k1_funct_1('#skF_5', A_201), '#skF_4') | ~r2_hidden(A_201, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_557, c_887])).
% 3.80/1.65  tff(c_908, plain, (![A_203]: (r2_hidden(k1_funct_1('#skF_5', A_203), '#skF_4') | ~r2_hidden(A_203, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_360, c_100, c_893])).
% 3.80/1.65  tff(c_92, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.80/1.65  tff(c_916, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_908, c_92])).
% 3.80/1.65  tff(c_94, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.80/1.65  tff(c_98, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.80/1.65  tff(c_470, plain, (![A_146, B_147, C_148]: (k1_relset_1(A_146, B_147, C_148)=k1_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.80/1.65  tff(c_483, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_470])).
% 3.80/1.65  tff(c_1078, plain, (![B_227, A_228, C_229]: (k1_xboole_0=B_227 | k1_relset_1(A_228, B_227, C_229)=A_228 | ~v1_funct_2(C_229, A_228, B_227) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_228, B_227))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.80/1.65  tff(c_1089, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_96, c_1078])).
% 3.80/1.65  tff(c_1098, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_483, c_1089])).
% 3.80/1.65  tff(c_1099, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_94, c_1098])).
% 3.80/1.65  tff(c_288, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k1_tarski(B_111))=A_110 | r2_hidden(B_111, A_110))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.80/1.65  tff(c_12, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.80/1.65  tff(c_10, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.80/1.65  tff(c_255, plain, (![A_105, B_106]: (k3_xboole_0(k1_tarski(A_105), k2_tarski(A_105, B_106))=k1_tarski(A_105))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.80/1.65  tff(c_6, plain, (![A_2, B_3]: (k5_xboole_0(A_2, k3_xboole_0(A_2, B_3))=k4_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.65  tff(c_261, plain, (![A_105, B_106]: (k5_xboole_0(k1_tarski(A_105), k1_tarski(A_105))=k4_xboole_0(k1_tarski(A_105), k2_tarski(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_255, c_6])).
% 3.80/1.65  tff(c_271, plain, (![A_107, B_108]: (k4_xboole_0(k1_tarski(A_107), k2_tarski(A_107, B_108))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_261])).
% 3.80/1.65  tff(c_278, plain, (![A_6]: (k4_xboole_0(k1_tarski(A_6), k1_tarski(A_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_271])).
% 3.80/1.65  tff(c_295, plain, (![B_111]: (k1_tarski(B_111)=k1_xboole_0 | r2_hidden(B_111, k1_tarski(B_111)))), inference(superposition, [status(thm), theory('equality')], [c_288, c_278])).
% 3.80/1.65  tff(c_1119, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1099, c_295])).
% 3.80/1.65  tff(c_1156, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1099, c_1119])).
% 3.80/1.65  tff(c_1157, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_916, c_1156])).
% 3.80/1.65  tff(c_1182, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1157, c_1099])).
% 3.80/1.65  tff(c_66, plain, (![A_60]: (k2_xboole_0(A_60, k1_tarski(A_60))=k1_ordinal1(A_60))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.80/1.65  tff(c_1250, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k1_ordinal1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1182, c_66])).
% 3.80/1.65  tff(c_1262, plain, (k1_ordinal1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1250])).
% 3.80/1.65  tff(c_1264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1262])).
% 3.80/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.65  
% 3.80/1.65  Inference rules
% 3.80/1.65  ----------------------
% 3.80/1.65  #Ref     : 0
% 3.80/1.65  #Sup     : 250
% 3.80/1.65  #Fact    : 0
% 3.80/1.65  #Define  : 0
% 3.80/1.65  #Split   : 4
% 3.80/1.65  #Chain   : 0
% 3.80/1.65  #Close   : 0
% 3.80/1.65  
% 3.80/1.65  Ordering : KBO
% 3.80/1.65  
% 3.80/1.65  Simplification rules
% 3.80/1.65  ----------------------
% 3.80/1.65  #Subsume      : 11
% 3.80/1.65  #Demod        : 174
% 3.80/1.65  #Tautology    : 138
% 3.80/1.65  #SimpNegUnit  : 8
% 3.80/1.65  #BackRed      : 21
% 3.80/1.65  
% 3.80/1.65  #Partial instantiations: 0
% 3.80/1.65  #Strategies tried      : 1
% 3.80/1.65  
% 3.80/1.65  Timing (in seconds)
% 3.80/1.65  ----------------------
% 3.80/1.66  Preprocessing        : 0.42
% 3.80/1.66  Parsing              : 0.23
% 3.80/1.66  CNF conversion       : 0.03
% 3.80/1.66  Main loop            : 0.43
% 3.80/1.66  Inferencing          : 0.15
% 3.80/1.66  Reduction            : 0.15
% 3.80/1.66  Demodulation         : 0.11
% 3.80/1.66  BG Simplification    : 0.03
% 3.80/1.66  Subsumption          : 0.07
% 3.80/1.66  Abstraction          : 0.02
% 3.80/1.66  MUC search           : 0.00
% 3.80/1.66  Cooper               : 0.00
% 3.80/1.66  Total                : 0.89
% 3.80/1.66  Index Insertion      : 0.00
% 3.80/1.66  Index Deletion       : 0.00
% 3.80/1.66  Index Matching       : 0.00
% 3.80/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
