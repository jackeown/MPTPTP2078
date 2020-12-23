%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:48 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 194 expanded)
%              Number of leaves         :   39 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 413 expanded)
%              Number of equality atoms :   85 ( 147 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_165,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_169,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_165])).

tff(c_38,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,A_16),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) = k1_xboole_0
      | k2_relat_1(A_18) != k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_176,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_169,c_40])).

tff(c_178,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_42,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) = k1_xboole_0
      | k1_relat_1(A_18) != k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_177,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_169,c_42])).

tff(c_179,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_177])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_243,plain,(
    ! [B_82,A_83] :
      ( k1_tarski(k1_funct_1(B_82,A_83)) = k2_relat_1(B_82)
      | k1_tarski(A_83) != k1_relat_1(B_82)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_261,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_54])).

tff(c_270,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_62,c_261])).

tff(c_291,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_218,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_222,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_218])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_353,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k1_enumset1(A_107,B_108,C_109) = D_110
      | k2_tarski(A_107,C_109) = D_110
      | k2_tarski(B_108,C_109) = D_110
      | k2_tarski(A_107,B_108) = D_110
      | k1_tarski(C_109) = D_110
      | k1_tarski(B_108) = D_110
      | k1_tarski(A_107) = D_110
      | k1_xboole_0 = D_110
      | ~ r1_tarski(D_110,k1_enumset1(A_107,B_108,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_378,plain,(
    ! [A_5,B_6,D_110] :
      ( k1_enumset1(A_5,A_5,B_6) = D_110
      | k2_tarski(A_5,B_6) = D_110
      | k2_tarski(A_5,B_6) = D_110
      | k2_tarski(A_5,A_5) = D_110
      | k1_tarski(B_6) = D_110
      | k1_tarski(A_5) = D_110
      | k1_tarski(A_5) = D_110
      | k1_xboole_0 = D_110
      | ~ r1_tarski(D_110,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_353])).

tff(c_523,plain,(
    ! [A_156,B_157,D_158] :
      ( k2_tarski(A_156,B_157) = D_158
      | k2_tarski(A_156,B_157) = D_158
      | k2_tarski(A_156,B_157) = D_158
      | k1_tarski(A_156) = D_158
      | k1_tarski(B_157) = D_158
      | k1_tarski(A_156) = D_158
      | k1_tarski(A_156) = D_158
      | k1_xboole_0 = D_158
      | ~ r1_tarski(D_158,k2_tarski(A_156,B_157)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_378])).

tff(c_563,plain,(
    ! [A_159,B_160,B_161] :
      ( k2_tarski(A_159,B_160) = k1_relat_1(B_161)
      | k1_tarski(B_160) = k1_relat_1(B_161)
      | k1_tarski(A_159) = k1_relat_1(B_161)
      | k1_relat_1(B_161) = k1_xboole_0
      | ~ v4_relat_1(B_161,k2_tarski(A_159,B_160))
      | ~ v1_relat_1(B_161) ) ),
    inference(resolution,[status(thm)],[c_36,c_523])).

tff(c_566,plain,(
    ! [A_4,B_161] :
      ( k2_tarski(A_4,A_4) = k1_relat_1(B_161)
      | k1_tarski(A_4) = k1_relat_1(B_161)
      | k1_tarski(A_4) = k1_relat_1(B_161)
      | k1_relat_1(B_161) = k1_xboole_0
      | ~ v4_relat_1(B_161,k1_tarski(A_4))
      | ~ v1_relat_1(B_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_563])).

tff(c_568,plain,(
    ! [A_162,B_163] :
      ( k1_tarski(A_162) = k1_relat_1(B_163)
      | k1_tarski(A_162) = k1_relat_1(B_163)
      | k1_tarski(A_162) = k1_relat_1(B_163)
      | k1_relat_1(B_163) = k1_xboole_0
      | ~ v4_relat_1(B_163,k1_tarski(A_162))
      | ~ v1_relat_1(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_566])).

tff(c_574,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_222,c_568])).

tff(c_577,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_574])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_291,c_577])).

tff(c_581,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_584,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_58])).

tff(c_52,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k7_relset_1(A_27,B_28,C_29,D_30) = k9_relat_1(C_29,D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_667,plain,(
    ! [D_30] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_30) = k9_relat_1('#skF_4',D_30) ),
    inference(resolution,[status(thm)],[c_584,c_52])).

tff(c_580,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_742,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_580])).

tff(c_813,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_742])).

tff(c_826,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_813])).

tff(c_830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_826])).

tff(c_831,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_838,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_177])).

tff(c_842,plain,(
    ! [A_16] :
      ( r1_tarski(k9_relat_1('#skF_4',A_16),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_38])).

tff(c_849,plain,(
    ! [A_189] : r1_tarski(k9_relat_1('#skF_4',A_189),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_842])).

tff(c_118,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_855,plain,(
    ! [A_189] : k9_relat_1('#skF_4',A_189) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_849,c_145])).

tff(c_1001,plain,(
    ! [A_217,B_218,C_219,D_220] :
      ( k7_relset_1(A_217,B_218,C_219,D_220) = k9_relat_1(C_219,D_220)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1003,plain,(
    ! [D_220] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_220) = k9_relat_1('#skF_4',D_220) ),
    inference(resolution,[status(thm)],[c_58,c_1001])).

tff(c_1005,plain,(
    ! [D_220] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_220) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_1003])).

tff(c_1006,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1005,c_54])).

tff(c_1009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.60  
% 3.72/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.60  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.72/1.60  
% 3.72/1.60  %Foreground sorts:
% 3.72/1.60  
% 3.72/1.60  
% 3.72/1.60  %Background operators:
% 3.72/1.60  
% 3.72/1.60  
% 3.72/1.60  %Foreground operators:
% 3.72/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.72/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.72/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.72/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.72/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.72/1.60  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.72/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.72/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.72/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.72/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.72/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.72/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.72/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.72/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.72/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.72/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.72/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.72/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.72/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.72/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.60  
% 3.72/1.62  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.72/1.62  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.72/1.62  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.72/1.62  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.72/1.62  tff(f_82, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.72/1.62  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.72/1.62  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.72/1.62  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.72/1.62  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.72/1.62  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.72/1.62  tff(f_66, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.72/1.62  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.72/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.72/1.62  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.72/1.62  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.72/1.62  tff(c_165, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.72/1.62  tff(c_169, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_165])).
% 3.72/1.62  tff(c_38, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.72/1.62  tff(c_40, plain, (![A_18]: (k1_relat_1(A_18)=k1_xboole_0 | k2_relat_1(A_18)!=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.72/1.62  tff(c_176, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_169, c_40])).
% 3.72/1.62  tff(c_178, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_176])).
% 3.72/1.62  tff(c_42, plain, (![A_18]: (k2_relat_1(A_18)=k1_xboole_0 | k1_relat_1(A_18)!=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.72/1.62  tff(c_177, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_169, c_42])).
% 3.72/1.62  tff(c_179, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_178, c_177])).
% 3.72/1.62  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.72/1.62  tff(c_243, plain, (![B_82, A_83]: (k1_tarski(k1_funct_1(B_82, A_83))=k2_relat_1(B_82) | k1_tarski(A_83)!=k1_relat_1(B_82) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.72/1.62  tff(c_54, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.72/1.62  tff(c_261, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_243, c_54])).
% 3.72/1.62  tff(c_270, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_62, c_261])).
% 3.72/1.62  tff(c_291, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_270])).
% 3.72/1.62  tff(c_218, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.72/1.62  tff(c_222, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_218])).
% 3.72/1.62  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.72/1.62  tff(c_36, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.72/1.62  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.72/1.62  tff(c_353, plain, (![A_107, B_108, C_109, D_110]: (k1_enumset1(A_107, B_108, C_109)=D_110 | k2_tarski(A_107, C_109)=D_110 | k2_tarski(B_108, C_109)=D_110 | k2_tarski(A_107, B_108)=D_110 | k1_tarski(C_109)=D_110 | k1_tarski(B_108)=D_110 | k1_tarski(A_107)=D_110 | k1_xboole_0=D_110 | ~r1_tarski(D_110, k1_enumset1(A_107, B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.72/1.62  tff(c_378, plain, (![A_5, B_6, D_110]: (k1_enumset1(A_5, A_5, B_6)=D_110 | k2_tarski(A_5, B_6)=D_110 | k2_tarski(A_5, B_6)=D_110 | k2_tarski(A_5, A_5)=D_110 | k1_tarski(B_6)=D_110 | k1_tarski(A_5)=D_110 | k1_tarski(A_5)=D_110 | k1_xboole_0=D_110 | ~r1_tarski(D_110, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_353])).
% 3.72/1.62  tff(c_523, plain, (![A_156, B_157, D_158]: (k2_tarski(A_156, B_157)=D_158 | k2_tarski(A_156, B_157)=D_158 | k2_tarski(A_156, B_157)=D_158 | k1_tarski(A_156)=D_158 | k1_tarski(B_157)=D_158 | k1_tarski(A_156)=D_158 | k1_tarski(A_156)=D_158 | k1_xboole_0=D_158 | ~r1_tarski(D_158, k2_tarski(A_156, B_157)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_378])).
% 3.72/1.62  tff(c_563, plain, (![A_159, B_160, B_161]: (k2_tarski(A_159, B_160)=k1_relat_1(B_161) | k1_tarski(B_160)=k1_relat_1(B_161) | k1_tarski(A_159)=k1_relat_1(B_161) | k1_relat_1(B_161)=k1_xboole_0 | ~v4_relat_1(B_161, k2_tarski(A_159, B_160)) | ~v1_relat_1(B_161))), inference(resolution, [status(thm)], [c_36, c_523])).
% 3.72/1.62  tff(c_566, plain, (![A_4, B_161]: (k2_tarski(A_4, A_4)=k1_relat_1(B_161) | k1_tarski(A_4)=k1_relat_1(B_161) | k1_tarski(A_4)=k1_relat_1(B_161) | k1_relat_1(B_161)=k1_xboole_0 | ~v4_relat_1(B_161, k1_tarski(A_4)) | ~v1_relat_1(B_161))), inference(superposition, [status(thm), theory('equality')], [c_10, c_563])).
% 3.72/1.62  tff(c_568, plain, (![A_162, B_163]: (k1_tarski(A_162)=k1_relat_1(B_163) | k1_tarski(A_162)=k1_relat_1(B_163) | k1_tarski(A_162)=k1_relat_1(B_163) | k1_relat_1(B_163)=k1_xboole_0 | ~v4_relat_1(B_163, k1_tarski(A_162)) | ~v1_relat_1(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_566])).
% 3.72/1.62  tff(c_574, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_222, c_568])).
% 3.72/1.62  tff(c_577, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_169, c_574])).
% 3.72/1.62  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_291, c_577])).
% 3.72/1.62  tff(c_581, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_270])).
% 3.72/1.62  tff(c_584, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_58])).
% 3.72/1.62  tff(c_52, plain, (![A_27, B_28, C_29, D_30]: (k7_relset_1(A_27, B_28, C_29, D_30)=k9_relat_1(C_29, D_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.72/1.62  tff(c_667, plain, (![D_30]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_30)=k9_relat_1('#skF_4', D_30))), inference(resolution, [status(thm)], [c_584, c_52])).
% 3.72/1.62  tff(c_580, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_270])).
% 3.72/1.62  tff(c_742, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_580])).
% 3.72/1.62  tff(c_813, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_667, c_742])).
% 3.72/1.62  tff(c_826, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_813])).
% 3.72/1.62  tff(c_830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_826])).
% 3.72/1.62  tff(c_831, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_176])).
% 3.72/1.62  tff(c_838, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_831, c_177])).
% 3.72/1.62  tff(c_842, plain, (![A_16]: (r1_tarski(k9_relat_1('#skF_4', A_16), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_838, c_38])).
% 3.72/1.62  tff(c_849, plain, (![A_189]: (r1_tarski(k9_relat_1('#skF_4', A_189), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_842])).
% 3.72/1.62  tff(c_118, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.72/1.62  tff(c_145, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_118])).
% 3.72/1.62  tff(c_855, plain, (![A_189]: (k9_relat_1('#skF_4', A_189)=k1_xboole_0)), inference(resolution, [status(thm)], [c_849, c_145])).
% 3.72/1.62  tff(c_1001, plain, (![A_217, B_218, C_219, D_220]: (k7_relset_1(A_217, B_218, C_219, D_220)=k9_relat_1(C_219, D_220) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.72/1.62  tff(c_1003, plain, (![D_220]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_220)=k9_relat_1('#skF_4', D_220))), inference(resolution, [status(thm)], [c_58, c_1001])).
% 3.72/1.62  tff(c_1005, plain, (![D_220]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_220)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_855, c_1003])).
% 3.72/1.62  tff(c_1006, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1005, c_54])).
% 3.72/1.62  tff(c_1009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1006])).
% 3.72/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.62  
% 3.72/1.62  Inference rules
% 3.72/1.62  ----------------------
% 3.72/1.62  #Ref     : 0
% 3.72/1.62  #Sup     : 200
% 3.72/1.62  #Fact    : 0
% 3.72/1.62  #Define  : 0
% 3.72/1.62  #Split   : 3
% 3.72/1.62  #Chain   : 0
% 3.72/1.62  #Close   : 0
% 3.72/1.62  
% 3.72/1.62  Ordering : KBO
% 3.72/1.62  
% 3.72/1.62  Simplification rules
% 3.72/1.62  ----------------------
% 3.72/1.62  #Subsume      : 23
% 3.72/1.62  #Demod        : 124
% 3.72/1.62  #Tautology    : 97
% 3.72/1.62  #SimpNegUnit  : 5
% 3.72/1.62  #BackRed      : 9
% 3.72/1.62  
% 3.72/1.62  #Partial instantiations: 0
% 3.72/1.62  #Strategies tried      : 1
% 3.72/1.62  
% 3.72/1.62  Timing (in seconds)
% 3.72/1.62  ----------------------
% 3.72/1.63  Preprocessing        : 0.35
% 3.72/1.63  Parsing              : 0.19
% 3.72/1.63  CNF conversion       : 0.02
% 3.72/1.63  Main loop            : 0.50
% 3.72/1.63  Inferencing          : 0.18
% 3.72/1.63  Reduction            : 0.16
% 3.72/1.63  Demodulation         : 0.11
% 3.72/1.63  BG Simplification    : 0.03
% 3.72/1.63  Subsumption          : 0.10
% 3.72/1.63  Abstraction          : 0.03
% 3.72/1.63  MUC search           : 0.00
% 3.72/1.63  Cooper               : 0.00
% 3.72/1.63  Total                : 0.89
% 3.72/1.63  Index Insertion      : 0.00
% 3.72/1.63  Index Deletion       : 0.00
% 3.72/1.63  Index Matching       : 0.00
% 3.72/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
