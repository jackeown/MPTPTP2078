%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:59 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 375 expanded)
%              Number of leaves         :   48 ( 147 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 ( 764 expanded)
%              Number of equality atoms :   48 ( 166 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_99,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(c_44,plain,(
    ! [A_42,B_43] : v1_relat_1(k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_198,plain,(
    ! [B_81,A_82] :
      ( v1_relat_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_201,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_198])).

tff(c_204,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_201])).

tff(c_46,plain,(
    ! [B_45,A_44] :
      ( r1_tarski(k9_relat_1(B_45,A_44),k2_relat_1(B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_240,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_250,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_240])).

tff(c_52,plain,(
    ! [B_52,A_51] :
      ( k7_relat_1(B_52,A_51) = B_52
      | ~ v4_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_253,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_250,c_52])).

tff(c_256,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_253])).

tff(c_390,plain,(
    ! [C_111,A_112,B_113] :
      ( k7_relat_1(k7_relat_1(C_111,A_112),B_113) = k1_xboole_0
      | ~ r1_xboole_0(A_112,B_113)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_422,plain,(
    ! [B_113] :
      ( k7_relat_1('#skF_4',B_113) = k1_xboole_0
      | ~ r1_xboole_0(k1_tarski('#skF_1'),B_113)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_390])).

tff(c_432,plain,(
    ! [B_114] :
      ( k7_relat_1('#skF_4',B_114) = k1_xboole_0
      | ~ r1_xboole_0(k1_tarski('#skF_1'),B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_422])).

tff(c_437,plain,(
    k7_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_432])).

tff(c_297,plain,(
    ! [B_105,A_106] :
      ( r1_tarski(k1_relat_1(B_105),A_106)
      | ~ v4_relat_1(B_105,A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [B_34,A_33] :
      ( k1_tarski(B_34) = A_33
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,k1_tarski(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_684,plain,(
    ! [B_139,B_140] :
      ( k1_tarski(B_139) = k1_relat_1(B_140)
      | k1_relat_1(B_140) = k1_xboole_0
      | ~ v4_relat_1(B_140,k1_tarski(B_139))
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_297,c_26])).

tff(c_694,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_250,c_684])).

tff(c_700,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_694])).

tff(c_701,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_700])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_262,plain,(
    ! [B_100,A_101] :
      ( v4_relat_1(B_100,A_101)
      | ~ r1_tarski(k1_relat_1(B_100),A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_287,plain,(
    ! [B_104] :
      ( v4_relat_1(B_104,k1_relat_1(B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_6,c_262])).

tff(c_294,plain,(
    ! [B_104] :
      ( k7_relat_1(B_104,k1_relat_1(B_104)) = B_104
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_287,c_52])).

tff(c_714,plain,
    ( k7_relat_1('#skF_4',k1_xboole_0) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_294])).

tff(c_733,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_437,c_714])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_763,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_8])).

tff(c_90,plain,(
    ! [B_67] : k2_zfmisc_1(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_44])).

tff(c_54,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_146,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(k9_relat_1(B_74,A_75),k2_relat_1(B_74))
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_149,plain,(
    ! [A_75] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_75),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_146])).

tff(c_151,plain,(
    ! [A_75] : r1_tarski(k9_relat_1(k1_xboole_0,A_75),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_149])).

tff(c_153,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ r1_tarski(B_77,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [A_75] :
      ( k9_relat_1(k1_xboole_0,A_75) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,A_75)) ) ),
    inference(resolution,[status(thm)],[c_151,c_153])).

tff(c_164,plain,(
    ! [A_75] : k9_relat_1(k1_xboole_0,A_75) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_155])).

tff(c_758,plain,(
    ! [A_75] : k9_relat_1('#skF_4',A_75) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_733,c_164])).

tff(c_773,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k7_relset_1(A_141,B_142,C_143,D_144) = k9_relat_1(C_143,D_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_776,plain,(
    ! [D_144] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_144) = k9_relat_1('#skF_4',D_144) ),
    inference(resolution,[status(thm)],[c_70,c_773])).

tff(c_66,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_827,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_66])).

tff(c_953,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_827])).

tff(c_957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_953])).

tff(c_958,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_700])).

tff(c_58,plain,(
    ! [B_54,A_53] :
      ( k1_tarski(k1_funct_1(B_54,A_53)) = k2_relat_1(B_54)
      | k1_tarski(A_53) != k1_relat_1(B_54)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_960,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k7_relset_1(A_158,B_159,C_160,D_161) = k9_relat_1(C_160,D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_967,plain,(
    ! [D_161] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_161) = k9_relat_1('#skF_4',D_161) ),
    inference(resolution,[status(thm)],[c_70,c_960])).

tff(c_1082,plain,(
    ! [D_161] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_161) = k9_relat_1('#skF_4',D_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_967])).

tff(c_972,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_66])).

tff(c_1092,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_972])).

tff(c_1095,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1092])).

tff(c_1097,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_74,c_958,c_1095])).

tff(c_1100,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1097])).

tff(c_1104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_1100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:34:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.56  
% 3.05/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.05/1.56  
% 3.05/1.56  %Foreground sorts:
% 3.05/1.56  
% 3.05/1.56  
% 3.05/1.56  %Background operators:
% 3.05/1.56  
% 3.05/1.56  
% 3.05/1.56  %Foreground operators:
% 3.05/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.05/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.05/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.05/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.05/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.05/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.05/1.56  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.05/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.05/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.05/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.05/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.05/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.05/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.05/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.05/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.05/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.05/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.05/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.56  
% 3.46/1.58  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.46/1.58  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.46/1.58  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.46/1.58  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.46/1.58  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.46/1.58  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.46/1.58  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.46/1.58  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 3.46/1.58  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.46/1.58  tff(f_55, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.46/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.46/1.58  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.46/1.58  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.46/1.58  tff(f_99, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.46/1.58  tff(f_117, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.46/1.58  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.46/1.58  tff(c_44, plain, (![A_42, B_43]: (v1_relat_1(k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.46/1.58  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.46/1.58  tff(c_198, plain, (![B_81, A_82]: (v1_relat_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.46/1.58  tff(c_201, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_198])).
% 3.46/1.58  tff(c_204, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_201])).
% 3.46/1.58  tff(c_46, plain, (![B_45, A_44]: (r1_tarski(k9_relat_1(B_45, A_44), k2_relat_1(B_45)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.46/1.58  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.46/1.58  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.58  tff(c_240, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.46/1.58  tff(c_250, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_240])).
% 3.46/1.58  tff(c_52, plain, (![B_52, A_51]: (k7_relat_1(B_52, A_51)=B_52 | ~v4_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.46/1.58  tff(c_253, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_250, c_52])).
% 3.46/1.58  tff(c_256, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_253])).
% 3.46/1.58  tff(c_390, plain, (![C_111, A_112, B_113]: (k7_relat_1(k7_relat_1(C_111, A_112), B_113)=k1_xboole_0 | ~r1_xboole_0(A_112, B_113) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.46/1.58  tff(c_422, plain, (![B_113]: (k7_relat_1('#skF_4', B_113)=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_1'), B_113) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_256, c_390])).
% 3.46/1.58  tff(c_432, plain, (![B_114]: (k7_relat_1('#skF_4', B_114)=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_1'), B_114))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_422])).
% 3.46/1.58  tff(c_437, plain, (k7_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_432])).
% 3.46/1.58  tff(c_297, plain, (![B_105, A_106]: (r1_tarski(k1_relat_1(B_105), A_106) | ~v4_relat_1(B_105, A_106) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.46/1.58  tff(c_26, plain, (![B_34, A_33]: (k1_tarski(B_34)=A_33 | k1_xboole_0=A_33 | ~r1_tarski(A_33, k1_tarski(B_34)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.46/1.58  tff(c_684, plain, (![B_139, B_140]: (k1_tarski(B_139)=k1_relat_1(B_140) | k1_relat_1(B_140)=k1_xboole_0 | ~v4_relat_1(B_140, k1_tarski(B_139)) | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_297, c_26])).
% 3.46/1.58  tff(c_694, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_250, c_684])).
% 3.46/1.58  tff(c_700, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_204, c_694])).
% 3.46/1.58  tff(c_701, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_700])).
% 3.46/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.58  tff(c_262, plain, (![B_100, A_101]: (v4_relat_1(B_100, A_101) | ~r1_tarski(k1_relat_1(B_100), A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.46/1.58  tff(c_287, plain, (![B_104]: (v4_relat_1(B_104, k1_relat_1(B_104)) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_6, c_262])).
% 3.46/1.58  tff(c_294, plain, (![B_104]: (k7_relat_1(B_104, k1_relat_1(B_104))=B_104 | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_287, c_52])).
% 3.46/1.58  tff(c_714, plain, (k7_relat_1('#skF_4', k1_xboole_0)='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_701, c_294])).
% 3.46/1.58  tff(c_733, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_437, c_714])).
% 3.46/1.58  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.46/1.58  tff(c_763, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_733, c_8])).
% 3.46/1.58  tff(c_90, plain, (![B_67]: (k2_zfmisc_1(k1_xboole_0, B_67)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.46/1.58  tff(c_94, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_44])).
% 3.46/1.58  tff(c_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.46/1.58  tff(c_146, plain, (![B_74, A_75]: (r1_tarski(k9_relat_1(B_74, A_75), k2_relat_1(B_74)) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.46/1.58  tff(c_149, plain, (![A_75]: (r1_tarski(k9_relat_1(k1_xboole_0, A_75), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_146])).
% 3.46/1.58  tff(c_151, plain, (![A_75]: (r1_tarski(k9_relat_1(k1_xboole_0, A_75), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_149])).
% 3.46/1.58  tff(c_153, plain, (![B_77, A_78]: (B_77=A_78 | ~r1_tarski(B_77, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.58  tff(c_155, plain, (![A_75]: (k9_relat_1(k1_xboole_0, A_75)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1(k1_xboole_0, A_75)))), inference(resolution, [status(thm)], [c_151, c_153])).
% 3.46/1.58  tff(c_164, plain, (![A_75]: (k9_relat_1(k1_xboole_0, A_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_155])).
% 3.46/1.58  tff(c_758, plain, (![A_75]: (k9_relat_1('#skF_4', A_75)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_733, c_733, c_164])).
% 3.46/1.58  tff(c_773, plain, (![A_141, B_142, C_143, D_144]: (k7_relset_1(A_141, B_142, C_143, D_144)=k9_relat_1(C_143, D_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.46/1.58  tff(c_776, plain, (![D_144]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_144)=k9_relat_1('#skF_4', D_144))), inference(resolution, [status(thm)], [c_70, c_773])).
% 3.46/1.58  tff(c_66, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.46/1.58  tff(c_827, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_776, c_66])).
% 3.46/1.58  tff(c_953, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_758, c_827])).
% 3.46/1.58  tff(c_957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_763, c_953])).
% 3.46/1.58  tff(c_958, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_700])).
% 3.46/1.58  tff(c_58, plain, (![B_54, A_53]: (k1_tarski(k1_funct_1(B_54, A_53))=k2_relat_1(B_54) | k1_tarski(A_53)!=k1_relat_1(B_54) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.46/1.58  tff(c_960, plain, (![A_158, B_159, C_160, D_161]: (k7_relset_1(A_158, B_159, C_160, D_161)=k9_relat_1(C_160, D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.46/1.58  tff(c_967, plain, (![D_161]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_161)=k9_relat_1('#skF_4', D_161))), inference(resolution, [status(thm)], [c_70, c_960])).
% 3.46/1.58  tff(c_1082, plain, (![D_161]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_161)=k9_relat_1('#skF_4', D_161))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_967])).
% 3.46/1.58  tff(c_972, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_66])).
% 3.46/1.58  tff(c_1092, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_972])).
% 3.46/1.58  tff(c_1095, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_58, c_1092])).
% 3.46/1.58  tff(c_1097, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_74, c_958, c_1095])).
% 3.46/1.58  tff(c_1100, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1097])).
% 3.46/1.58  tff(c_1104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_1100])).
% 3.46/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.58  
% 3.46/1.58  Inference rules
% 3.46/1.58  ----------------------
% 3.46/1.58  #Ref     : 0
% 3.46/1.58  #Sup     : 221
% 3.46/1.58  #Fact    : 0
% 3.46/1.58  #Define  : 0
% 3.46/1.58  #Split   : 1
% 3.46/1.58  #Chain   : 0
% 3.46/1.58  #Close   : 0
% 3.46/1.58  
% 3.46/1.58  Ordering : KBO
% 3.46/1.58  
% 3.46/1.58  Simplification rules
% 3.46/1.58  ----------------------
% 3.46/1.58  #Subsume      : 10
% 3.46/1.58  #Demod        : 239
% 3.46/1.58  #Tautology    : 156
% 3.46/1.58  #SimpNegUnit  : 0
% 3.46/1.58  #BackRed      : 39
% 3.46/1.58  
% 3.46/1.58  #Partial instantiations: 0
% 3.46/1.58  #Strategies tried      : 1
% 3.46/1.58  
% 3.46/1.58  Timing (in seconds)
% 3.46/1.58  ----------------------
% 3.46/1.58  Preprocessing        : 0.38
% 3.46/1.58  Parsing              : 0.20
% 3.46/1.58  CNF conversion       : 0.03
% 3.46/1.58  Main loop            : 0.37
% 3.46/1.58  Inferencing          : 0.12
% 3.46/1.58  Reduction            : 0.13
% 3.46/1.58  Demodulation         : 0.10
% 3.46/1.58  BG Simplification    : 0.02
% 3.46/1.58  Subsumption          : 0.06
% 3.46/1.58  Abstraction          : 0.02
% 3.46/1.58  MUC search           : 0.00
% 3.46/1.58  Cooper               : 0.00
% 3.46/1.58  Total                : 0.78
% 3.46/1.58  Index Insertion      : 0.00
% 3.46/1.58  Index Deletion       : 0.00
% 3.46/1.58  Index Matching       : 0.00
% 3.46/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
