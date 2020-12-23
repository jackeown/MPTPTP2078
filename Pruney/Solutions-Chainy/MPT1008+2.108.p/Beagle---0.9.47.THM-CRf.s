%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:40 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 223 expanded)
%              Number of leaves         :   48 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  127 ( 501 expanded)
%              Number of equality atoms :   67 ( 244 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_62,plain,(
    ! [A_45,B_46] : v1_relat_1(k2_zfmisc_1(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_94,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_118,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_94,c_118])).

tff(c_124,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_121])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_96,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_159,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_163,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_159])).

tff(c_299,plain,(
    ! [B_210,A_211,C_212] :
      ( k1_xboole_0 = B_210
      | k1_relset_1(A_211,B_210,C_212) = A_211
      | ~ v1_funct_2(C_212,A_211,B_210)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_302,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_299])).

tff(c_305,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_163,c_302])).

tff(c_306,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_305])).

tff(c_60,plain,(
    ! [A_42,B_44] :
      ( k9_relat_1(A_42,k1_tarski(B_44)) = k11_relat_1(A_42,B_44)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_318,plain,(
    ! [A_42] :
      ( k9_relat_1(A_42,k1_relat_1('#skF_5')) = k11_relat_1(A_42,'#skF_3')
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_60])).

tff(c_203,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k7_relset_1(A_135,B_136,C_137,D_138) = k9_relat_1(C_137,D_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_206,plain,(
    ! [D_138] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',D_138) = k9_relat_1('#skF_5',D_138) ),
    inference(resolution,[status(thm)],[c_94,c_203])).

tff(c_307,plain,(
    ! [D_138] : k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',D_138) = k9_relat_1('#skF_5',D_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_206])).

tff(c_98,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_311,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_96])).

tff(c_310,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_94])).

tff(c_437,plain,(
    ! [B_224,A_225,C_226] :
      ( k1_xboole_0 = B_224
      | k8_relset_1(A_225,B_224,C_226,B_224) = A_225
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224)))
      | ~ v1_funct_2(C_226,A_225,B_224)
      | ~ v1_funct_1(C_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_439,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_310,c_437])).

tff(c_442,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_311,c_439])).

tff(c_443,plain,(
    k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_442])).

tff(c_400,plain,(
    ! [B_218,A_219,C_220] :
      ( k7_relset_1(B_218,A_219,C_220,k8_relset_1(B_218,A_219,C_220,A_219)) = k2_relset_1(B_218,A_219,C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(B_218,A_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_403,plain,(
    k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4')) = k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_310,c_400])).

tff(c_445,plain,(
    k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',k1_relat_1('#skF_5')) = k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_403])).

tff(c_446,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') = k9_relat_1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_445])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_168,plain,(
    ! [C_121,A_122,E_125,D_124,B_123] : k4_enumset1(A_122,A_122,B_123,C_121,D_124,E_125) = k3_enumset1(A_122,B_123,C_121,D_124,E_125) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [E_33,A_29,F_34,H_38,D_32,C_31] : r2_hidden(H_38,k4_enumset1(A_29,H_38,C_31,D_32,E_33,F_34)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_195,plain,(
    ! [E_127,A_126,B_130,D_128,C_129] : r2_hidden(A_126,k3_enumset1(A_126,B_130,C_129,D_128,E_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_26])).

tff(c_199,plain,(
    ! [A_131,B_132,C_133,D_134] : r2_hidden(A_131,k2_enumset1(A_131,B_132,C_133,D_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_195])).

tff(c_207,plain,(
    ! [A_139,B_140,C_141] : r2_hidden(A_139,k1_enumset1(A_139,B_140,C_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_199])).

tff(c_211,plain,(
    ! [A_142,B_143] : r2_hidden(A_142,k2_tarski(A_142,B_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_207])).

tff(c_214,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_211])).

tff(c_315,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_214])).

tff(c_64,plain,(
    ! [B_48,A_47] :
      ( k1_tarski(k1_funct_1(B_48,A_47)) = k11_relat_1(B_48,A_47)
      | ~ r2_hidden(A_47,k1_relat_1(B_48))
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_324,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_315,c_64])).

tff(c_327,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_98,c_324])).

tff(c_90,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_309,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_90])).

tff(c_371,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_309])).

tff(c_451,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) != k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_371])).

tff(c_458,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_451])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n025.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:51:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.45  
% 3.03/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.45  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.03/1.45  
% 3.03/1.45  %Foreground sorts:
% 3.03/1.45  
% 3.03/1.45  
% 3.03/1.45  %Background operators:
% 3.03/1.45  
% 3.03/1.45  
% 3.03/1.45  %Foreground operators:
% 3.03/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.03/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.03/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.03/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.03/1.45  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.03/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.03/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.03/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.03/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.03/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.03/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.45  
% 3.16/1.47  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.16/1.47  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.16/1.47  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.16/1.47  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.47  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.16/1.47  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.16/1.47  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.16/1.47  tff(f_129, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 3.16/1.47  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.16/1.47  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.16/1.47  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.16/1.47  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.16/1.47  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.16/1.47  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.16/1.47  tff(f_63, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 3.16/1.47  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.16/1.47  tff(c_62, plain, (![A_45, B_46]: (v1_relat_1(k2_zfmisc_1(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.47  tff(c_94, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.16/1.47  tff(c_118, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.47  tff(c_121, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_94, c_118])).
% 3.16/1.47  tff(c_124, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_121])).
% 3.16/1.47  tff(c_92, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.16/1.47  tff(c_96, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.16/1.47  tff(c_159, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.16/1.47  tff(c_163, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_94, c_159])).
% 3.16/1.47  tff(c_299, plain, (![B_210, A_211, C_212]: (k1_xboole_0=B_210 | k1_relset_1(A_211, B_210, C_212)=A_211 | ~v1_funct_2(C_212, A_211, B_210) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.16/1.47  tff(c_302, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_94, c_299])).
% 3.16/1.47  tff(c_305, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_163, c_302])).
% 3.16/1.47  tff(c_306, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_305])).
% 3.16/1.47  tff(c_60, plain, (![A_42, B_44]: (k9_relat_1(A_42, k1_tarski(B_44))=k11_relat_1(A_42, B_44) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.16/1.47  tff(c_318, plain, (![A_42]: (k9_relat_1(A_42, k1_relat_1('#skF_5'))=k11_relat_1(A_42, '#skF_3') | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_306, c_60])).
% 3.16/1.47  tff(c_203, plain, (![A_135, B_136, C_137, D_138]: (k7_relset_1(A_135, B_136, C_137, D_138)=k9_relat_1(C_137, D_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.16/1.47  tff(c_206, plain, (![D_138]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', D_138)=k9_relat_1('#skF_5', D_138))), inference(resolution, [status(thm)], [c_94, c_203])).
% 3.16/1.47  tff(c_307, plain, (![D_138]: (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', D_138)=k9_relat_1('#skF_5', D_138))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_206])).
% 3.16/1.47  tff(c_98, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.16/1.47  tff(c_311, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_306, c_96])).
% 3.16/1.47  tff(c_310, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_94])).
% 3.16/1.47  tff(c_437, plain, (![B_224, A_225, C_226]: (k1_xboole_0=B_224 | k8_relset_1(A_225, B_224, C_226, B_224)=A_225 | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))) | ~v1_funct_2(C_226, A_225, B_224) | ~v1_funct_1(C_226))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.16/1.47  tff(c_439, plain, (k1_xboole_0='#skF_4' | k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_310, c_437])).
% 3.16/1.47  tff(c_442, plain, (k1_xboole_0='#skF_4' | k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_311, c_439])).
% 3.16/1.47  tff(c_443, plain, (k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_442])).
% 3.16/1.47  tff(c_400, plain, (![B_218, A_219, C_220]: (k7_relset_1(B_218, A_219, C_220, k8_relset_1(B_218, A_219, C_220, A_219))=k2_relset_1(B_218, A_219, C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(B_218, A_219))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.16/1.47  tff(c_403, plain, (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4'))=k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_310, c_400])).
% 3.16/1.47  tff(c_445, plain, (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', k1_relat_1('#skF_5'))=k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_403])).
% 3.16/1.47  tff(c_446, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')=k9_relat_1('#skF_5', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_445])).
% 3.16/1.47  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.47  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.47  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.47  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.47  tff(c_168, plain, (![C_121, A_122, E_125, D_124, B_123]: (k4_enumset1(A_122, A_122, B_123, C_121, D_124, E_125)=k3_enumset1(A_122, B_123, C_121, D_124, E_125))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.47  tff(c_26, plain, (![E_33, A_29, F_34, H_38, D_32, C_31]: (r2_hidden(H_38, k4_enumset1(A_29, H_38, C_31, D_32, E_33, F_34)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.47  tff(c_195, plain, (![E_127, A_126, B_130, D_128, C_129]: (r2_hidden(A_126, k3_enumset1(A_126, B_130, C_129, D_128, E_127)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_26])).
% 3.16/1.47  tff(c_199, plain, (![A_131, B_132, C_133, D_134]: (r2_hidden(A_131, k2_enumset1(A_131, B_132, C_133, D_134)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_195])).
% 3.16/1.47  tff(c_207, plain, (![A_139, B_140, C_141]: (r2_hidden(A_139, k1_enumset1(A_139, B_140, C_141)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_199])).
% 3.16/1.47  tff(c_211, plain, (![A_142, B_143]: (r2_hidden(A_142, k2_tarski(A_142, B_143)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_207])).
% 3.16/1.47  tff(c_214, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_211])).
% 3.16/1.47  tff(c_315, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_306, c_214])).
% 3.16/1.47  tff(c_64, plain, (![B_48, A_47]: (k1_tarski(k1_funct_1(B_48, A_47))=k11_relat_1(B_48, A_47) | ~r2_hidden(A_47, k1_relat_1(B_48)) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.47  tff(c_324, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_315, c_64])).
% 3.16/1.47  tff(c_327, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_98, c_324])).
% 3.16/1.47  tff(c_90, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.16/1.47  tff(c_309, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_90])).
% 3.16/1.47  tff(c_371, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_309])).
% 3.16/1.47  tff(c_451, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))!=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_371])).
% 3.16/1.47  tff(c_458, plain, (~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_318, c_451])).
% 3.16/1.47  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_458])).
% 3.16/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  Inference rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Ref     : 0
% 3.16/1.47  #Sup     : 86
% 3.16/1.47  #Fact    : 0
% 3.16/1.47  #Define  : 0
% 3.16/1.47  #Split   : 0
% 3.16/1.47  #Chain   : 0
% 3.16/1.47  #Close   : 0
% 3.16/1.47  
% 3.16/1.47  Ordering : KBO
% 3.16/1.47  
% 3.16/1.47  Simplification rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Subsume      : 0
% 3.16/1.47  #Demod        : 36
% 3.16/1.47  #Tautology    : 56
% 3.16/1.47  #SimpNegUnit  : 5
% 3.16/1.47  #BackRed      : 8
% 3.16/1.47  
% 3.16/1.47  #Partial instantiations: 0
% 3.16/1.47  #Strategies tried      : 1
% 3.16/1.47  
% 3.16/1.47  Timing (in seconds)
% 3.16/1.47  ----------------------
% 3.16/1.47  Preprocessing        : 0.38
% 3.16/1.47  Parsing              : 0.19
% 3.16/1.47  CNF conversion       : 0.03
% 3.16/1.47  Main loop            : 0.28
% 3.16/1.47  Inferencing          : 0.09
% 3.16/1.47  Reduction            : 0.09
% 3.16/1.47  Demodulation         : 0.06
% 3.16/1.47  BG Simplification    : 0.02
% 3.16/1.47  Subsumption          : 0.07
% 3.16/1.47  Abstraction          : 0.02
% 3.16/1.47  MUC search           : 0.00
% 3.16/1.47  Cooper               : 0.00
% 3.16/1.47  Total                : 0.70
% 3.16/1.47  Index Insertion      : 0.00
% 3.16/1.47  Index Deletion       : 0.00
% 3.16/1.47  Index Matching       : 0.00
% 3.16/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
