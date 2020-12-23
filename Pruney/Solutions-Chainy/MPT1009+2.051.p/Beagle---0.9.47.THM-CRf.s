%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:49 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 245 expanded)
%              Number of leaves         :   44 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 500 expanded)
%              Number of equality atoms :   63 ( 166 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_161,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_169,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_161])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,A_17),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_184,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_169,c_40])).

tff(c_187,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_315,plain,(
    ! [B_88,A_89] :
      ( k1_tarski(k1_funct_1(B_88,A_89)) = k2_relat_1(B_88)
      | k1_tarski(A_89) != k1_relat_1(B_88)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_321,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_58])).

tff(c_339,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_66,c_321])).

tff(c_341,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_229,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_237,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_229])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_373,plain,(
    ! [B_98,C_99,A_100] :
      ( k2_tarski(B_98,C_99) = A_100
      | k1_tarski(C_99) = A_100
      | k1_tarski(B_98) = A_100
      | k1_xboole_0 = A_100
      | ~ r1_tarski(A_100,k2_tarski(B_98,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_389,plain,(
    ! [A_2,A_100] :
      ( k2_tarski(A_2,A_2) = A_100
      | k1_tarski(A_2) = A_100
      | k1_tarski(A_2) = A_100
      | k1_xboole_0 = A_100
      | ~ r1_tarski(A_100,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_373])).

tff(c_430,plain,(
    ! [A_105,A_106] :
      ( k1_tarski(A_105) = A_106
      | k1_tarski(A_105) = A_106
      | k1_tarski(A_105) = A_106
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,k1_tarski(A_105)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_389])).

tff(c_450,plain,(
    ! [A_107,B_108] :
      ( k1_tarski(A_107) = k1_relat_1(B_108)
      | k1_relat_1(B_108) = k1_xboole_0
      | ~ v4_relat_1(B_108,k1_tarski(A_107))
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_26,c_430])).

tff(c_456,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_237,c_450])).

tff(c_463,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_456])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_341,c_463])).

tff(c_467,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_468,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k7_relset_1(A_109,B_110,C_111,D_112) = k9_relat_1(C_111,D_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_474,plain,(
    ! [D_112] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_112) = k9_relat_1('#skF_4',D_112) ),
    inference(resolution,[status(thm)],[c_62,c_468])).

tff(c_637,plain,(
    ! [D_112] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_112) = k9_relat_1('#skF_4',D_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_474])).

tff(c_466,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_706,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_467,c_466])).

tff(c_709,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_706])).

tff(c_713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_709])).

tff(c_714,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_725,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_2])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_726,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_714,c_34])).

tff(c_715,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_746,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_715])).

tff(c_770,plain,(
    ! [B_128,A_129] :
      ( v4_relat_1(B_128,A_129)
      | ~ r1_tarski(k1_relat_1(B_128),A_129)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_773,plain,(
    ! [A_129] :
      ( v4_relat_1('#skF_4',A_129)
      | ~ r1_tarski('#skF_4',A_129)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_770])).

tff(c_775,plain,(
    ! [A_129] : v4_relat_1('#skF_4',A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_725,c_773])).

tff(c_849,plain,(
    ! [B_147,A_148] :
      ( k7_relat_1(B_147,A_148) = B_147
      | ~ v4_relat_1(B_147,A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_852,plain,(
    ! [A_129] :
      ( k7_relat_1('#skF_4',A_129) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_775,c_849])).

tff(c_857,plain,(
    ! [A_150] : k7_relat_1('#skF_4',A_150) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_852])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_862,plain,(
    ! [A_150] :
      ( k9_relat_1('#skF_4',A_150) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_30])).

tff(c_867,plain,(
    ! [A_150] : k9_relat_1('#skF_4',A_150) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_726,c_862])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_721,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_20])).

tff(c_925,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k7_relset_1(A_161,B_162,C_163,D_164) = k9_relat_1(C_163,D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_928,plain,(
    ! [A_161,B_162,D_164] : k7_relset_1(A_161,B_162,'#skF_4',D_164) = k9_relat_1('#skF_4',D_164) ),
    inference(resolution,[status(thm)],[c_721,c_925])).

tff(c_930,plain,(
    ! [A_161,B_162,D_164] : k7_relset_1(A_161,B_162,'#skF_4',D_164) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_928])).

tff(c_931,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_58])).

tff(c_934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_931])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.44  
% 2.79/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.45  
% 2.79/1.45  %Foreground sorts:
% 2.79/1.45  
% 2.79/1.45  
% 2.79/1.45  %Background operators:
% 2.79/1.45  
% 2.79/1.45  
% 2.79/1.45  %Foreground operators:
% 2.79/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.79/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.79/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.79/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.79/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.79/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.79/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.79/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.45  
% 3.20/1.46  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.20/1.46  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.20/1.46  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.20/1.46  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.20/1.46  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.20/1.46  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.20/1.46  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.20/1.46  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.20/1.46  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.20/1.46  tff(f_114, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.20/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.46  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.20/1.46  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.20/1.46  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.20/1.46  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.20/1.46  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.20/1.46  tff(c_161, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.46  tff(c_169, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_161])).
% 3.20/1.46  tff(c_28, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, A_17), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.20/1.46  tff(c_40, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.20/1.46  tff(c_184, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_169, c_40])).
% 3.20/1.46  tff(c_187, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_184])).
% 3.20/1.46  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.20/1.46  tff(c_315, plain, (![B_88, A_89]: (k1_tarski(k1_funct_1(B_88, A_89))=k2_relat_1(B_88) | k1_tarski(A_89)!=k1_relat_1(B_88) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.20/1.46  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.20/1.46  tff(c_321, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_315, c_58])).
% 3.20/1.46  tff(c_339, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_66, c_321])).
% 3.20/1.46  tff(c_341, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_339])).
% 3.20/1.46  tff(c_229, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.20/1.46  tff(c_237, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_229])).
% 3.20/1.46  tff(c_26, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.20/1.46  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.46  tff(c_373, plain, (![B_98, C_99, A_100]: (k2_tarski(B_98, C_99)=A_100 | k1_tarski(C_99)=A_100 | k1_tarski(B_98)=A_100 | k1_xboole_0=A_100 | ~r1_tarski(A_100, k2_tarski(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.20/1.46  tff(c_389, plain, (![A_2, A_100]: (k2_tarski(A_2, A_2)=A_100 | k1_tarski(A_2)=A_100 | k1_tarski(A_2)=A_100 | k1_xboole_0=A_100 | ~r1_tarski(A_100, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_373])).
% 3.20/1.46  tff(c_430, plain, (![A_105, A_106]: (k1_tarski(A_105)=A_106 | k1_tarski(A_105)=A_106 | k1_tarski(A_105)=A_106 | k1_xboole_0=A_106 | ~r1_tarski(A_106, k1_tarski(A_105)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_389])).
% 3.20/1.46  tff(c_450, plain, (![A_107, B_108]: (k1_tarski(A_107)=k1_relat_1(B_108) | k1_relat_1(B_108)=k1_xboole_0 | ~v4_relat_1(B_108, k1_tarski(A_107)) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_26, c_430])).
% 3.20/1.46  tff(c_456, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_237, c_450])).
% 3.20/1.46  tff(c_463, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_169, c_456])).
% 3.20/1.46  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_341, c_463])).
% 3.20/1.46  tff(c_467, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_339])).
% 3.20/1.46  tff(c_468, plain, (![A_109, B_110, C_111, D_112]: (k7_relset_1(A_109, B_110, C_111, D_112)=k9_relat_1(C_111, D_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.20/1.46  tff(c_474, plain, (![D_112]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_112)=k9_relat_1('#skF_4', D_112))), inference(resolution, [status(thm)], [c_62, c_468])).
% 3.20/1.46  tff(c_637, plain, (![D_112]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_112)=k9_relat_1('#skF_4', D_112))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_474])).
% 3.20/1.46  tff(c_466, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_339])).
% 3.20/1.46  tff(c_706, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_467, c_466])).
% 3.20/1.46  tff(c_709, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_706])).
% 3.20/1.46  tff(c_713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_709])).
% 3.20/1.46  tff(c_714, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_184])).
% 3.20/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.46  tff(c_725, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_714, c_2])).
% 3.20/1.46  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.46  tff(c_726, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_714, c_714, c_34])).
% 3.20/1.46  tff(c_715, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_184])).
% 3.20/1.46  tff(c_746, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_714, c_715])).
% 3.20/1.46  tff(c_770, plain, (![B_128, A_129]: (v4_relat_1(B_128, A_129) | ~r1_tarski(k1_relat_1(B_128), A_129) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.20/1.46  tff(c_773, plain, (![A_129]: (v4_relat_1('#skF_4', A_129) | ~r1_tarski('#skF_4', A_129) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_746, c_770])).
% 3.20/1.46  tff(c_775, plain, (![A_129]: (v4_relat_1('#skF_4', A_129))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_725, c_773])).
% 3.20/1.46  tff(c_849, plain, (![B_147, A_148]: (k7_relat_1(B_147, A_148)=B_147 | ~v4_relat_1(B_147, A_148) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.20/1.46  tff(c_852, plain, (![A_129]: (k7_relat_1('#skF_4', A_129)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_775, c_849])).
% 3.20/1.46  tff(c_857, plain, (![A_150]: (k7_relat_1('#skF_4', A_150)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_852])).
% 3.20/1.46  tff(c_30, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.20/1.46  tff(c_862, plain, (![A_150]: (k9_relat_1('#skF_4', A_150)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_857, c_30])).
% 3.20/1.46  tff(c_867, plain, (![A_150]: (k9_relat_1('#skF_4', A_150)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_726, c_862])).
% 3.20/1.46  tff(c_20, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.20/1.46  tff(c_721, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_714, c_20])).
% 3.20/1.46  tff(c_925, plain, (![A_161, B_162, C_163, D_164]: (k7_relset_1(A_161, B_162, C_163, D_164)=k9_relat_1(C_163, D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.20/1.46  tff(c_928, plain, (![A_161, B_162, D_164]: (k7_relset_1(A_161, B_162, '#skF_4', D_164)=k9_relat_1('#skF_4', D_164))), inference(resolution, [status(thm)], [c_721, c_925])).
% 3.20/1.46  tff(c_930, plain, (![A_161, B_162, D_164]: (k7_relset_1(A_161, B_162, '#skF_4', D_164)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_867, c_928])).
% 3.20/1.46  tff(c_931, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_930, c_58])).
% 3.20/1.46  tff(c_934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_725, c_931])).
% 3.20/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.46  
% 3.20/1.46  Inference rules
% 3.20/1.46  ----------------------
% 3.20/1.46  #Ref     : 0
% 3.20/1.46  #Sup     : 183
% 3.20/1.46  #Fact    : 0
% 3.20/1.46  #Define  : 0
% 3.20/1.46  #Split   : 4
% 3.20/1.46  #Chain   : 0
% 3.20/1.46  #Close   : 0
% 3.20/1.46  
% 3.20/1.46  Ordering : KBO
% 3.20/1.46  
% 3.20/1.46  Simplification rules
% 3.20/1.46  ----------------------
% 3.20/1.46  #Subsume      : 3
% 3.20/1.46  #Demod        : 165
% 3.20/1.46  #Tautology    : 124
% 3.20/1.46  #SimpNegUnit  : 3
% 3.20/1.46  #BackRed      : 24
% 3.20/1.46  
% 3.20/1.46  #Partial instantiations: 0
% 3.20/1.46  #Strategies tried      : 1
% 3.20/1.46  
% 3.20/1.46  Timing (in seconds)
% 3.20/1.46  ----------------------
% 3.20/1.47  Preprocessing        : 0.33
% 3.20/1.47  Parsing              : 0.18
% 3.20/1.47  CNF conversion       : 0.02
% 3.20/1.47  Main loop            : 0.35
% 3.20/1.47  Inferencing          : 0.13
% 3.20/1.47  Reduction            : 0.12
% 3.20/1.47  Demodulation         : 0.09
% 3.20/1.47  BG Simplification    : 0.02
% 3.20/1.47  Subsumption          : 0.05
% 3.20/1.47  Abstraction          : 0.02
% 3.20/1.47  MUC search           : 0.00
% 3.20/1.47  Cooper               : 0.00
% 3.20/1.47  Total                : 0.72
% 3.20/1.47  Index Insertion      : 0.00
% 3.20/1.47  Index Deletion       : 0.00
% 3.20/1.47  Index Matching       : 0.00
% 3.20/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
