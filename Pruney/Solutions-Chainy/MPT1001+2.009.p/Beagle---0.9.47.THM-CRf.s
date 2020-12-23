%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:56 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 150 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 306 expanded)
%              Number of equality atoms :   37 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & k8_relset_1(A,B,C,k1_tarski(D)) = k1_xboole_0 )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_76,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_79,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_79])).

tff(c_158,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_162,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_158])).

tff(c_48,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_83,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_163,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_83])).

tff(c_283,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1(k2_relset_1(A_88,B_89,C_90),k1_zfmisc_1(B_89))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_296,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_283])).

tff(c_301,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_296])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [C_55,A_56,B_57] :
      ( r2_hidden(C_55,A_56)
      | ~ r2_hidden(C_55,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_168,plain,(
    ! [A_70,B_71,A_72] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_72)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(A_72))
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_184,plain,(
    ! [A_70,A_72] :
      ( ~ m1_subset_1(A_70,k1_zfmisc_1(A_72))
      | r1_tarski(A_70,A_72) ) ),
    inference(resolution,[status(thm)],[c_168,c_4])).

tff(c_308,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_301,c_184])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_311,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_308,c_8])).

tff(c_314,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_311])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_2'(A_22,B_23),A_22)
      | r1_tarski(A_22,k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( k10_relat_1(B_23,k1_tarski('#skF_2'(A_22,B_23))) = k1_xboole_0
      | r1_tarski(A_22,k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_343,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k8_relset_1(A_96,B_97,C_98,D_99) = k10_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_350,plain,(
    ! [D_99] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_99) = k10_relat_1('#skF_5',D_99) ),
    inference(resolution,[status(thm)],[c_38,c_343])).

tff(c_54,plain,(
    ! [D_37] :
      ( k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski(D_37)) != k1_xboole_0
      | ~ r2_hidden(D_37,'#skF_4')
      | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_315,plain,(
    ! [D_37] :
      ( k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski(D_37)) != k1_xboole_0
      | ~ r2_hidden(D_37,'#skF_4')
      | k2_relat_1('#skF_5') = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_54])).

tff(c_316,plain,(
    ! [D_37] :
      ( k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski(D_37)) != k1_xboole_0
      | ~ r2_hidden(D_37,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_315])).

tff(c_361,plain,(
    ! [D_101] :
      ( k10_relat_1('#skF_5',k1_tarski(D_101)) != k1_xboole_0
      | ~ r2_hidden(D_101,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_316])).

tff(c_365,plain,(
    ! [A_22] :
      ( ~ r2_hidden('#skF_2'(A_22,'#skF_5'),'#skF_4')
      | r1_tarski(A_22,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_361])).

tff(c_371,plain,(
    ! [A_102] :
      ( ~ r2_hidden('#skF_2'(A_102,'#skF_5'),'#skF_4')
      | r1_tarski(A_102,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_365])).

tff(c_375,plain,
    ( r1_tarski('#skF_4',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_371])).

tff(c_378,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_375])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_378])).

tff(c_382,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_498,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_501,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_498])).

tff(c_503,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_501])).

tff(c_381,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_402,plain,(
    ! [C_109,B_110,A_111] :
      ( r2_hidden(C_109,B_110)
      | ~ r2_hidden(C_109,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_408,plain,(
    ! [B_110] :
      ( r2_hidden('#skF_6',B_110)
      | ~ r1_tarski('#skF_4',B_110) ) ),
    inference(resolution,[status(thm)],[c_381,c_402])).

tff(c_459,plain,(
    ! [B_125,A_126] :
      ( k10_relat_1(B_125,k1_tarski(A_126)) != k1_xboole_0
      | ~ r2_hidden(A_126,k2_relat_1(B_125))
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_477,plain,(
    ! [B_125] :
      ( k10_relat_1(B_125,k1_tarski('#skF_6')) != k1_xboole_0
      | ~ v1_relat_1(B_125)
      | ~ r1_tarski('#skF_4',k2_relat_1(B_125)) ) ),
    inference(resolution,[status(thm)],[c_408,c_459])).

tff(c_507,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_6')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_477])).

tff(c_517,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_82,c_507])).

tff(c_674,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( k8_relset_1(A_153,B_154,C_155,D_156) = k10_relat_1(C_155,D_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_682,plain,(
    ! [D_157] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_157) = k10_relat_1('#skF_5',D_157) ),
    inference(resolution,[status(thm)],[c_38,c_674])).

tff(c_44,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_414,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_44])).

tff(c_688,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_414])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.73/1.40  
% 2.73/1.40  %Foreground sorts:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Background operators:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Foreground operators:
% 2.73/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.73/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.73/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.73/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.40  
% 2.73/1.42  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.42  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.73/1.42  tff(f_102, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (k8_relset_1(A, B, C, k1_tarski(D)) = k1_xboole_0))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_2)).
% 2.73/1.42  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.73/1.42  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.73/1.42  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.73/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.73/1.42  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.73/1.42  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_1)).
% 2.73/1.42  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.73/1.42  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.73/1.42  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.42  tff(c_22, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.42  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.73/1.42  tff(c_76, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.42  tff(c_79, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_76])).
% 2.73/1.42  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_79])).
% 2.73/1.42  tff(c_158, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.42  tff(c_162, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_158])).
% 2.73/1.42  tff(c_48, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.73/1.42  tff(c_83, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 2.73/1.42  tff(c_163, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_83])).
% 2.73/1.42  tff(c_283, plain, (![A_88, B_89, C_90]: (m1_subset_1(k2_relset_1(A_88, B_89, C_90), k1_zfmisc_1(B_89)) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.73/1.42  tff(c_296, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_162, c_283])).
% 2.73/1.42  tff(c_301, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_296])).
% 2.73/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.42  tff(c_103, plain, (![C_55, A_56, B_57]: (r2_hidden(C_55, A_56) | ~r2_hidden(C_55, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.42  tff(c_168, plain, (![A_70, B_71, A_72]: (r2_hidden('#skF_1'(A_70, B_71), A_72) | ~m1_subset_1(A_70, k1_zfmisc_1(A_72)) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_6, c_103])).
% 2.73/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.42  tff(c_184, plain, (![A_70, A_72]: (~m1_subset_1(A_70, k1_zfmisc_1(A_72)) | r1_tarski(A_70, A_72))), inference(resolution, [status(thm)], [c_168, c_4])).
% 2.73/1.42  tff(c_308, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_301, c_184])).
% 2.73/1.42  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.42  tff(c_311, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_308, c_8])).
% 2.73/1.42  tff(c_314, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_163, c_311])).
% 2.73/1.42  tff(c_30, plain, (![A_22, B_23]: (r2_hidden('#skF_2'(A_22, B_23), A_22) | r1_tarski(A_22, k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.42  tff(c_28, plain, (![B_23, A_22]: (k10_relat_1(B_23, k1_tarski('#skF_2'(A_22, B_23)))=k1_xboole_0 | r1_tarski(A_22, k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.42  tff(c_343, plain, (![A_96, B_97, C_98, D_99]: (k8_relset_1(A_96, B_97, C_98, D_99)=k10_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.73/1.42  tff(c_350, plain, (![D_99]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_99)=k10_relat_1('#skF_5', D_99))), inference(resolution, [status(thm)], [c_38, c_343])).
% 2.73/1.42  tff(c_54, plain, (![D_37]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski(D_37))!=k1_xboole_0 | ~r2_hidden(D_37, '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.73/1.42  tff(c_315, plain, (![D_37]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski(D_37))!=k1_xboole_0 | ~r2_hidden(D_37, '#skF_4') | k2_relat_1('#skF_5')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_54])).
% 2.73/1.42  tff(c_316, plain, (![D_37]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski(D_37))!=k1_xboole_0 | ~r2_hidden(D_37, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_163, c_315])).
% 2.73/1.42  tff(c_361, plain, (![D_101]: (k10_relat_1('#skF_5', k1_tarski(D_101))!=k1_xboole_0 | ~r2_hidden(D_101, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_316])).
% 2.73/1.42  tff(c_365, plain, (![A_22]: (~r2_hidden('#skF_2'(A_22, '#skF_5'), '#skF_4') | r1_tarski(A_22, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_361])).
% 2.73/1.42  tff(c_371, plain, (![A_102]: (~r2_hidden('#skF_2'(A_102, '#skF_5'), '#skF_4') | r1_tarski(A_102, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_365])).
% 2.73/1.42  tff(c_375, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_371])).
% 2.73/1.42  tff(c_378, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_375])).
% 2.73/1.42  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_378])).
% 2.73/1.42  tff(c_382, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 2.73/1.42  tff(c_498, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.42  tff(c_501, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_498])).
% 2.73/1.42  tff(c_503, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_382, c_501])).
% 2.73/1.42  tff(c_381, plain, (r2_hidden('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 2.73/1.42  tff(c_402, plain, (![C_109, B_110, A_111]: (r2_hidden(C_109, B_110) | ~r2_hidden(C_109, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.42  tff(c_408, plain, (![B_110]: (r2_hidden('#skF_6', B_110) | ~r1_tarski('#skF_4', B_110))), inference(resolution, [status(thm)], [c_381, c_402])).
% 2.73/1.42  tff(c_459, plain, (![B_125, A_126]: (k10_relat_1(B_125, k1_tarski(A_126))!=k1_xboole_0 | ~r2_hidden(A_126, k2_relat_1(B_125)) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.73/1.42  tff(c_477, plain, (![B_125]: (k10_relat_1(B_125, k1_tarski('#skF_6'))!=k1_xboole_0 | ~v1_relat_1(B_125) | ~r1_tarski('#skF_4', k2_relat_1(B_125)))), inference(resolution, [status(thm)], [c_408, c_459])).
% 2.73/1.42  tff(c_507, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_6'))!=k1_xboole_0 | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_503, c_477])).
% 2.73/1.42  tff(c_517, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_82, c_507])).
% 2.73/1.42  tff(c_674, plain, (![A_153, B_154, C_155, D_156]: (k8_relset_1(A_153, B_154, C_155, D_156)=k10_relat_1(C_155, D_156) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.73/1.42  tff(c_682, plain, (![D_157]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_157)=k10_relat_1('#skF_5', D_157))), inference(resolution, [status(thm)], [c_38, c_674])).
% 2.73/1.42  tff(c_44, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.73/1.42  tff(c_414, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_382, c_44])).
% 2.73/1.42  tff(c_688, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_682, c_414])).
% 2.73/1.42  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_517, c_688])).
% 2.73/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  Inference rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Ref     : 0
% 2.73/1.42  #Sup     : 135
% 2.73/1.42  #Fact    : 0
% 2.73/1.42  #Define  : 0
% 2.73/1.42  #Split   : 8
% 2.73/1.42  #Chain   : 0
% 2.73/1.42  #Close   : 0
% 2.73/1.42  
% 2.73/1.42  Ordering : KBO
% 2.73/1.42  
% 2.73/1.42  Simplification rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Subsume      : 7
% 2.73/1.42  #Demod        : 48
% 2.73/1.42  #Tautology    : 47
% 2.73/1.42  #SimpNegUnit  : 7
% 2.73/1.42  #BackRed      : 3
% 2.73/1.42  
% 2.73/1.42  #Partial instantiations: 0
% 2.73/1.42  #Strategies tried      : 1
% 2.73/1.42  
% 2.73/1.42  Timing (in seconds)
% 2.73/1.42  ----------------------
% 2.73/1.42  Preprocessing        : 0.32
% 2.73/1.42  Parsing              : 0.17
% 2.73/1.42  CNF conversion       : 0.02
% 2.73/1.42  Main loop            : 0.34
% 2.73/1.42  Inferencing          : 0.12
% 2.73/1.42  Reduction            : 0.10
% 2.73/1.42  Demodulation         : 0.07
% 2.73/1.42  BG Simplification    : 0.02
% 2.73/1.42  Subsumption          : 0.07
% 2.73/1.42  Abstraction          : 0.02
% 2.73/1.42  MUC search           : 0.00
% 2.73/1.42  Cooper               : 0.00
% 2.73/1.42  Total                : 0.69
% 2.73/1.42  Index Insertion      : 0.00
% 2.73/1.42  Index Deletion       : 0.00
% 2.73/1.42  Index Matching       : 0.00
% 2.73/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
