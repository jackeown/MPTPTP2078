%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:46 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 183 expanded)
%              Number of leaves         :   40 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 345 expanded)
%              Number of equality atoms :   55 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_205,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_213,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_205])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,A_16),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_222,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_213,c_40])).

tff(c_224,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_371,plain,(
    ! [B_94,A_95] :
      ( k1_tarski(k1_funct_1(B_94,A_95)) = k2_relat_1(B_94)
      | k1_tarski(A_95) != k1_relat_1(B_94)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_298,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k7_relset_1(A_75,B_76,C_77,D_78) = k9_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_304,plain,(
    ! [D_78] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_78) = k9_relat_1('#skF_4',D_78) ),
    inference(resolution,[status(thm)],[c_56,c_298])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_315,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_52])).

tff(c_383,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_315])).

tff(c_395,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_60,c_383])).

tff(c_397,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_395])).

tff(c_240,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_248,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_240])).

tff(c_30,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_411,plain,(
    ! [B_99,C_100,A_101] :
      ( k2_tarski(B_99,C_100) = A_101
      | k1_tarski(C_100) = A_101
      | k1_tarski(B_99) = A_101
      | k1_xboole_0 = A_101
      | ~ r1_tarski(A_101,k2_tarski(B_99,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_427,plain,(
    ! [A_4,A_101] :
      ( k2_tarski(A_4,A_4) = A_101
      | k1_tarski(A_4) = A_101
      | k1_tarski(A_4) = A_101
      | k1_xboole_0 = A_101
      | ~ r1_tarski(A_101,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_411])).

tff(c_447,plain,(
    ! [A_102,A_103] :
      ( k1_tarski(A_102) = A_103
      | k1_tarski(A_102) = A_103
      | k1_tarski(A_102) = A_103
      | k1_xboole_0 = A_103
      | ~ r1_tarski(A_103,k1_tarski(A_102)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_427])).

tff(c_468,plain,(
    ! [A_104,B_105] :
      ( k1_tarski(A_104) = k1_relat_1(B_105)
      | k1_relat_1(B_105) = k1_xboole_0
      | ~ v4_relat_1(B_105,k1_tarski(A_104))
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_30,c_447])).

tff(c_474,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_248,c_468])).

tff(c_481,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_474])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_397,c_481])).

tff(c_484,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_543,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_484])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_543])).

tff(c_548,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_556,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_8])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_112,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(k9_relat_1(B_43,A_44),k2_relat_1(B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_117,plain,(
    ! [A_44] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_44),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_112])).

tff(c_132,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_24,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_142,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_149,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_142])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_149])).

tff(c_171,plain,(
    ! [A_51] : r1_tarski(k9_relat_1(k1_xboole_0,A_51),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_96,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_177,plain,(
    ! [A_51] : k9_relat_1(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_171,c_111])).

tff(c_550,plain,(
    ! [A_51] : k9_relat_1('#skF_4',A_51) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_548,c_177])).

tff(c_555,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_24])).

tff(c_770,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( k7_relset_1(A_144,B_145,C_146,D_147) = k9_relat_1(C_146,D_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_773,plain,(
    ! [A_144,B_145,D_147] : k7_relset_1(A_144,B_145,'#skF_4',D_147) = k9_relat_1('#skF_4',D_147) ),
    inference(resolution,[status(thm)],[c_555,c_770])).

tff(c_775,plain,(
    ! [A_144,B_145,D_147] : k7_relset_1(A_144,B_145,'#skF_4',D_147) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_773])).

tff(c_809,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_52])).

tff(c_812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:34:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.13/1.49  
% 3.13/1.49  %Foreground sorts:
% 3.13/1.49  
% 3.13/1.49  
% 3.13/1.49  %Background operators:
% 3.13/1.49  
% 3.13/1.49  
% 3.13/1.49  %Foreground operators:
% 3.13/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.13/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.13/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.13/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.13/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.13/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.13/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.49  
% 3.13/1.51  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.13/1.51  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.13/1.51  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.13/1.51  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.13/1.51  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.13/1.51  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.13/1.51  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.13/1.51  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.13/1.51  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.13/1.51  tff(f_52, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.13/1.51  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.13/1.51  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.13/1.51  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.13/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.13/1.51  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.13/1.51  tff(c_205, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.51  tff(c_213, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_205])).
% 3.13/1.51  tff(c_32, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.13/1.51  tff(c_40, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.13/1.51  tff(c_222, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_213, c_40])).
% 3.13/1.51  tff(c_224, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_222])).
% 3.13/1.51  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.13/1.51  tff(c_371, plain, (![B_94, A_95]: (k1_tarski(k1_funct_1(B_94, A_95))=k2_relat_1(B_94) | k1_tarski(A_95)!=k1_relat_1(B_94) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.13/1.51  tff(c_298, plain, (![A_75, B_76, C_77, D_78]: (k7_relset_1(A_75, B_76, C_77, D_78)=k9_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.13/1.51  tff(c_304, plain, (![D_78]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_78)=k9_relat_1('#skF_4', D_78))), inference(resolution, [status(thm)], [c_56, c_298])).
% 3.13/1.51  tff(c_52, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.13/1.51  tff(c_315, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_52])).
% 3.13/1.51  tff(c_383, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_371, c_315])).
% 3.13/1.51  tff(c_395, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_60, c_383])).
% 3.13/1.51  tff(c_397, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_395])).
% 3.13/1.51  tff(c_240, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.13/1.51  tff(c_248, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_240])).
% 3.13/1.51  tff(c_30, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.51  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.51  tff(c_411, plain, (![B_99, C_100, A_101]: (k2_tarski(B_99, C_100)=A_101 | k1_tarski(C_100)=A_101 | k1_tarski(B_99)=A_101 | k1_xboole_0=A_101 | ~r1_tarski(A_101, k2_tarski(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.13/1.51  tff(c_427, plain, (![A_4, A_101]: (k2_tarski(A_4, A_4)=A_101 | k1_tarski(A_4)=A_101 | k1_tarski(A_4)=A_101 | k1_xboole_0=A_101 | ~r1_tarski(A_101, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_411])).
% 3.13/1.51  tff(c_447, plain, (![A_102, A_103]: (k1_tarski(A_102)=A_103 | k1_tarski(A_102)=A_103 | k1_tarski(A_102)=A_103 | k1_xboole_0=A_103 | ~r1_tarski(A_103, k1_tarski(A_102)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_427])).
% 3.13/1.51  tff(c_468, plain, (![A_104, B_105]: (k1_tarski(A_104)=k1_relat_1(B_105) | k1_relat_1(B_105)=k1_xboole_0 | ~v4_relat_1(B_105, k1_tarski(A_104)) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_30, c_447])).
% 3.13/1.51  tff(c_474, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_248, c_468])).
% 3.13/1.51  tff(c_481, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_213, c_474])).
% 3.13/1.51  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_397, c_481])).
% 3.13/1.51  tff(c_484, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_395])).
% 3.13/1.51  tff(c_543, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_484])).
% 3.13/1.51  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_543])).
% 3.13/1.51  tff(c_548, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_222])).
% 3.13/1.51  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.51  tff(c_556, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_8])).
% 3.13/1.51  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.51  tff(c_112, plain, (![B_43, A_44]: (r1_tarski(k9_relat_1(B_43, A_44), k2_relat_1(B_43)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.13/1.51  tff(c_117, plain, (![A_44]: (r1_tarski(k9_relat_1(k1_xboole_0, A_44), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_112])).
% 3.13/1.51  tff(c_132, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_117])).
% 3.13/1.51  tff(c_24, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.51  tff(c_142, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.51  tff(c_149, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_142])).
% 3.13/1.51  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_149])).
% 3.13/1.51  tff(c_171, plain, (![A_51]: (r1_tarski(k9_relat_1(k1_xboole_0, A_51), k1_xboole_0))), inference(splitRight, [status(thm)], [c_117])).
% 3.13/1.51  tff(c_96, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.51  tff(c_111, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_96])).
% 3.13/1.51  tff(c_177, plain, (![A_51]: (k9_relat_1(k1_xboole_0, A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_171, c_111])).
% 3.13/1.51  tff(c_550, plain, (![A_51]: (k9_relat_1('#skF_4', A_51)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_548, c_548, c_177])).
% 3.13/1.51  tff(c_555, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_24])).
% 3.13/1.51  tff(c_770, plain, (![A_144, B_145, C_146, D_147]: (k7_relset_1(A_144, B_145, C_146, D_147)=k9_relat_1(C_146, D_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.13/1.51  tff(c_773, plain, (![A_144, B_145, D_147]: (k7_relset_1(A_144, B_145, '#skF_4', D_147)=k9_relat_1('#skF_4', D_147))), inference(resolution, [status(thm)], [c_555, c_770])).
% 3.13/1.51  tff(c_775, plain, (![A_144, B_145, D_147]: (k7_relset_1(A_144, B_145, '#skF_4', D_147)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_773])).
% 3.13/1.51  tff(c_809, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_775, c_52])).
% 3.13/1.51  tff(c_812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_556, c_809])).
% 3.13/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  Inference rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Ref     : 0
% 3.13/1.51  #Sup     : 147
% 3.13/1.51  #Fact    : 0
% 3.13/1.51  #Define  : 0
% 3.13/1.51  #Split   : 5
% 3.13/1.51  #Chain   : 0
% 3.13/1.51  #Close   : 0
% 3.13/1.51  
% 3.13/1.51  Ordering : KBO
% 3.13/1.51  
% 3.13/1.51  Simplification rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Subsume      : 6
% 3.13/1.51  #Demod        : 123
% 3.13/1.51  #Tautology    : 90
% 3.13/1.51  #SimpNegUnit  : 2
% 3.13/1.51  #BackRed      : 18
% 3.13/1.51  
% 3.13/1.51  #Partial instantiations: 0
% 3.13/1.51  #Strategies tried      : 1
% 3.13/1.51  
% 3.13/1.51  Timing (in seconds)
% 3.13/1.51  ----------------------
% 3.13/1.52  Preprocessing        : 0.34
% 3.13/1.52  Parsing              : 0.18
% 3.13/1.52  CNF conversion       : 0.02
% 3.13/1.52  Main loop            : 0.39
% 3.13/1.52  Inferencing          : 0.14
% 3.13/1.52  Reduction            : 0.12
% 3.13/1.52  Demodulation         : 0.09
% 3.13/1.52  BG Simplification    : 0.02
% 3.13/1.52  Subsumption          : 0.08
% 3.13/1.52  Abstraction          : 0.02
% 3.13/1.52  MUC search           : 0.00
% 3.13/1.52  Cooper               : 0.00
% 3.13/1.52  Total                : 0.78
% 3.13/1.52  Index Insertion      : 0.00
% 3.13/1.52  Index Deletion       : 0.00
% 3.13/1.52  Index Matching       : 0.00
% 3.13/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
