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
% DateTime   : Thu Dec  3 10:14:46 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 219 expanded)
%              Number of leaves         :   40 (  90 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 448 expanded)
%              Number of equality atoms :   57 ( 150 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_134,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_134])).

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

tff(c_150,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_142,c_40])).

tff(c_166,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_310,plain,(
    ! [B_79,A_80] :
      ( k1_tarski(k1_funct_1(B_79,A_80)) = k2_relat_1(B_79)
      | k1_tarski(A_80) != k1_relat_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_322,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_52])).

tff(c_334,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_60,c_322])).

tff(c_347,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_213,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_221,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_213])).

tff(c_30,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_405,plain,(
    ! [B_96,C_97,A_98] :
      ( k2_tarski(B_96,C_97) = A_98
      | k1_tarski(C_97) = A_98
      | k1_tarski(B_96) = A_98
      | k1_xboole_0 = A_98
      | ~ r1_tarski(A_98,k2_tarski(B_96,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_421,plain,(
    ! [A_4,A_98] :
      ( k2_tarski(A_4,A_4) = A_98
      | k1_tarski(A_4) = A_98
      | k1_tarski(A_4) = A_98
      | k1_xboole_0 = A_98
      | ~ r1_tarski(A_98,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_405])).

tff(c_441,plain,(
    ! [A_99,A_100] :
      ( k1_tarski(A_99) = A_100
      | k1_tarski(A_99) = A_100
      | k1_tarski(A_99) = A_100
      | k1_xboole_0 = A_100
      | ~ r1_tarski(A_100,k1_tarski(A_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_421])).

tff(c_466,plain,(
    ! [A_101,B_102] :
      ( k1_tarski(A_101) = k1_relat_1(B_102)
      | k1_relat_1(B_102) = k1_xboole_0
      | ~ v4_relat_1(B_102,k1_tarski(A_101))
      | ~ v1_relat_1(B_102) ) ),
    inference(resolution,[status(thm)],[c_30,c_441])).

tff(c_472,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_221,c_466])).

tff(c_479,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_472])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_347,c_479])).

tff(c_483,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_487,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_56])).

tff(c_50,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k7_relset_1(A_27,B_28,C_29,D_30) = k9_relat_1(C_29,D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_575,plain,(
    ! [D_30] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_30) = k9_relat_1('#skF_4',D_30) ),
    inference(resolution,[status(thm)],[c_487,c_50])).

tff(c_482,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_583,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_482])).

tff(c_591,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_583])).

tff(c_603,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_591])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_603])).

tff(c_608,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_615,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_8])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_616,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_608,c_34])).

tff(c_642,plain,(
    ! [A_16] :
      ( r1_tarski(k9_relat_1('#skF_4',A_16),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_32])).

tff(c_669,plain,(
    ! [A_121] : r1_tarski(k9_relat_1('#skF_4',A_121),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_642])).

tff(c_105,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_611,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_608,c_116])).

tff(c_675,plain,(
    ! [A_121] : k9_relat_1('#skF_4',A_121) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_669,c_611])).

tff(c_24,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_614,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_24])).

tff(c_773,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( k7_relset_1(A_144,B_145,C_146,D_147) = k9_relat_1(C_146,D_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_776,plain,(
    ! [A_144,B_145,D_147] : k7_relset_1(A_144,B_145,'#skF_4',D_147) = k9_relat_1('#skF_4',D_147) ),
    inference(resolution,[status(thm)],[c_614,c_773])).

tff(c_778,plain,(
    ! [A_144,B_145,D_147] : k7_relset_1(A_144,B_145,'#skF_4',D_147) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_776])).

tff(c_779,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_52])).

tff(c_782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:42:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.40  
% 2.88/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.88/1.40  
% 2.88/1.40  %Foreground sorts:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Background operators:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Foreground operators:
% 2.88/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.88/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.88/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.88/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.88/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.88/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.40  
% 2.88/1.42  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.88/1.42  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.88/1.42  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.88/1.42  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.88/1.42  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.88/1.42  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.88/1.42  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.88/1.42  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.88/1.42  tff(f_52, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.88/1.42  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.88/1.42  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.88/1.42  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.88/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.88/1.42  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.88/1.42  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.88/1.42  tff(c_134, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.88/1.42  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_134])).
% 2.88/1.42  tff(c_32, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.88/1.42  tff(c_40, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.88/1.42  tff(c_150, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_142, c_40])).
% 2.88/1.42  tff(c_166, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_150])).
% 2.88/1.42  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.88/1.42  tff(c_310, plain, (![B_79, A_80]: (k1_tarski(k1_funct_1(B_79, A_80))=k2_relat_1(B_79) | k1_tarski(A_80)!=k1_relat_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.88/1.42  tff(c_52, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.88/1.42  tff(c_322, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_310, c_52])).
% 2.88/1.42  tff(c_334, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_60, c_322])).
% 2.88/1.42  tff(c_347, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_334])).
% 2.88/1.42  tff(c_213, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.42  tff(c_221, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_213])).
% 2.88/1.42  tff(c_30, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.88/1.42  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.42  tff(c_405, plain, (![B_96, C_97, A_98]: (k2_tarski(B_96, C_97)=A_98 | k1_tarski(C_97)=A_98 | k1_tarski(B_96)=A_98 | k1_xboole_0=A_98 | ~r1_tarski(A_98, k2_tarski(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.88/1.42  tff(c_421, plain, (![A_4, A_98]: (k2_tarski(A_4, A_4)=A_98 | k1_tarski(A_4)=A_98 | k1_tarski(A_4)=A_98 | k1_xboole_0=A_98 | ~r1_tarski(A_98, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_405])).
% 2.88/1.42  tff(c_441, plain, (![A_99, A_100]: (k1_tarski(A_99)=A_100 | k1_tarski(A_99)=A_100 | k1_tarski(A_99)=A_100 | k1_xboole_0=A_100 | ~r1_tarski(A_100, k1_tarski(A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_421])).
% 2.88/1.42  tff(c_466, plain, (![A_101, B_102]: (k1_tarski(A_101)=k1_relat_1(B_102) | k1_relat_1(B_102)=k1_xboole_0 | ~v4_relat_1(B_102, k1_tarski(A_101)) | ~v1_relat_1(B_102))), inference(resolution, [status(thm)], [c_30, c_441])).
% 2.88/1.42  tff(c_472, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_221, c_466])).
% 2.88/1.42  tff(c_479, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_142, c_472])).
% 2.88/1.42  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_347, c_479])).
% 2.88/1.42  tff(c_483, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_334])).
% 2.88/1.42  tff(c_487, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_56])).
% 2.88/1.42  tff(c_50, plain, (![A_27, B_28, C_29, D_30]: (k7_relset_1(A_27, B_28, C_29, D_30)=k9_relat_1(C_29, D_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.42  tff(c_575, plain, (![D_30]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_30)=k9_relat_1('#skF_4', D_30))), inference(resolution, [status(thm)], [c_487, c_50])).
% 2.88/1.42  tff(c_482, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_334])).
% 2.88/1.42  tff(c_583, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_482])).
% 2.88/1.42  tff(c_591, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_583])).
% 2.88/1.42  tff(c_603, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_591])).
% 2.88/1.42  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_603])).
% 2.88/1.42  tff(c_608, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_150])).
% 2.88/1.42  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.42  tff(c_615, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_8])).
% 2.88/1.42  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.88/1.42  tff(c_616, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_608, c_608, c_34])).
% 2.88/1.42  tff(c_642, plain, (![A_16]: (r1_tarski(k9_relat_1('#skF_4', A_16), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_616, c_32])).
% 2.88/1.42  tff(c_669, plain, (![A_121]: (r1_tarski(k9_relat_1('#skF_4', A_121), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_642])).
% 2.88/1.42  tff(c_105, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.42  tff(c_116, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_105])).
% 2.88/1.42  tff(c_611, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_608, c_116])).
% 2.88/1.42  tff(c_675, plain, (![A_121]: (k9_relat_1('#skF_4', A_121)='#skF_4')), inference(resolution, [status(thm)], [c_669, c_611])).
% 2.88/1.42  tff(c_24, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.88/1.42  tff(c_614, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_24])).
% 2.88/1.42  tff(c_773, plain, (![A_144, B_145, C_146, D_147]: (k7_relset_1(A_144, B_145, C_146, D_147)=k9_relat_1(C_146, D_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.42  tff(c_776, plain, (![A_144, B_145, D_147]: (k7_relset_1(A_144, B_145, '#skF_4', D_147)=k9_relat_1('#skF_4', D_147))), inference(resolution, [status(thm)], [c_614, c_773])).
% 2.88/1.42  tff(c_778, plain, (![A_144, B_145, D_147]: (k7_relset_1(A_144, B_145, '#skF_4', D_147)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_675, c_776])).
% 2.88/1.42  tff(c_779, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_778, c_52])).
% 2.88/1.42  tff(c_782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_615, c_779])).
% 2.88/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.42  
% 2.88/1.42  Inference rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Ref     : 0
% 2.88/1.42  #Sup     : 143
% 2.88/1.42  #Fact    : 0
% 2.88/1.42  #Define  : 0
% 2.88/1.42  #Split   : 3
% 2.88/1.42  #Chain   : 0
% 2.88/1.42  #Close   : 0
% 2.88/1.42  
% 2.88/1.42  Ordering : KBO
% 2.88/1.42  
% 2.88/1.42  Simplification rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Subsume      : 8
% 2.88/1.42  #Demod        : 128
% 2.88/1.42  #Tautology    : 86
% 2.88/1.42  #SimpNegUnit  : 1
% 2.88/1.42  #BackRed      : 20
% 2.88/1.42  
% 2.88/1.42  #Partial instantiations: 0
% 2.88/1.42  #Strategies tried      : 1
% 2.88/1.42  
% 2.88/1.42  Timing (in seconds)
% 2.88/1.42  ----------------------
% 2.88/1.42  Preprocessing        : 0.32
% 2.88/1.42  Parsing              : 0.17
% 2.88/1.42  CNF conversion       : 0.02
% 2.88/1.42  Main loop            : 0.33
% 2.88/1.42  Inferencing          : 0.12
% 2.88/1.42  Reduction            : 0.11
% 2.88/1.42  Demodulation         : 0.08
% 2.88/1.42  BG Simplification    : 0.02
% 2.88/1.42  Subsumption          : 0.06
% 2.88/1.42  Abstraction          : 0.01
% 2.88/1.42  MUC search           : 0.00
% 2.88/1.42  Cooper               : 0.00
% 2.88/1.42  Total                : 0.68
% 2.88/1.42  Index Insertion      : 0.00
% 2.88/1.42  Index Deletion       : 0.00
% 2.88/1.42  Index Matching       : 0.00
% 2.88/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
