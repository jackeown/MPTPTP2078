%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:46 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 397 expanded)
%              Number of leaves         :   40 ( 154 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 917 expanded)
%              Number of equality atoms :   55 ( 323 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_118,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_130,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_118])).

tff(c_36,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,A_16),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_338,plain,(
    ! [B_80,A_81] :
      ( k1_tarski(k1_funct_1(B_80,A_81)) = k2_relat_1(B_80)
      | k1_tarski(A_81) != k1_relat_1(B_80)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_344,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_54])).

tff(c_356,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_62,c_344])).

tff(c_398,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_276,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_290,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_276])).

tff(c_34,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_440,plain,(
    ! [B_98,C_99,A_100] :
      ( k2_tarski(B_98,C_99) = A_100
      | k1_tarski(C_99) = A_100
      | k1_tarski(B_98) = A_100
      | k1_xboole_0 = A_100
      | ~ r1_tarski(A_100,k2_tarski(B_98,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_453,plain,(
    ! [A_4,A_100] :
      ( k2_tarski(A_4,A_4) = A_100
      | k1_tarski(A_4) = A_100
      | k1_tarski(A_4) = A_100
      | k1_xboole_0 = A_100
      | ~ r1_tarski(A_100,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_440])).

tff(c_500,plain,(
    ! [A_108,A_109] :
      ( k1_tarski(A_108) = A_109
      | k1_tarski(A_108) = A_109
      | k1_tarski(A_108) = A_109
      | k1_xboole_0 = A_109
      | ~ r1_tarski(A_109,k1_tarski(A_108)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_453])).

tff(c_521,plain,(
    ! [A_110,B_111] :
      ( k1_tarski(A_110) = k1_relat_1(B_111)
      | k1_relat_1(B_111) = k1_xboole_0
      | ~ v4_relat_1(B_111,k1_tarski(A_110))
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_34,c_500])).

tff(c_527,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_290,c_521])).

tff(c_534,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_527])).

tff(c_535,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_398,c_534])).

tff(c_228,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,k2_zfmisc_1(k1_relat_1(A_57),k2_relat_1(A_57)))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_588,plain,(
    ! [A_112] :
      ( k2_zfmisc_1(k1_relat_1(A_112),k2_relat_1(A_112)) = A_112
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_112),k2_relat_1(A_112)),A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_228,c_2])).

tff(c_591,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_588])).

tff(c_599,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_8,c_26,c_26,c_535,c_591])).

tff(c_627,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_8])).

tff(c_28,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_131,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_118])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_179,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(k9_relat_1(B_50,A_51),k2_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_184,plain,(
    ! [A_51] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_51),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_179])).

tff(c_188,plain,(
    ! [A_52] : r1_tarski(k9_relat_1(k1_xboole_0,A_52),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_184])).

tff(c_132,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_194,plain,(
    ! [A_52] : k9_relat_1(k1_xboole_0,A_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_188,c_147])).

tff(c_619,plain,(
    ! [A_52] : k9_relat_1('#skF_4',A_52) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_599,c_194])).

tff(c_410,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( k7_relset_1(A_90,B_91,C_92,D_93) = k9_relat_1(C_92,D_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_420,plain,(
    ! [D_93] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_93) = k9_relat_1('#skF_4',D_93) ),
    inference(resolution,[status(thm)],[c_58,c_410])).

tff(c_430,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_54])).

tff(c_822,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_430])).

tff(c_826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_822])).

tff(c_828,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_832,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_58])).

tff(c_52,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k7_relset_1(A_27,B_28,C_29,D_30) = k9_relat_1(C_29,D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_924,plain,(
    ! [D_30] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_30) = k9_relat_1('#skF_4',D_30) ),
    inference(resolution,[status(thm)],[c_832,c_52])).

tff(c_827,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_938,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_827])).

tff(c_939,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_924,c_938])).

tff(c_952,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_939])).

tff(c_956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_952])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:27:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.46  
% 2.85/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.85/1.46  
% 2.85/1.46  %Foreground sorts:
% 2.85/1.46  
% 2.85/1.46  
% 2.85/1.46  %Background operators:
% 2.85/1.46  
% 2.85/1.46  
% 2.85/1.46  %Foreground operators:
% 2.85/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.85/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.85/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.85/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.85/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.85/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.85/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.85/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.85/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.46  
% 3.23/1.48  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.23/1.48  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.23/1.48  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.23/1.48  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.23/1.48  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.23/1.48  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.23/1.48  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.23/1.48  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.23/1.48  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.23/1.48  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.23/1.48  tff(f_78, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.23/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.48  tff(f_58, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.23/1.48  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.23/1.48  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.23/1.48  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.23/1.48  tff(c_118, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.48  tff(c_130, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_118])).
% 3.23/1.48  tff(c_36, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.23/1.48  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.48  tff(c_26, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.23/1.48  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.23/1.48  tff(c_338, plain, (![B_80, A_81]: (k1_tarski(k1_funct_1(B_80, A_81))=k2_relat_1(B_80) | k1_tarski(A_81)!=k1_relat_1(B_80) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.23/1.48  tff(c_54, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.23/1.48  tff(c_344, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_338, c_54])).
% 3.23/1.48  tff(c_356, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_62, c_344])).
% 3.23/1.48  tff(c_398, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_356])).
% 3.23/1.48  tff(c_276, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.23/1.48  tff(c_290, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_276])).
% 3.23/1.48  tff(c_34, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.23/1.48  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.48  tff(c_440, plain, (![B_98, C_99, A_100]: (k2_tarski(B_98, C_99)=A_100 | k1_tarski(C_99)=A_100 | k1_tarski(B_98)=A_100 | k1_xboole_0=A_100 | ~r1_tarski(A_100, k2_tarski(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/1.48  tff(c_453, plain, (![A_4, A_100]: (k2_tarski(A_4, A_4)=A_100 | k1_tarski(A_4)=A_100 | k1_tarski(A_4)=A_100 | k1_xboole_0=A_100 | ~r1_tarski(A_100, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_440])).
% 3.23/1.48  tff(c_500, plain, (![A_108, A_109]: (k1_tarski(A_108)=A_109 | k1_tarski(A_108)=A_109 | k1_tarski(A_108)=A_109 | k1_xboole_0=A_109 | ~r1_tarski(A_109, k1_tarski(A_108)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_453])).
% 3.23/1.48  tff(c_521, plain, (![A_110, B_111]: (k1_tarski(A_110)=k1_relat_1(B_111) | k1_relat_1(B_111)=k1_xboole_0 | ~v4_relat_1(B_111, k1_tarski(A_110)) | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_34, c_500])).
% 3.23/1.48  tff(c_527, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_290, c_521])).
% 3.23/1.48  tff(c_534, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_130, c_527])).
% 3.23/1.48  tff(c_535, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_398, c_534])).
% 3.23/1.48  tff(c_228, plain, (![A_57]: (r1_tarski(A_57, k2_zfmisc_1(k1_relat_1(A_57), k2_relat_1(A_57))) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.23/1.48  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.48  tff(c_588, plain, (![A_112]: (k2_zfmisc_1(k1_relat_1(A_112), k2_relat_1(A_112))=A_112 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_112), k2_relat_1(A_112)), A_112) | ~v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_228, c_2])).
% 3.23/1.48  tff(c_591, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_535, c_588])).
% 3.23/1.48  tff(c_599, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_8, c_26, c_26, c_535, c_591])).
% 3.23/1.48  tff(c_627, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_8])).
% 3.23/1.48  tff(c_28, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.23/1.48  tff(c_131, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_118])).
% 3.23/1.48  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.48  tff(c_179, plain, (![B_50, A_51]: (r1_tarski(k9_relat_1(B_50, A_51), k2_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.23/1.48  tff(c_184, plain, (![A_51]: (r1_tarski(k9_relat_1(k1_xboole_0, A_51), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_179])).
% 3.23/1.48  tff(c_188, plain, (![A_52]: (r1_tarski(k9_relat_1(k1_xboole_0, A_52), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_184])).
% 3.23/1.48  tff(c_132, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.48  tff(c_147, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_132])).
% 3.23/1.48  tff(c_194, plain, (![A_52]: (k9_relat_1(k1_xboole_0, A_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_188, c_147])).
% 3.23/1.48  tff(c_619, plain, (![A_52]: (k9_relat_1('#skF_4', A_52)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_599, c_194])).
% 3.23/1.48  tff(c_410, plain, (![A_90, B_91, C_92, D_93]: (k7_relset_1(A_90, B_91, C_92, D_93)=k9_relat_1(C_92, D_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.23/1.48  tff(c_420, plain, (![D_93]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_93)=k9_relat_1('#skF_4', D_93))), inference(resolution, [status(thm)], [c_58, c_410])).
% 3.23/1.48  tff(c_430, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_54])).
% 3.23/1.48  tff(c_822, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_619, c_430])).
% 3.23/1.48  tff(c_826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_627, c_822])).
% 3.23/1.48  tff(c_828, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_356])).
% 3.23/1.48  tff(c_832, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_828, c_58])).
% 3.23/1.48  tff(c_52, plain, (![A_27, B_28, C_29, D_30]: (k7_relset_1(A_27, B_28, C_29, D_30)=k9_relat_1(C_29, D_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.23/1.48  tff(c_924, plain, (![D_30]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_30)=k9_relat_1('#skF_4', D_30))), inference(resolution, [status(thm)], [c_832, c_52])).
% 3.23/1.48  tff(c_827, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_356])).
% 3.23/1.48  tff(c_938, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_828, c_827])).
% 3.23/1.48  tff(c_939, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_924, c_938])).
% 3.23/1.48  tff(c_952, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_939])).
% 3.23/1.48  tff(c_956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_952])).
% 3.23/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  Inference rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Ref     : 0
% 3.23/1.48  #Sup     : 187
% 3.23/1.48  #Fact    : 0
% 3.23/1.48  #Define  : 0
% 3.23/1.48  #Split   : 1
% 3.23/1.48  #Chain   : 0
% 3.23/1.48  #Close   : 0
% 3.23/1.48  
% 3.23/1.48  Ordering : KBO
% 3.23/1.48  
% 3.23/1.48  Simplification rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Subsume      : 7
% 3.23/1.48  #Demod        : 246
% 3.23/1.48  #Tautology    : 109
% 3.23/1.48  #SimpNegUnit  : 1
% 3.23/1.48  #BackRed      : 39
% 3.23/1.48  
% 3.23/1.48  #Partial instantiations: 0
% 3.23/1.48  #Strategies tried      : 1
% 3.23/1.48  
% 3.23/1.48  Timing (in seconds)
% 3.23/1.48  ----------------------
% 3.23/1.48  Preprocessing        : 0.34
% 3.23/1.48  Parsing              : 0.19
% 3.23/1.48  CNF conversion       : 0.02
% 3.23/1.48  Main loop            : 0.37
% 3.23/1.48  Inferencing          : 0.13
% 3.23/1.48  Reduction            : 0.13
% 3.23/1.48  Demodulation         : 0.09
% 3.23/1.48  BG Simplification    : 0.02
% 3.23/1.49  Subsumption          : 0.06
% 3.23/1.49  Abstraction          : 0.02
% 3.23/1.49  MUC search           : 0.00
% 3.23/1.49  Cooper               : 0.00
% 3.23/1.49  Total                : 0.74
% 3.23/1.49  Index Insertion      : 0.00
% 3.23/1.49  Index Deletion       : 0.00
% 3.23/1.49  Index Matching       : 0.00
% 3.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
