%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:44 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  275 (3198 expanded)
%              Number of leaves         :   36 ( 986 expanded)
%              Depth                    :   19
%              Number of atoms          :  433 (7735 expanded)
%              Number of equality atoms :  205 (2867 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_118,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_131,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_118])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_138,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_141,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_64,c_141])).

tff(c_146,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_199,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_251,plain,(
    ! [A_53] :
      ( k4_relat_1(A_53) = k2_funct_1(A_53)
      | ~ v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_254,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_251])).

tff(c_257,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_64,c_254])).

tff(c_291,plain,(
    ! [A_60,B_61,C_62] :
      ( k3_relset_1(A_60,B_61,C_62) = k4_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_298,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_291])).

tff(c_307,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_298])).

tff(c_328,plain,(
    ! [A_66,B_67,C_68] :
      ( m1_subset_1(k3_relset_1(A_66,B_67,C_68),k1_zfmisc_1(k2_zfmisc_1(B_67,A_66)))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_343,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_328])).

tff(c_355,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_343])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_355])).

tff(c_358,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3826,plain,(
    ! [A_319] :
      ( k4_relat_1(A_319) = k2_funct_1(A_319)
      | ~ v2_funct_1(A_319)
      | ~ v1_funct_1(A_319)
      | ~ v1_relat_1(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3829,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3826])).

tff(c_3832,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_64,c_3829])).

tff(c_424,plain,(
    ! [A_73] :
      ( k4_relat_1(A_73) = k2_funct_1(A_73)
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_427,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_424])).

tff(c_430,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_64,c_427])).

tff(c_1219,plain,(
    ! [A_140,B_141,C_142] :
      ( k3_relset_1(A_140,B_141,C_142) = k4_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1229,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1219])).

tff(c_1238,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_1229])).

tff(c_2096,plain,(
    ! [B_224,A_225,C_226] :
      ( k1_relset_1(B_224,A_225,k3_relset_1(A_225,B_224,C_226)) = k2_relset_1(A_225,B_224,C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2107,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2096])).

tff(c_2117,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_56,c_2107])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_359,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_978,plain,(
    ! [B_125,C_126,A_127] :
      ( k1_xboole_0 = B_125
      | v1_funct_2(C_126,A_127,B_125)
      | k1_relset_1(A_127,B_125,C_126) != A_127
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_990,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_359,c_978])).

tff(c_1009,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_990])).

tff(c_1015,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1009])).

tff(c_436,plain,(
    ! [A_74,B_75,C_76] :
      ( k3_relset_1(A_74,B_75,C_76) = k4_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_446,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_436])).

tff(c_456,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_446])).

tff(c_1094,plain,(
    ! [B_136,A_137,C_138] :
      ( k1_relset_1(B_136,A_137,k3_relset_1(A_137,B_136,C_138)) = k2_relset_1(A_137,B_136,C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1107,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1094])).

tff(c_1120,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_56,c_1107])).

tff(c_1122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1015,c_1120])).

tff(c_1123,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1009])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1154,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1152,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1123,c_12])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_367,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_359,c_16])).

tff(c_373,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_382,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_367,c_373])).

tff(c_435,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_1194,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1152,c_435])).

tff(c_1199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1154,c_1194])).

tff(c_1200,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_2200,plain,(
    ! [B_229,A_230,C_231] :
      ( k1_xboole_0 = B_229
      | k1_relset_1(A_230,B_229,C_231) = A_230
      | ~ v1_funct_2(C_231,A_230,B_229)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_230,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2209,plain,(
    ! [C_231] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1('#skF_2','#skF_1',C_231) = '#skF_2'
      | ~ v1_funct_2(C_231,'#skF_2','#skF_1')
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1200,c_2200])).

tff(c_2295,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2209])).

tff(c_2329,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2328,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_2295,c_14])).

tff(c_107,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_107])).

tff(c_383,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_373])).

tff(c_422,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_2399,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2328,c_422])).

tff(c_2404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_2399])).

tff(c_2406,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2209])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1894,plain,(
    ! [B_208,C_209,A_210] :
      ( k1_xboole_0 = B_208
      | v1_funct_2(C_209,A_210,B_208)
      | k1_relset_1(A_210,B_208,C_209) != A_210
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_210,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3720,plain,(
    ! [B_313,A_314,A_315] :
      ( k1_xboole_0 = B_313
      | v1_funct_2(A_314,A_315,B_313)
      | k1_relset_1(A_315,B_313,A_314) != A_315
      | ~ r1_tarski(A_314,k2_zfmisc_1(A_315,B_313)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1894])).

tff(c_3732,plain,(
    ! [A_314] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(A_314,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',A_314) != '#skF_2'
      | ~ r1_tarski(A_314,k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1200,c_3720])).

tff(c_3765,plain,(
    ! [A_316] :
      ( v1_funct_2(A_316,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',A_316) != '#skF_2'
      | ~ r1_tarski(A_316,k2_funct_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2406,c_3732])).

tff(c_3775,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_3765])).

tff(c_3784,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2117,c_3775])).

tff(c_3786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_3784])).

tff(c_3787,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_3790,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3787,c_60])).

tff(c_4853,plain,(
    ! [A_390,B_391,C_392] :
      ( k3_relset_1(A_390,B_391,C_392) = k4_relat_1(C_392)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_390,B_391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4904,plain,(
    ! [C_400] :
      ( k3_relset_1('#skF_1','#skF_2',C_400) = k4_relat_1(C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_4853])).

tff(c_4907,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3790,c_4904])).

tff(c_4913,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3832,c_4907])).

tff(c_5657,plain,(
    ! [B_459,A_460,C_461] :
      ( k1_relset_1(B_459,A_460,k3_relset_1(A_460,B_459,C_461)) = k2_relset_1(A_460,B_459,C_461)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(A_460,B_459))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5691,plain,(
    ! [C_464] :
      ( k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2',C_464)) = k2_relset_1('#skF_1','#skF_2',C_464)
      | ~ m1_subset_1(C_464,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_5657])).

tff(c_5697,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_3790,c_5691])).

tff(c_5705,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4913,c_5697])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4958,plain,(
    ! [A_405,B_406,C_407] :
      ( k2_relset_1(A_405,B_406,C_407) = k2_relat_1(C_407)
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(A_405,B_406))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5089,plain,(
    ! [A_424,B_425,A_426] :
      ( k2_relset_1(A_424,B_425,A_426) = k2_relat_1(A_426)
      | ~ r1_tarski(A_426,k2_zfmisc_1(A_424,B_425)) ) ),
    inference(resolution,[status(thm)],[c_18,c_4958])).

tff(c_5109,plain,(
    ! [A_424,B_425] : k2_relset_1(A_424,B_425,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_5089])).

tff(c_5112,plain,(
    ! [A_424,B_425] : k2_relset_1(A_424,B_425,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5109])).

tff(c_42,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_25,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_68,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_389,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_392,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_389])).

tff(c_396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_392])).

tff(c_398,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_5165,plain,(
    ! [A_432,B_433,A_434] :
      ( k3_relset_1(A_432,B_433,A_434) = k4_relat_1(A_434)
      | ~ r1_tarski(A_434,k2_zfmisc_1(A_432,B_433)) ) ),
    inference(resolution,[status(thm)],[c_18,c_4853])).

tff(c_5186,plain,(
    ! [A_432,B_433] : k3_relset_1(A_432,B_433,k2_zfmisc_1(A_432,B_433)) = k4_relat_1(k2_zfmisc_1(A_432,B_433)) ),
    inference(resolution,[status(thm)],[c_6,c_5165])).

tff(c_5291,plain,(
    ! [A_447,B_448,C_449] :
      ( m1_subset_1(k3_relset_1(A_447,B_448,C_449),k1_zfmisc_1(k2_zfmisc_1(B_448,A_447)))
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5327,plain,(
    ! [B_5,C_449] :
      ( m1_subset_1(k3_relset_1(B_5,k1_xboole_0,C_449),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(B_5,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_5291])).

tff(c_5561,plain,(
    ! [B_457,C_458] :
      ( m1_subset_1(k3_relset_1(B_457,k1_xboole_0,C_458),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5327])).

tff(c_5581,plain,(
    ! [A_432] :
      ( m1_subset_1(k4_relat_1(k2_zfmisc_1(A_432,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(k2_zfmisc_1(A_432,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5186,c_5561])).

tff(c_5594,plain,(
    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_12,c_12,c_5581])).

tff(c_5619,plain,(
    r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5594,c_16])).

tff(c_388,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_373])).

tff(c_5640,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5619,c_388])).

tff(c_5187,plain,(
    ! [A_432,B_433] : k3_relset_1(A_432,B_433,k1_xboole_0) = k4_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_5165])).

tff(c_5649,plain,(
    ! [A_432,B_433] : k3_relset_1(A_432,B_433,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5640,c_5187])).

tff(c_3850,plain,(
    ! [A_321,B_322,C_323] :
      ( k3_relset_1(A_321,B_322,C_323) = k4_relat_1(C_323)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3914,plain,(
    ! [C_333] :
      ( k3_relset_1('#skF_1','#skF_2',C_333) = k4_relat_1(C_333)
      | ~ m1_subset_1(C_333,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_3850])).

tff(c_3917,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3790,c_3914])).

tff(c_3923,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3832,c_3917])).

tff(c_4481,plain,(
    ! [B_372,A_373,C_374] :
      ( k1_relset_1(B_372,A_373,k3_relset_1(A_373,B_372,C_374)) = k2_relset_1(A_373,B_372,C_374)
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4504,plain,(
    ! [C_375] :
      ( k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2',C_375)) = k2_relset_1('#skF_1','#skF_2',C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_4481])).

tff(c_4513,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_3790,c_4504])).

tff(c_4521,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3923,c_4513])).

tff(c_4638,plain,(
    ! [B_380,C_381,A_382] :
      ( k1_xboole_0 = B_380
      | v1_funct_2(C_381,A_382,B_380)
      | k1_relset_1(A_382,B_380,C_381) != A_382
      | ~ m1_subset_1(C_381,k1_zfmisc_1(k2_zfmisc_1(A_382,B_380))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4650,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_359,c_4638])).

tff(c_4666,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4521,c_4650])).

tff(c_4667,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_4666])).

tff(c_4702,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_8])).

tff(c_4700,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_4667,c_12])).

tff(c_3849,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_4797,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4700,c_3849])).

tff(c_4802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4702,c_4797])).

tff(c_4803,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_5321,plain,(
    ! [C_449] :
      ( m1_subset_1(k3_relset_1('#skF_2','#skF_1',C_449),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_5291])).

tff(c_5873,plain,(
    ! [C_482] :
      ( m1_subset_1(k3_relset_1('#skF_2','#skF_1',C_482),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4803,c_5321])).

tff(c_5895,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5649,c_5873])).

tff(c_5913,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_5895])).

tff(c_5916,plain,(
    ~ r1_tarski(k1_xboole_0,k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_5913])).

tff(c_5920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5916])).

tff(c_5921,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5895])).

tff(c_5715,plain,(
    ! [B_465,A_466,C_467] :
      ( k2_relset_1(B_465,A_466,k3_relset_1(A_466,B_465,C_467)) = k1_relset_1(A_466,B_465,C_467)
      | ~ m1_subset_1(C_467,k1_zfmisc_1(k2_zfmisc_1(A_466,B_465))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5721,plain,(
    ! [C_467] :
      ( k2_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2',C_467)) = k1_relset_1('#skF_1','#skF_2',C_467)
      | ~ m1_subset_1(C_467,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_5715])).

tff(c_5925,plain,(
    k2_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2',k1_xboole_0)) = k1_relset_1('#skF_1','#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5921,c_5721])).

tff(c_5942,plain,(
    k1_relset_1('#skF_1','#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5112,c_5649,c_5925])).

tff(c_5402,plain,(
    ! [B_450,A_451,C_452] :
      ( k1_xboole_0 = B_450
      | k1_relset_1(A_451,B_450,C_452) = A_451
      | ~ v1_funct_2(C_452,A_451,B_450)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(A_451,B_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5411,plain,(
    ! [C_452] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_452) = '#skF_1'
      | ~ v1_funct_2(C_452,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_452,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_5402])).

tff(c_5443,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5411])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4815,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4803,c_10])).

tff(c_4841,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4815])).

tff(c_5460,plain,(
    k2_funct_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5443,c_4841])).

tff(c_5470,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5443,c_5443,c_14])).

tff(c_5556,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5470,c_4803])).

tff(c_5558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5460,c_5556])).

tff(c_6444,plain,(
    ! [C_513] :
      ( k1_relset_1('#skF_1','#skF_2',C_513) = '#skF_1'
      | ~ v1_funct_2(C_513,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_513,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_5411])).

tff(c_6447,plain,
    ( k1_relset_1('#skF_1','#skF_2',k1_xboole_0) = '#skF_1'
    | ~ v1_funct_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5921,c_6444])).

tff(c_6462,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v1_funct_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5942,c_6447])).

tff(c_6483,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6462])).

tff(c_5560,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5411])).

tff(c_5785,plain,(
    ! [B_473,C_474,A_475] :
      ( k1_xboole_0 = B_473
      | v1_funct_2(C_474,A_475,B_473)
      | k1_relset_1(A_475,B_473,C_474) != A_475
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_475,B_473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5794,plain,(
    ! [C_474] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_474,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_474) != '#skF_1'
      | ~ m1_subset_1(C_474,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_5785])).

tff(c_6566,plain,(
    ! [C_521] :
      ( v1_funct_2(C_521,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_521) != '#skF_1'
      | ~ m1_subset_1(C_521,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5560,c_5794])).

tff(c_6569,plain,
    ( v1_funct_2(k1_xboole_0,'#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2',k1_xboole_0) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_5921,c_6566])).

tff(c_6584,plain,
    ( v1_funct_2(k1_xboole_0,'#skF_1','#skF_2')
    | k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5942,c_6569])).

tff(c_6585,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_6483,c_6584])).

tff(c_7585,plain,(
    ! [B_580,A_581,A_582] :
      ( k1_xboole_0 = B_580
      | v1_funct_2(A_581,A_582,B_580)
      | k1_relset_1(A_582,B_580,A_581) != A_582
      | ~ r1_tarski(A_581,k2_zfmisc_1(A_582,B_580)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5785])).

tff(c_7591,plain,(
    ! [A_581] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(A_581,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',A_581) != '#skF_2'
      | ~ r1_tarski(A_581,k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4803,c_7585])).

tff(c_8409,plain,(
    ! [A_615] :
      ( v1_funct_2(A_615,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',A_615) != '#skF_2'
      | ~ r1_tarski(A_615,k2_funct_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6585,c_7591])).

tff(c_8422,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_8409])).

tff(c_8434,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5705,c_8422])).

tff(c_8436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_8434])).

tff(c_8437,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6462])).

tff(c_8474,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8437,c_4841])).

tff(c_8483,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8437,c_8437,c_12])).

tff(c_8635,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8483,c_4803])).

tff(c_8637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8474,c_8635])).

tff(c_8638,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4815])).

tff(c_8686,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8638])).

tff(c_3799,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_10])).

tff(c_3837,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3799])).

tff(c_8690,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8686,c_3837])).

tff(c_8699,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8686,c_8686,c_14])).

tff(c_8777,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8699,c_3787])).

tff(c_8779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8690,c_8777])).

tff(c_8780,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8638])).

tff(c_8785,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8780,c_3837])).

tff(c_8905,plain,(
    ! [A_634] : k2_zfmisc_1(A_634,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8780,c_8780,c_12])).

tff(c_8918,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8905,c_3787])).

tff(c_8935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8785,c_8918])).

tff(c_8937,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3799])).

tff(c_8946,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8937,c_8937,c_14])).

tff(c_8936,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3799])).

tff(c_8993,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8937,c_8937,c_8936])).

tff(c_8994,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8993])).

tff(c_8997,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8994,c_359])).

tff(c_9084,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8946,c_8997])).

tff(c_9093,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_9084,c_16])).

tff(c_8939,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8937,c_8937,c_388])).

tff(c_9102,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9093,c_8939])).

tff(c_9111,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_3832])).

tff(c_8947,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8937,c_8])).

tff(c_9137,plain,(
    ! [A_645,B_646,C_647] :
      ( k3_relset_1(A_645,B_646,C_647) = k4_relat_1(C_647)
      | ~ m1_subset_1(C_647,k1_zfmisc_1(k2_zfmisc_1(A_645,B_646))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9573,plain,(
    ! [A_715,B_716,A_717] :
      ( k3_relset_1(A_715,B_716,A_717) = k4_relat_1(A_717)
      | ~ r1_tarski(A_717,k2_zfmisc_1(A_715,B_716)) ) ),
    inference(resolution,[status(thm)],[c_18,c_9137])).

tff(c_9583,plain,(
    ! [A_715,B_716] : k3_relset_1(A_715,B_716,'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8947,c_9573])).

tff(c_9589,plain,(
    ! [A_715,B_716] : k3_relset_1(A_715,B_716,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9111,c_9583])).

tff(c_8948,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8937,c_8937,c_20])).

tff(c_8976,plain,(
    ! [A_636,B_637,C_638] :
      ( k2_relset_1(A_636,B_637,C_638) = k2_relat_1(C_638)
      | ~ m1_subset_1(C_638,k1_zfmisc_1(k2_zfmisc_1(A_636,B_637))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9517,plain,(
    ! [A_705,B_706,A_707] :
      ( k2_relset_1(A_705,B_706,A_707) = k2_relat_1(A_707)
      | ~ r1_tarski(A_707,k2_zfmisc_1(A_705,B_706)) ) ),
    inference(resolution,[status(thm)],[c_18,c_8976])).

tff(c_9527,plain,(
    ! [A_705,B_706] : k2_relset_1(A_705,B_706,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8947,c_9517])).

tff(c_9533,plain,(
    ! [A_705,B_706] : k2_relset_1(A_705,B_706,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8948,c_9527])).

tff(c_9421,plain,(
    ! [B_686,A_687,C_688] :
      ( k1_relset_1(B_686,A_687,k3_relset_1(A_687,B_686,C_688)) = k2_relset_1(A_687,B_686,C_688)
      | ~ m1_subset_1(C_688,k1_zfmisc_1(k2_zfmisc_1(A_687,B_686))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9961,plain,(
    ! [B_751,A_752,A_753] :
      ( k1_relset_1(B_751,A_752,k3_relset_1(A_752,B_751,A_753)) = k2_relset_1(A_752,B_751,A_753)
      | ~ r1_tarski(A_753,k2_zfmisc_1(A_752,B_751)) ) ),
    inference(resolution,[status(thm)],[c_18,c_9421])).

tff(c_9970,plain,(
    ! [B_751,A_752] : k1_relset_1(B_751,A_752,k3_relset_1(A_752,B_751,'#skF_3')) = k2_relset_1(A_752,B_751,'#skF_3') ),
    inference(resolution,[status(thm)],[c_8947,c_9961])).

tff(c_9976,plain,(
    ! [B_751,A_752] : k1_relset_1(B_751,A_752,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9589,c_9533,c_9970])).

tff(c_46,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_66,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_9289,plain,(
    ! [C_668,B_669] :
      ( v1_funct_2(C_668,'#skF_3',B_669)
      | k1_relset_1('#skF_3',B_669,C_668) != '#skF_3'
      | ~ m1_subset_1(C_668,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8937,c_8937,c_8937,c_8937,c_66])).

tff(c_9297,plain,(
    ! [B_670] :
      ( v1_funct_2('#skF_3','#skF_3',B_670)
      | k1_relset_1('#skF_3',B_670,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_3790,c_9289])).

tff(c_8998,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8994,c_358])).

tff(c_9110,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_8998])).

tff(c_9309,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_9297,c_9110])).

tff(c_9983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9976,c_9309])).

tff(c_9984,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8993])).

tff(c_9985,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8993])).

tff(c_10008,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9984,c_9985])).

tff(c_397,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25 ) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_8938,plain,(
    ! [A_25] :
      ( v1_funct_2('#skF_3',A_25,'#skF_3')
      | A_25 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8937,c_8937,c_8937,c_397])).

tff(c_10234,plain,(
    ! [A_767] :
      ( v1_funct_2('#skF_1',A_767,'#skF_1')
      | A_767 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9984,c_9984,c_9984,c_8938])).

tff(c_8945,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8937,c_8937,c_12])).

tff(c_10046,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9984,c_9984,c_8945])).

tff(c_9994,plain,(
    r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9984,c_367])).

tff(c_10175,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10046,c_9994])).

tff(c_10124,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9984,c_9984,c_8939])).

tff(c_10186,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10175,c_10124])).

tff(c_9997,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9984,c_358])).

tff(c_10206,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10186,c_9997])).

tff(c_10237,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10234,c_10206])).

tff(c_10243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10008,c_10237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:56:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.62/2.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.68  
% 7.62/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.68  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.62/2.68  
% 7.62/2.68  %Foreground sorts:
% 7.62/2.68  
% 7.62/2.68  
% 7.62/2.68  %Background operators:
% 7.62/2.68  
% 7.62/2.68  
% 7.62/2.68  %Foreground operators:
% 7.62/2.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.62/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.62/2.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.62/2.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.62/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.62/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.62/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.62/2.68  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 7.62/2.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.62/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.62/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.62/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.62/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.62/2.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.62/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.62/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.62/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.62/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.62/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.62/2.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.62/2.68  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.62/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.62/2.68  
% 8.03/2.71  tff(f_119, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.03/2.71  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.03/2.71  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.03/2.71  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 8.03/2.71  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 8.03/2.71  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 8.03/2.71  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relset_1)).
% 8.03/2.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.03/2.71  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.03/2.71  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.03/2.71  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.03/2.71  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.03/2.71  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.03/2.71  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.03/2.71  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.03/2.71  tff(c_118, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.03/2.71  tff(c_131, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_118])).
% 8.03/2.71  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.03/2.71  tff(c_26, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.03/2.71  tff(c_54, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.03/2.71  tff(c_138, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 8.03/2.71  tff(c_141, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_138])).
% 8.03/2.71  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_64, c_141])).
% 8.03/2.71  tff(c_146, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 8.03/2.71  tff(c_199, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_146])).
% 8.03/2.71  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.03/2.71  tff(c_251, plain, (![A_53]: (k4_relat_1(A_53)=k2_funct_1(A_53) | ~v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.03/2.71  tff(c_254, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_251])).
% 8.03/2.71  tff(c_257, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_64, c_254])).
% 8.03/2.71  tff(c_291, plain, (![A_60, B_61, C_62]: (k3_relset_1(A_60, B_61, C_62)=k4_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.03/2.71  tff(c_298, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_291])).
% 8.03/2.71  tff(c_307, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_298])).
% 8.03/2.71  tff(c_328, plain, (![A_66, B_67, C_68]: (m1_subset_1(k3_relset_1(A_66, B_67, C_68), k1_zfmisc_1(k2_zfmisc_1(B_67, A_66))) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.03/2.71  tff(c_343, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_307, c_328])).
% 8.03/2.71  tff(c_355, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_343])).
% 8.03/2.71  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_355])).
% 8.03/2.71  tff(c_358, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_146])).
% 8.03/2.71  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.03/2.71  tff(c_3826, plain, (![A_319]: (k4_relat_1(A_319)=k2_funct_1(A_319) | ~v2_funct_1(A_319) | ~v1_funct_1(A_319) | ~v1_relat_1(A_319))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.03/2.71  tff(c_3829, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_3826])).
% 8.03/2.71  tff(c_3832, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_64, c_3829])).
% 8.03/2.71  tff(c_424, plain, (![A_73]: (k4_relat_1(A_73)=k2_funct_1(A_73) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.03/2.71  tff(c_427, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_424])).
% 8.03/2.71  tff(c_430, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_64, c_427])).
% 8.03/2.71  tff(c_1219, plain, (![A_140, B_141, C_142]: (k3_relset_1(A_140, B_141, C_142)=k4_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.03/2.71  tff(c_1229, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1219])).
% 8.03/2.71  tff(c_1238, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_1229])).
% 8.03/2.72  tff(c_2096, plain, (![B_224, A_225, C_226]: (k1_relset_1(B_224, A_225, k3_relset_1(A_225, B_224, C_226))=k2_relset_1(A_225, B_224, C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.03/2.72  tff(c_2107, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_2096])).
% 8.03/2.72  tff(c_2117, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_56, c_2107])).
% 8.03/2.72  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.03/2.72  tff(c_359, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_146])).
% 8.03/2.72  tff(c_978, plain, (![B_125, C_126, A_127]: (k1_xboole_0=B_125 | v1_funct_2(C_126, A_127, B_125) | k1_relset_1(A_127, B_125, C_126)!=A_127 | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_125))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.03/2.72  tff(c_990, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_359, c_978])).
% 8.03/2.72  tff(c_1009, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_358, c_990])).
% 8.03/2.72  tff(c_1015, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_1009])).
% 8.03/2.72  tff(c_436, plain, (![A_74, B_75, C_76]: (k3_relset_1(A_74, B_75, C_76)=k4_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.03/2.72  tff(c_446, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_436])).
% 8.03/2.72  tff(c_456, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_446])).
% 8.03/2.72  tff(c_1094, plain, (![B_136, A_137, C_138]: (k1_relset_1(B_136, A_137, k3_relset_1(A_137, B_136, C_138))=k2_relset_1(A_137, B_136, C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.03/2.72  tff(c_1107, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_1094])).
% 8.03/2.72  tff(c_1120, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_456, c_56, c_1107])).
% 8.03/2.72  tff(c_1122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1015, c_1120])).
% 8.03/2.72  tff(c_1123, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1009])).
% 8.03/2.72  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.03/2.72  tff(c_1154, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_8])).
% 8.03/2.72  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/2.72  tff(c_1152, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1123, c_12])).
% 8.03/2.72  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.03/2.72  tff(c_367, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_359, c_16])).
% 8.03/2.72  tff(c_373, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.03/2.72  tff(c_382, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_367, c_373])).
% 8.03/2.72  tff(c_435, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_382])).
% 8.03/2.72  tff(c_1194, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1152, c_435])).
% 8.03/2.72  tff(c_1199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1154, c_1194])).
% 8.03/2.72  tff(c_1200, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_382])).
% 8.03/2.72  tff(c_2200, plain, (![B_229, A_230, C_231]: (k1_xboole_0=B_229 | k1_relset_1(A_230, B_229, C_231)=A_230 | ~v1_funct_2(C_231, A_230, B_229) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_230, B_229))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.03/2.72  tff(c_2209, plain, (![C_231]: (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', C_231)='#skF_2' | ~v1_funct_2(C_231, '#skF_2', '#skF_1') | ~m1_subset_1(C_231, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1200, c_2200])).
% 8.03/2.72  tff(c_2295, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2209])).
% 8.03/2.72  tff(c_2329, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2295, c_8])).
% 8.03/2.72  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/2.72  tff(c_2328, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2295, c_2295, c_14])).
% 8.03/2.72  tff(c_107, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.03/2.72  tff(c_115, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_107])).
% 8.03/2.72  tff(c_383, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_115, c_373])).
% 8.03/2.72  tff(c_422, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_383])).
% 8.03/2.72  tff(c_2399, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2328, c_422])).
% 8.03/2.72  tff(c_2404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2329, c_2399])).
% 8.03/2.72  tff(c_2406, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_2209])).
% 8.03/2.72  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.03/2.72  tff(c_1894, plain, (![B_208, C_209, A_210]: (k1_xboole_0=B_208 | v1_funct_2(C_209, A_210, B_208) | k1_relset_1(A_210, B_208, C_209)!=A_210 | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_210, B_208))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.03/2.72  tff(c_3720, plain, (![B_313, A_314, A_315]: (k1_xboole_0=B_313 | v1_funct_2(A_314, A_315, B_313) | k1_relset_1(A_315, B_313, A_314)!=A_315 | ~r1_tarski(A_314, k2_zfmisc_1(A_315, B_313)))), inference(resolution, [status(thm)], [c_18, c_1894])).
% 8.03/2.72  tff(c_3732, plain, (![A_314]: (k1_xboole_0='#skF_1' | v1_funct_2(A_314, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', A_314)!='#skF_2' | ~r1_tarski(A_314, k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1200, c_3720])).
% 8.03/2.72  tff(c_3765, plain, (![A_316]: (v1_funct_2(A_316, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', A_316)!='#skF_2' | ~r1_tarski(A_316, k2_funct_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_2406, c_3732])).
% 8.03/2.72  tff(c_3775, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_6, c_3765])).
% 8.03/2.72  tff(c_3784, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2117, c_3775])).
% 8.03/2.72  tff(c_3786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_358, c_3784])).
% 8.03/2.72  tff(c_3787, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_383])).
% 8.03/2.72  tff(c_3790, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3787, c_60])).
% 8.03/2.72  tff(c_4853, plain, (![A_390, B_391, C_392]: (k3_relset_1(A_390, B_391, C_392)=k4_relat_1(C_392) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_390, B_391))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.03/2.72  tff(c_4904, plain, (![C_400]: (k3_relset_1('#skF_1', '#skF_2', C_400)=k4_relat_1(C_400) | ~m1_subset_1(C_400, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_4853])).
% 8.03/2.72  tff(c_4907, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3790, c_4904])).
% 8.03/2.72  tff(c_4913, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3832, c_4907])).
% 8.03/2.72  tff(c_5657, plain, (![B_459, A_460, C_461]: (k1_relset_1(B_459, A_460, k3_relset_1(A_460, B_459, C_461))=k2_relset_1(A_460, B_459, C_461) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(A_460, B_459))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.03/2.72  tff(c_5691, plain, (![C_464]: (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', C_464))=k2_relset_1('#skF_1', '#skF_2', C_464) | ~m1_subset_1(C_464, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_5657])).
% 8.03/2.72  tff(c_5697, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_3790, c_5691])).
% 8.03/2.72  tff(c_5705, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4913, c_5697])).
% 8.03/2.72  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.03/2.72  tff(c_4958, plain, (![A_405, B_406, C_407]: (k2_relset_1(A_405, B_406, C_407)=k2_relat_1(C_407) | ~m1_subset_1(C_407, k1_zfmisc_1(k2_zfmisc_1(A_405, B_406))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.03/2.72  tff(c_5089, plain, (![A_424, B_425, A_426]: (k2_relset_1(A_424, B_425, A_426)=k2_relat_1(A_426) | ~r1_tarski(A_426, k2_zfmisc_1(A_424, B_425)))), inference(resolution, [status(thm)], [c_18, c_4958])).
% 8.03/2.72  tff(c_5109, plain, (![A_424, B_425]: (k2_relset_1(A_424, B_425, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_5089])).
% 8.03/2.72  tff(c_5112, plain, (![A_424, B_425]: (k2_relset_1(A_424, B_425, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5109])).
% 8.03/2.72  tff(c_42, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_25, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.03/2.72  tff(c_68, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 8.03/2.72  tff(c_389, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_68])).
% 8.03/2.72  tff(c_392, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_389])).
% 8.03/2.72  tff(c_396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_392])).
% 8.03/2.72  tff(c_398, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_68])).
% 8.03/2.72  tff(c_5165, plain, (![A_432, B_433, A_434]: (k3_relset_1(A_432, B_433, A_434)=k4_relat_1(A_434) | ~r1_tarski(A_434, k2_zfmisc_1(A_432, B_433)))), inference(resolution, [status(thm)], [c_18, c_4853])).
% 8.03/2.72  tff(c_5186, plain, (![A_432, B_433]: (k3_relset_1(A_432, B_433, k2_zfmisc_1(A_432, B_433))=k4_relat_1(k2_zfmisc_1(A_432, B_433)))), inference(resolution, [status(thm)], [c_6, c_5165])).
% 8.03/2.72  tff(c_5291, plain, (![A_447, B_448, C_449]: (m1_subset_1(k3_relset_1(A_447, B_448, C_449), k1_zfmisc_1(k2_zfmisc_1(B_448, A_447))) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.03/2.72  tff(c_5327, plain, (![B_5, C_449]: (m1_subset_1(k3_relset_1(B_5, k1_xboole_0, C_449), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(B_5, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_14, c_5291])).
% 8.03/2.72  tff(c_5561, plain, (![B_457, C_458]: (m1_subset_1(k3_relset_1(B_457, k1_xboole_0, C_458), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(C_458, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5327])).
% 8.03/2.72  tff(c_5581, plain, (![A_432]: (m1_subset_1(k4_relat_1(k2_zfmisc_1(A_432, k1_xboole_0)), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(A_432, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_5186, c_5561])).
% 8.03/2.72  tff(c_5594, plain, (m1_subset_1(k4_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_12, c_12, c_5581])).
% 8.03/2.72  tff(c_5619, plain, (r1_tarski(k4_relat_1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_5594, c_16])).
% 8.03/2.72  tff(c_388, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_373])).
% 8.03/2.72  tff(c_5640, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_5619, c_388])).
% 8.03/2.72  tff(c_5187, plain, (![A_432, B_433]: (k3_relset_1(A_432, B_433, k1_xboole_0)=k4_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_5165])).
% 8.03/2.72  tff(c_5649, plain, (![A_432, B_433]: (k3_relset_1(A_432, B_433, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5640, c_5187])).
% 8.03/2.72  tff(c_3850, plain, (![A_321, B_322, C_323]: (k3_relset_1(A_321, B_322, C_323)=k4_relat_1(C_323) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.03/2.72  tff(c_3914, plain, (![C_333]: (k3_relset_1('#skF_1', '#skF_2', C_333)=k4_relat_1(C_333) | ~m1_subset_1(C_333, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_3850])).
% 8.03/2.72  tff(c_3917, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3790, c_3914])).
% 8.03/2.72  tff(c_3923, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3832, c_3917])).
% 8.03/2.72  tff(c_4481, plain, (![B_372, A_373, C_374]: (k1_relset_1(B_372, A_373, k3_relset_1(A_373, B_372, C_374))=k2_relset_1(A_373, B_372, C_374) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_373, B_372))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.03/2.72  tff(c_4504, plain, (![C_375]: (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', C_375))=k2_relset_1('#skF_1', '#skF_2', C_375) | ~m1_subset_1(C_375, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_4481])).
% 8.03/2.72  tff(c_4513, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_3790, c_4504])).
% 8.03/2.72  tff(c_4521, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3923, c_4513])).
% 8.03/2.72  tff(c_4638, plain, (![B_380, C_381, A_382]: (k1_xboole_0=B_380 | v1_funct_2(C_381, A_382, B_380) | k1_relset_1(A_382, B_380, C_381)!=A_382 | ~m1_subset_1(C_381, k1_zfmisc_1(k2_zfmisc_1(A_382, B_380))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.03/2.72  tff(c_4650, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_359, c_4638])).
% 8.03/2.72  tff(c_4666, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4521, c_4650])).
% 8.03/2.72  tff(c_4667, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_358, c_4666])).
% 8.03/2.72  tff(c_4702, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_8])).
% 8.03/2.72  tff(c_4700, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_4667, c_12])).
% 8.03/2.72  tff(c_3849, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_382])).
% 8.03/2.72  tff(c_4797, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4700, c_3849])).
% 8.03/2.72  tff(c_4802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4702, c_4797])).
% 8.03/2.72  tff(c_4803, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_382])).
% 8.03/2.72  tff(c_5321, plain, (![C_449]: (m1_subset_1(k3_relset_1('#skF_2', '#skF_1', C_449), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_5291])).
% 8.03/2.72  tff(c_5873, plain, (![C_482]: (m1_subset_1(k3_relset_1('#skF_2', '#skF_1', C_482), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(C_482, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_4803, c_5321])).
% 8.03/2.72  tff(c_5895, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5649, c_5873])).
% 8.03/2.72  tff(c_5913, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_5895])).
% 8.03/2.72  tff(c_5916, plain, (~r1_tarski(k1_xboole_0, k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_5913])).
% 8.03/2.72  tff(c_5920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_5916])).
% 8.03/2.72  tff(c_5921, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5895])).
% 8.03/2.72  tff(c_5715, plain, (![B_465, A_466, C_467]: (k2_relset_1(B_465, A_466, k3_relset_1(A_466, B_465, C_467))=k1_relset_1(A_466, B_465, C_467) | ~m1_subset_1(C_467, k1_zfmisc_1(k2_zfmisc_1(A_466, B_465))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.03/2.72  tff(c_5721, plain, (![C_467]: (k2_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', C_467))=k1_relset_1('#skF_1', '#skF_2', C_467) | ~m1_subset_1(C_467, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_5715])).
% 8.03/2.72  tff(c_5925, plain, (k2_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', k1_xboole_0))=k1_relset_1('#skF_1', '#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_5921, c_5721])).
% 8.03/2.72  tff(c_5942, plain, (k1_relset_1('#skF_1', '#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5112, c_5649, c_5925])).
% 8.03/2.72  tff(c_5402, plain, (![B_450, A_451, C_452]: (k1_xboole_0=B_450 | k1_relset_1(A_451, B_450, C_452)=A_451 | ~v1_funct_2(C_452, A_451, B_450) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(A_451, B_450))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.03/2.72  tff(c_5411, plain, (![C_452]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_452)='#skF_1' | ~v1_funct_2(C_452, '#skF_1', '#skF_2') | ~m1_subset_1(C_452, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_5402])).
% 8.03/2.72  tff(c_5443, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_5411])).
% 8.03/2.72  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/2.72  tff(c_4815, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4803, c_10])).
% 8.03/2.72  tff(c_4841, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4815])).
% 8.03/2.72  tff(c_5460, plain, (k2_funct_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5443, c_4841])).
% 8.03/2.72  tff(c_5470, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5443, c_5443, c_14])).
% 8.03/2.72  tff(c_5556, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5470, c_4803])).
% 8.03/2.72  tff(c_5558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5460, c_5556])).
% 8.03/2.72  tff(c_6444, plain, (![C_513]: (k1_relset_1('#skF_1', '#skF_2', C_513)='#skF_1' | ~v1_funct_2(C_513, '#skF_1', '#skF_2') | ~m1_subset_1(C_513, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_5411])).
% 8.03/2.72  tff(c_6447, plain, (k1_relset_1('#skF_1', '#skF_2', k1_xboole_0)='#skF_1' | ~v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5921, c_6444])).
% 8.03/2.72  tff(c_6462, plain, (k1_xboole_0='#skF_1' | ~v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5942, c_6447])).
% 8.03/2.72  tff(c_6483, plain, (~v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_6462])).
% 8.03/2.72  tff(c_5560, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_5411])).
% 8.03/2.72  tff(c_5785, plain, (![B_473, C_474, A_475]: (k1_xboole_0=B_473 | v1_funct_2(C_474, A_475, B_473) | k1_relset_1(A_475, B_473, C_474)!=A_475 | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_475, B_473))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.03/2.72  tff(c_5794, plain, (![C_474]: (k1_xboole_0='#skF_2' | v1_funct_2(C_474, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_474)!='#skF_1' | ~m1_subset_1(C_474, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_5785])).
% 8.03/2.72  tff(c_6566, plain, (![C_521]: (v1_funct_2(C_521, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_521)!='#skF_1' | ~m1_subset_1(C_521, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_5560, c_5794])).
% 8.03/2.72  tff(c_6569, plain, (v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', k1_xboole_0)!='#skF_1'), inference(resolution, [status(thm)], [c_5921, c_6566])).
% 8.03/2.72  tff(c_6584, plain, (v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2') | k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5942, c_6569])).
% 8.03/2.72  tff(c_6585, plain, (k1_xboole_0!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_6483, c_6584])).
% 8.03/2.72  tff(c_7585, plain, (![B_580, A_581, A_582]: (k1_xboole_0=B_580 | v1_funct_2(A_581, A_582, B_580) | k1_relset_1(A_582, B_580, A_581)!=A_582 | ~r1_tarski(A_581, k2_zfmisc_1(A_582, B_580)))), inference(resolution, [status(thm)], [c_18, c_5785])).
% 8.03/2.72  tff(c_7591, plain, (![A_581]: (k1_xboole_0='#skF_1' | v1_funct_2(A_581, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', A_581)!='#skF_2' | ~r1_tarski(A_581, k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4803, c_7585])).
% 8.03/2.72  tff(c_8409, plain, (![A_615]: (v1_funct_2(A_615, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', A_615)!='#skF_2' | ~r1_tarski(A_615, k2_funct_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_6585, c_7591])).
% 8.03/2.72  tff(c_8422, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_6, c_8409])).
% 8.03/2.72  tff(c_8434, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5705, c_8422])).
% 8.03/2.72  tff(c_8436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_358, c_8434])).
% 8.03/2.72  tff(c_8437, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6462])).
% 8.03/2.72  tff(c_8474, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8437, c_4841])).
% 8.03/2.72  tff(c_8483, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8437, c_8437, c_12])).
% 8.03/2.72  tff(c_8635, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8483, c_4803])).
% 8.03/2.72  tff(c_8637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8474, c_8635])).
% 8.03/2.72  tff(c_8638, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4815])).
% 8.03/2.72  tff(c_8686, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_8638])).
% 8.03/2.72  tff(c_3799, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3787, c_10])).
% 8.03/2.72  tff(c_3837, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_3799])).
% 8.03/2.72  tff(c_8690, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8686, c_3837])).
% 8.03/2.72  tff(c_8699, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8686, c_8686, c_14])).
% 8.03/2.72  tff(c_8777, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8699, c_3787])).
% 8.03/2.72  tff(c_8779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8690, c_8777])).
% 8.03/2.72  tff(c_8780, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_8638])).
% 8.03/2.72  tff(c_8785, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8780, c_3837])).
% 8.03/2.72  tff(c_8905, plain, (![A_634]: (k2_zfmisc_1(A_634, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8780, c_8780, c_12])).
% 8.03/2.72  tff(c_8918, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8905, c_3787])).
% 8.03/2.72  tff(c_8935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8785, c_8918])).
% 8.03/2.72  tff(c_8937, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3799])).
% 8.03/2.72  tff(c_8946, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8937, c_8937, c_14])).
% 8.03/2.72  tff(c_8936, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3799])).
% 8.03/2.72  tff(c_8993, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8937, c_8937, c_8936])).
% 8.03/2.72  tff(c_8994, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_8993])).
% 8.03/2.72  tff(c_8997, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8994, c_359])).
% 8.03/2.72  tff(c_9084, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8946, c_8997])).
% 8.03/2.72  tff(c_9093, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_9084, c_16])).
% 8.03/2.72  tff(c_8939, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8937, c_8937, c_388])).
% 8.03/2.72  tff(c_9102, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_9093, c_8939])).
% 8.03/2.72  tff(c_9111, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_3832])).
% 8.03/2.72  tff(c_8947, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8937, c_8])).
% 8.03/2.72  tff(c_9137, plain, (![A_645, B_646, C_647]: (k3_relset_1(A_645, B_646, C_647)=k4_relat_1(C_647) | ~m1_subset_1(C_647, k1_zfmisc_1(k2_zfmisc_1(A_645, B_646))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.03/2.72  tff(c_9573, plain, (![A_715, B_716, A_717]: (k3_relset_1(A_715, B_716, A_717)=k4_relat_1(A_717) | ~r1_tarski(A_717, k2_zfmisc_1(A_715, B_716)))), inference(resolution, [status(thm)], [c_18, c_9137])).
% 8.03/2.72  tff(c_9583, plain, (![A_715, B_716]: (k3_relset_1(A_715, B_716, '#skF_3')=k4_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8947, c_9573])).
% 8.03/2.72  tff(c_9589, plain, (![A_715, B_716]: (k3_relset_1(A_715, B_716, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9111, c_9583])).
% 8.03/2.72  tff(c_8948, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8937, c_8937, c_20])).
% 8.03/2.72  tff(c_8976, plain, (![A_636, B_637, C_638]: (k2_relset_1(A_636, B_637, C_638)=k2_relat_1(C_638) | ~m1_subset_1(C_638, k1_zfmisc_1(k2_zfmisc_1(A_636, B_637))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.03/2.72  tff(c_9517, plain, (![A_705, B_706, A_707]: (k2_relset_1(A_705, B_706, A_707)=k2_relat_1(A_707) | ~r1_tarski(A_707, k2_zfmisc_1(A_705, B_706)))), inference(resolution, [status(thm)], [c_18, c_8976])).
% 8.03/2.72  tff(c_9527, plain, (![A_705, B_706]: (k2_relset_1(A_705, B_706, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8947, c_9517])).
% 8.03/2.72  tff(c_9533, plain, (![A_705, B_706]: (k2_relset_1(A_705, B_706, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8948, c_9527])).
% 8.03/2.72  tff(c_9421, plain, (![B_686, A_687, C_688]: (k1_relset_1(B_686, A_687, k3_relset_1(A_687, B_686, C_688))=k2_relset_1(A_687, B_686, C_688) | ~m1_subset_1(C_688, k1_zfmisc_1(k2_zfmisc_1(A_687, B_686))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.03/2.72  tff(c_9961, plain, (![B_751, A_752, A_753]: (k1_relset_1(B_751, A_752, k3_relset_1(A_752, B_751, A_753))=k2_relset_1(A_752, B_751, A_753) | ~r1_tarski(A_753, k2_zfmisc_1(A_752, B_751)))), inference(resolution, [status(thm)], [c_18, c_9421])).
% 8.03/2.72  tff(c_9970, plain, (![B_751, A_752]: (k1_relset_1(B_751, A_752, k3_relset_1(A_752, B_751, '#skF_3'))=k2_relset_1(A_752, B_751, '#skF_3'))), inference(resolution, [status(thm)], [c_8947, c_9961])).
% 8.03/2.72  tff(c_9976, plain, (![B_751, A_752]: (k1_relset_1(B_751, A_752, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9589, c_9533, c_9970])).
% 8.03/2.72  tff(c_46, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.03/2.72  tff(c_66, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 8.03/2.72  tff(c_9289, plain, (![C_668, B_669]: (v1_funct_2(C_668, '#skF_3', B_669) | k1_relset_1('#skF_3', B_669, C_668)!='#skF_3' | ~m1_subset_1(C_668, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8937, c_8937, c_8937, c_8937, c_66])).
% 8.03/2.72  tff(c_9297, plain, (![B_670]: (v1_funct_2('#skF_3', '#skF_3', B_670) | k1_relset_1('#skF_3', B_670, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_3790, c_9289])).
% 8.03/2.72  tff(c_8998, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8994, c_358])).
% 8.03/2.72  tff(c_9110, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_8998])).
% 8.03/2.72  tff(c_9309, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_9297, c_9110])).
% 8.03/2.72  tff(c_9983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9976, c_9309])).
% 8.03/2.72  tff(c_9984, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_8993])).
% 8.03/2.72  tff(c_9985, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_8993])).
% 8.03/2.72  tff(c_10008, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9984, c_9985])).
% 8.03/2.72  tff(c_397, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25)), inference(splitRight, [status(thm)], [c_68])).
% 8.03/2.72  tff(c_8938, plain, (![A_25]: (v1_funct_2('#skF_3', A_25, '#skF_3') | A_25='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8937, c_8937, c_8937, c_397])).
% 8.03/2.72  tff(c_10234, plain, (![A_767]: (v1_funct_2('#skF_1', A_767, '#skF_1') | A_767='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9984, c_9984, c_9984, c_8938])).
% 8.03/2.72  tff(c_8945, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8937, c_8937, c_12])).
% 8.03/2.72  tff(c_10046, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9984, c_9984, c_8945])).
% 8.03/2.72  tff(c_9994, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9984, c_367])).
% 8.03/2.72  tff(c_10175, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10046, c_9994])).
% 8.03/2.72  tff(c_10124, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9984, c_9984, c_8939])).
% 8.03/2.72  tff(c_10186, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_10175, c_10124])).
% 8.03/2.72  tff(c_9997, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9984, c_358])).
% 8.03/2.72  tff(c_10206, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10186, c_9997])).
% 8.03/2.72  tff(c_10237, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_10234, c_10206])).
% 8.03/2.72  tff(c_10243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10008, c_10237])).
% 8.03/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.72  
% 8.03/2.72  Inference rules
% 8.03/2.72  ----------------------
% 8.03/2.72  #Ref     : 0
% 8.03/2.72  #Sup     : 2336
% 8.03/2.72  #Fact    : 0
% 8.03/2.72  #Define  : 0
% 8.03/2.72  #Split   : 29
% 8.03/2.72  #Chain   : 0
% 8.03/2.72  #Close   : 0
% 8.03/2.72  
% 8.03/2.72  Ordering : KBO
% 8.03/2.72  
% 8.03/2.72  Simplification rules
% 8.03/2.72  ----------------------
% 8.03/2.72  #Subsume      : 139
% 8.03/2.72  #Demod        : 2592
% 8.03/2.72  #Tautology    : 1333
% 8.03/2.72  #SimpNegUnit  : 29
% 8.03/2.72  #BackRed      : 373
% 8.03/2.72  
% 8.03/2.72  #Partial instantiations: 0
% 8.03/2.72  #Strategies tried      : 1
% 8.03/2.72  
% 8.03/2.72  Timing (in seconds)
% 8.03/2.72  ----------------------
% 8.03/2.72  Preprocessing        : 0.33
% 8.03/2.72  Parsing              : 0.17
% 8.03/2.72  CNF conversion       : 0.02
% 8.03/2.72  Main loop            : 1.56
% 8.03/2.72  Inferencing          : 0.48
% 8.03/2.72  Reduction            : 0.58
% 8.03/2.72  Demodulation         : 0.41
% 8.03/2.72  BG Simplification    : 0.06
% 8.03/2.72  Subsumption          : 0.30
% 8.03/2.72  Abstraction          : 0.07
% 8.03/2.72  MUC search           : 0.00
% 8.03/2.72  Cooper               : 0.00
% 8.03/2.72  Total                : 1.98
% 8.03/2.72  Index Insertion      : 0.00
% 8.03/2.72  Index Deletion       : 0.00
% 8.03/2.72  Index Matching       : 0.00
% 8.03/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
