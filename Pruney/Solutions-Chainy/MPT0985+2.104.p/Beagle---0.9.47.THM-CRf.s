%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:43 EST 2020

% Result     : Theorem 5.27s
% Output     : CNFRefutation 5.68s
% Verified   : 
% Statistics : Number of formulae       :  236 (2872 expanded)
%              Number of leaves         :   35 ( 917 expanded)
%              Depth                    :   20
%              Number of atoms          :  417 (7471 expanded)
%              Number of equality atoms :  137 (1448 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_137,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_146,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_137])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2471,plain,(
    ! [A_235,B_236,C_237] :
      ( k2_relset_1(A_235,B_236,C_237) = k2_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2484,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2471])).

tff(c_2489,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2484])).

tff(c_22,plain,(
    ! [A_8] :
      ( k1_relat_1(k2_funct_1(A_8)) = k2_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    ! [A_35] :
      ( v1_funct_1(k2_funct_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_76,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_91,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_76])).

tff(c_94,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_91])).

tff(c_105,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_112,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_105])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_112])).

tff(c_118,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_151,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_300,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_310,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_300])).

tff(c_314,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_310])).

tff(c_18,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_119,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_201,plain,(
    ! [A_59] :
      ( k1_relat_1(k2_funct_1(A_59)) = k2_relat_1(A_59)
      | ~ v2_funct_1(A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [A_25] :
      ( v1_funct_2(A_25,k1_relat_1(A_25),k2_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_781,plain,(
    ! [A_120] :
      ( v1_funct_2(k2_funct_1(A_120),k2_relat_1(A_120),k2_relat_1(k2_funct_1(A_120)))
      | ~ v1_funct_1(k2_funct_1(A_120))
      | ~ v1_relat_1(k2_funct_1(A_120))
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_46])).

tff(c_790,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_781])).

tff(c_798,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_54,c_119,c_790])).

tff(c_799,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_798])).

tff(c_802,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_799])).

tff(c_806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_802])).

tff(c_808,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_798])).

tff(c_14,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) = k1_xboole_0
      | k1_relat_1(A_6) != k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_150,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_14])).

tff(c_152,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_168,plain,(
    ! [A_54] :
      ( k1_relat_1(A_54) = k1_xboole_0
      | k2_relat_1(A_54) != k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_171,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_168])).

tff(c_177,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_171])).

tff(c_315,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_177])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_282,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_295,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_282])).

tff(c_561,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_574,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_561])).

tff(c_583,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_295,c_574])).

tff(c_584,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_583])).

tff(c_20,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_243,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_65),k2_relat_1(A_65))))
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_931,plain,(
    ! [A_127] :
      ( m1_subset_1(k2_funct_1(A_127),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_127)),k1_relat_1(A_127))))
      | ~ v1_funct_1(k2_funct_1(A_127))
      | ~ v1_relat_1(k2_funct_1(A_127))
      | ~ v2_funct_1(A_127)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_243])).

tff(c_961,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_931])).

tff(c_976,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_54,c_808,c_119,c_961])).

tff(c_1003,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_976])).

tff(c_1020,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_54,c_314,c_1003])).

tff(c_1022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_1020])).

tff(c_1023,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_1024,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_1431,plain,(
    ! [A_155] :
      ( m1_subset_1(A_155,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_155),k2_relat_1(A_155))))
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1455,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_1431])).

tff(c_1467,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_1023,c_1455])).

tff(c_26,plain,(
    ! [C_15,A_12,B_13] :
      ( v1_xboole_0(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1472,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1467,c_26])).

tff(c_1481,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1472])).

tff(c_66,plain,(
    ! [B_27,A_28] :
      ( ~ v1_xboole_0(B_27)
      | B_27 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_2,c_66])).

tff(c_1490,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1481,c_69])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1504,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_4])).

tff(c_1128,plain,(
    ! [A_141] :
      ( m1_subset_1(A_141,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_141),k2_relat_1(A_141))))
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1146,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_1128])).

tff(c_1154,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_1023,c_1146])).

tff(c_1159,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1154,c_26])).

tff(c_1168,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1159])).

tff(c_1177,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1168,c_69])).

tff(c_1186,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_1024])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1037,plain,(
    ! [A_128,A_129,B_130] :
      ( v1_relat_1(A_128)
      | ~ r1_tarski(A_128,k2_zfmisc_1(A_129,B_130)) ) ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_1047,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_1037])).

tff(c_1051,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1047,c_14])).

tff(c_1052,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1051])).

tff(c_1184,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_1177,c_1052])).

tff(c_1241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_1184])).

tff(c_1243,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1051])).

tff(c_1496,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1490,c_1243])).

tff(c_1312,plain,(
    ! [A_151] :
      ( k2_relat_1(k2_funct_1(A_151)) = k1_relat_1(A_151)
      | ~ v2_funct_1(A_151)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2087,plain,(
    ! [A_214] :
      ( v1_funct_2(k2_funct_1(A_214),k1_relat_1(k2_funct_1(A_214)),k1_relat_1(A_214))
      | ~ v1_funct_1(k2_funct_1(A_214))
      | ~ v1_relat_1(k2_funct_1(A_214))
      | ~ v2_funct_1(A_214)
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1312,c_46])).

tff(c_2090,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_2087])).

tff(c_2098,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_54,c_119,c_2090])).

tff(c_2099,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2098])).

tff(c_2102,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_2099])).

tff(c_2106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_2102])).

tff(c_2108,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2098])).

tff(c_12,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) = k1_xboole_0
      | k2_relat_1(A_6) != k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1498,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) = '#skF_3'
      | k2_relat_1(A_6) != '#skF_3'
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1490,c_12])).

tff(c_2116,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2108,c_1498])).

tff(c_2173,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2116])).

tff(c_2179,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2173])).

tff(c_2185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_54,c_1496,c_2179])).

tff(c_2186,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2116])).

tff(c_1459,plain,(
    ! [A_155] :
      ( v1_xboole_0(A_155)
      | ~ v1_xboole_0(k1_relat_1(A_155))
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(resolution,[status(thm)],[c_1431,c_26])).

tff(c_2232,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_1459])).

tff(c_2267,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2108,c_119,c_1481,c_2232])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1491,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_1481,c_6])).

tff(c_2285,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2267,c_1491])).

tff(c_1242,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1051])).

tff(c_1497,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1490,c_1242])).

tff(c_1630,plain,(
    ! [A_163,B_164,C_165] :
      ( k2_relset_1(A_163,B_164,C_165) = k2_relat_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1643,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1630])).

tff(c_1649,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1497,c_52,c_1643])).

tff(c_1036,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_151])).

tff(c_1651,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1036])).

tff(c_2292,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2285,c_1651])).

tff(c_2300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1504,c_2292])).

tff(c_2301,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_2303,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_2316,plain,(
    ! [A_217] :
      ( k1_relat_1(A_217) = k1_xboole_0
      | k2_relat_1(A_217) != k1_xboole_0
      | ~ v1_relat_1(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2322,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_2316])).

tff(c_2329,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2303,c_2322])).

tff(c_2490,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2489,c_2329])).

tff(c_2520,plain,(
    ! [A_238,B_239,C_240] :
      ( k1_relset_1(A_238,B_239,C_240) = k1_relat_1(C_240)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2537,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2520])).

tff(c_2797,plain,(
    ! [B_267,A_268,C_269] :
      ( k1_xboole_0 = B_267
      | k1_relset_1(A_268,B_267,C_269) = A_268
      | ~ v1_funct_2(C_269,A_268,B_267)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_268,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2813,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2797])).

tff(c_2824,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2537,c_2813])).

tff(c_2825,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2490,c_2824])).

tff(c_2833,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2825,c_2303])).

tff(c_2302,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_2535,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2302,c_2520])).

tff(c_2884,plain,(
    ! [B_271,C_272,A_273] :
      ( k1_xboole_0 = B_271
      | v1_funct_2(C_272,A_273,B_271)
      | k1_relset_1(A_273,B_271,C_272) != A_273
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_273,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2890,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2302,c_2884])).

tff(c_2900,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2535,c_2890])).

tff(c_2901,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2301,c_2833,c_2900])).

tff(c_2909,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2901])).

tff(c_2912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_54,c_2489,c_2909])).

tff(c_2913,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_2914,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_3761,plain,(
    ! [A_336] :
      ( m1_subset_1(A_336,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_336),k2_relat_1(A_336))))
      | ~ v1_funct_1(A_336)
      | ~ v1_relat_1(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3791,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2914,c_3761])).

tff(c_3807,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_2913,c_3791])).

tff(c_3812,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3807,c_26])).

tff(c_3821,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3812])).

tff(c_3830,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3821,c_69])).

tff(c_3845,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3830,c_2913])).

tff(c_3857,plain,(
    ! [A_337,B_338,C_339] :
      ( k2_relset_1(A_337,B_338,C_339) = k2_relat_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3870,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_3857])).

tff(c_3875,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3870])).

tff(c_3904,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3845,c_3875])).

tff(c_3676,plain,(
    ! [C_326,A_327,B_328] :
      ( v1_xboole_0(C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328)))
      | ~ v1_xboole_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3687,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2302,c_3676])).

tff(c_3691,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3687])).

tff(c_3919,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3904,c_3691])).

tff(c_3929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3821,c_3919])).

tff(c_3931,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3687])).

tff(c_3937,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3931,c_69])).

tff(c_3950,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3937,c_2913])).

tff(c_3949,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3937,c_2914])).

tff(c_4096,plain,(
    ! [A_344] :
      ( m1_subset_1(A_344,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_344),k2_relat_1(A_344))))
      | ~ v1_funct_1(A_344)
      | ~ v1_relat_1(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4117,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3949,c_4096])).

tff(c_4132,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_3950,c_4117])).

tff(c_4139,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4132,c_26])).

tff(c_4148,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3931,c_4139])).

tff(c_3938,plain,(
    ! [A_2] :
      ( A_2 = '#skF_2'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_3931,c_6])).

tff(c_4158,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4148,c_3938])).

tff(c_3930,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3687])).

tff(c_4000,plain,(
    ! [A_342] :
      ( A_342 = '#skF_2'
      | ~ v1_xboole_0(A_342) ) ),
    inference(resolution,[status(thm)],[c_3931,c_6])).

tff(c_4007,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3930,c_4000])).

tff(c_4032,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4007,c_2301])).

tff(c_4164,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4158,c_4158,c_4032])).

tff(c_3168,plain,(
    ! [A_297] :
      ( m1_subset_1(A_297,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_297),k2_relat_1(A_297))))
      | ~ v1_funct_1(A_297)
      | ~ v1_relat_1(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3192,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2914,c_3168])).

tff(c_3204,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_2913,c_3192])).

tff(c_3209,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3204,c_26])).

tff(c_3218,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3209])).

tff(c_3252,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3218,c_69])).

tff(c_3265,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3252,c_2913])).

tff(c_2935,plain,(
    ! [A_274,A_275,B_276] :
      ( v1_relat_1(A_274)
      | ~ r1_tarski(A_274,k2_zfmisc_1(A_275,B_276)) ) ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_2950,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_2935])).

tff(c_2954,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2950,c_14])).

tff(c_2955,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2954])).

tff(c_2956,plain,(
    ! [A_277] :
      ( k1_relat_1(A_277) = k1_xboole_0
      | k2_relat_1(A_277) != k1_xboole_0
      | ~ v1_relat_1(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2969,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2950,c_2956])).

tff(c_2975,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2955,c_2969])).

tff(c_3260,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3252,c_3252,c_2975])).

tff(c_3324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_3260])).

tff(c_3326,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2954])).

tff(c_3946,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3937,c_3937,c_3326])).

tff(c_4167,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4158,c_4158,c_3946])).

tff(c_4031,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4007,c_2302])).

tff(c_4162,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4158,c_4158,c_4031])).

tff(c_28,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_relset_1(A_16,B_17,C_18) = k1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4377,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4162,c_28])).

tff(c_4391,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4167,c_4377])).

tff(c_4174,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4158,c_3937])).

tff(c_36,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4434,plain,(
    ! [C_357,B_358] :
      ( v1_funct_2(C_357,'#skF_3',B_358)
      | k1_relset_1('#skF_3',B_358,C_357) != '#skF_3'
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_358))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4174,c_4174,c_4174,c_4174,c_36])).

tff(c_4437,plain,
    ( v1_funct_2('#skF_3','#skF_3','#skF_1')
    | k1_relset_1('#skF_3','#skF_1','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4162,c_4434])).

tff(c_4447,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4391,c_4437])).

tff(c_4449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4164,c_4447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.27/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/2.05  
% 5.27/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/2.05  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.27/2.05  
% 5.27/2.05  %Foreground sorts:
% 5.27/2.05  
% 5.27/2.05  
% 5.27/2.05  %Background operators:
% 5.27/2.05  
% 5.27/2.05  
% 5.27/2.05  %Foreground operators:
% 5.27/2.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.27/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.27/2.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.27/2.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.27/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.27/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.27/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.27/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.27/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.27/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.27/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.27/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.27/2.05  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.27/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.27/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.27/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.27/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.27/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.27/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.27/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.27/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.27/2.05  
% 5.68/2.08  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.68/2.08  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.68/2.08  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.68/2.08  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.68/2.08  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.68/2.08  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.68/2.08  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.68/2.08  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 5.68/2.08  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.68/2.08  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.68/2.08  tff(f_75, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.68/2.08  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.68/2.08  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.68/2.08  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.68/2.08  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.68/2.08  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.68/2.08  tff(c_137, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.68/2.08  tff(c_146, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_137])).
% 5.68/2.08  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.68/2.08  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.68/2.08  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.68/2.08  tff(c_2471, plain, (![A_235, B_236, C_237]: (k2_relset_1(A_235, B_236, C_237)=k2_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.68/2.08  tff(c_2484, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2471])).
% 5.68/2.08  tff(c_2489, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2484])).
% 5.68/2.08  tff(c_22, plain, (![A_8]: (k1_relat_1(k2_funct_1(A_8))=k2_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.68/2.08  tff(c_88, plain, (![A_35]: (v1_funct_1(k2_funct_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.68/2.08  tff(c_50, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.68/2.08  tff(c_76, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.68/2.08  tff(c_91, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_76])).
% 5.68/2.08  tff(c_94, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_91])).
% 5.68/2.08  tff(c_105, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.68/2.08  tff(c_112, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_105])).
% 5.68/2.08  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_112])).
% 5.68/2.08  tff(c_118, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 5.68/2.08  tff(c_151, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_118])).
% 5.68/2.08  tff(c_300, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.68/2.08  tff(c_310, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_300])).
% 5.68/2.08  tff(c_314, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_310])).
% 5.68/2.08  tff(c_18, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.68/2.08  tff(c_119, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 5.68/2.08  tff(c_201, plain, (![A_59]: (k1_relat_1(k2_funct_1(A_59))=k2_relat_1(A_59) | ~v2_funct_1(A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.68/2.08  tff(c_46, plain, (![A_25]: (v1_funct_2(A_25, k1_relat_1(A_25), k2_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.68/2.08  tff(c_781, plain, (![A_120]: (v1_funct_2(k2_funct_1(A_120), k2_relat_1(A_120), k2_relat_1(k2_funct_1(A_120))) | ~v1_funct_1(k2_funct_1(A_120)) | ~v1_relat_1(k2_funct_1(A_120)) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_201, c_46])).
% 5.68/2.08  tff(c_790, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_314, c_781])).
% 5.68/2.08  tff(c_798, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_54, c_119, c_790])).
% 5.68/2.08  tff(c_799, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_798])).
% 5.68/2.08  tff(c_802, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_799])).
% 5.68/2.08  tff(c_806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_802])).
% 5.68/2.08  tff(c_808, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_798])).
% 5.68/2.08  tff(c_14, plain, (![A_6]: (k2_relat_1(A_6)=k1_xboole_0 | k1_relat_1(A_6)!=k1_xboole_0 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.68/2.08  tff(c_150, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_146, c_14])).
% 5.68/2.08  tff(c_152, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_150])).
% 5.68/2.08  tff(c_168, plain, (![A_54]: (k1_relat_1(A_54)=k1_xboole_0 | k2_relat_1(A_54)!=k1_xboole_0 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.68/2.08  tff(c_171, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_146, c_168])).
% 5.68/2.08  tff(c_177, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_152, c_171])).
% 5.68/2.08  tff(c_315, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_177])).
% 5.68/2.08  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.68/2.08  tff(c_282, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.68/2.08  tff(c_295, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_282])).
% 5.68/2.08  tff(c_561, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.68/2.08  tff(c_574, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_561])).
% 5.68/2.08  tff(c_583, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_295, c_574])).
% 5.68/2.08  tff(c_584, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_315, c_583])).
% 5.68/2.08  tff(c_20, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.68/2.08  tff(c_243, plain, (![A_65]: (m1_subset_1(A_65, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_65), k2_relat_1(A_65)))) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.68/2.08  tff(c_931, plain, (![A_127]: (m1_subset_1(k2_funct_1(A_127), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_127)), k1_relat_1(A_127)))) | ~v1_funct_1(k2_funct_1(A_127)) | ~v1_relat_1(k2_funct_1(A_127)) | ~v2_funct_1(A_127) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_20, c_243])).
% 5.68/2.08  tff(c_961, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_584, c_931])).
% 5.68/2.08  tff(c_976, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_54, c_808, c_119, c_961])).
% 5.68/2.08  tff(c_1003, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_976])).
% 5.68/2.08  tff(c_1020, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_54, c_314, c_1003])).
% 5.68/2.08  tff(c_1022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_1020])).
% 5.68/2.08  tff(c_1023, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_150])).
% 5.68/2.08  tff(c_1024, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_150])).
% 5.68/2.08  tff(c_1431, plain, (![A_155]: (m1_subset_1(A_155, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_155), k2_relat_1(A_155)))) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.68/2.08  tff(c_1455, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1024, c_1431])).
% 5.68/2.08  tff(c_1467, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_1023, c_1455])).
% 5.68/2.08  tff(c_26, plain, (![C_15, A_12, B_13]: (v1_xboole_0(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.68/2.08  tff(c_1472, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1467, c_26])).
% 5.68/2.08  tff(c_1481, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1472])).
% 5.68/2.08  tff(c_66, plain, (![B_27, A_28]: (~v1_xboole_0(B_27) | B_27=A_28 | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.68/2.08  tff(c_69, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_2, c_66])).
% 5.68/2.08  tff(c_1490, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1481, c_69])).
% 5.68/2.08  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.68/2.08  tff(c_1504, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_4])).
% 5.68/2.08  tff(c_1128, plain, (![A_141]: (m1_subset_1(A_141, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_141), k2_relat_1(A_141)))) | ~v1_funct_1(A_141) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.68/2.08  tff(c_1146, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1024, c_1128])).
% 5.68/2.08  tff(c_1154, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_1023, c_1146])).
% 5.68/2.08  tff(c_1159, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1154, c_26])).
% 5.68/2.08  tff(c_1168, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1159])).
% 5.68/2.08  tff(c_1177, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1168, c_69])).
% 5.68/2.08  tff(c_1186, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1177, c_1024])).
% 5.68/2.08  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.68/2.08  tff(c_1037, plain, (![A_128, A_129, B_130]: (v1_relat_1(A_128) | ~r1_tarski(A_128, k2_zfmisc_1(A_129, B_130)))), inference(resolution, [status(thm)], [c_10, c_137])).
% 5.68/2.08  tff(c_1047, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1037])).
% 5.68/2.08  tff(c_1051, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_1047, c_14])).
% 5.68/2.08  tff(c_1052, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1051])).
% 5.68/2.08  tff(c_1184, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1177, c_1177, c_1052])).
% 5.68/2.08  tff(c_1241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1186, c_1184])).
% 5.68/2.08  tff(c_1243, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_1051])).
% 5.68/2.08  tff(c_1496, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1490, c_1243])).
% 5.68/2.08  tff(c_1312, plain, (![A_151]: (k2_relat_1(k2_funct_1(A_151))=k1_relat_1(A_151) | ~v2_funct_1(A_151) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.68/2.08  tff(c_2087, plain, (![A_214]: (v1_funct_2(k2_funct_1(A_214), k1_relat_1(k2_funct_1(A_214)), k1_relat_1(A_214)) | ~v1_funct_1(k2_funct_1(A_214)) | ~v1_relat_1(k2_funct_1(A_214)) | ~v2_funct_1(A_214) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(superposition, [status(thm), theory('equality')], [c_1312, c_46])).
% 5.68/2.08  tff(c_2090, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1496, c_2087])).
% 5.68/2.08  tff(c_2098, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_54, c_119, c_2090])).
% 5.68/2.08  tff(c_2099, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2098])).
% 5.68/2.08  tff(c_2102, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_2099])).
% 5.68/2.08  tff(c_2106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_2102])).
% 5.68/2.08  tff(c_2108, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2098])).
% 5.68/2.08  tff(c_12, plain, (![A_6]: (k1_relat_1(A_6)=k1_xboole_0 | k2_relat_1(A_6)!=k1_xboole_0 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.68/2.08  tff(c_1498, plain, (![A_6]: (k1_relat_1(A_6)='#skF_3' | k2_relat_1(A_6)!='#skF_3' | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1490, c_12])).
% 5.68/2.08  tff(c_2116, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_2108, c_1498])).
% 5.68/2.08  tff(c_2173, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_2116])).
% 5.68/2.08  tff(c_2179, plain, (k1_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_2173])).
% 5.68/2.08  tff(c_2185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_54, c_1496, c_2179])).
% 5.68/2.08  tff(c_2186, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_2116])).
% 5.68/2.08  tff(c_1459, plain, (![A_155]: (v1_xboole_0(A_155) | ~v1_xboole_0(k1_relat_1(A_155)) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(resolution, [status(thm)], [c_1431, c_26])).
% 5.68/2.08  tff(c_2232, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2186, c_1459])).
% 5.68/2.08  tff(c_2267, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2108, c_119, c_1481, c_2232])).
% 5.68/2.08  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.68/2.08  tff(c_1491, plain, (![A_2]: (A_2='#skF_3' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_1481, c_6])).
% 5.68/2.08  tff(c_2285, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2267, c_1491])).
% 5.68/2.08  tff(c_1242, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_1051])).
% 5.68/2.08  tff(c_1497, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1490, c_1242])).
% 5.68/2.08  tff(c_1630, plain, (![A_163, B_164, C_165]: (k2_relset_1(A_163, B_164, C_165)=k2_relat_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.68/2.08  tff(c_1643, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1630])).
% 5.68/2.08  tff(c_1649, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1497, c_52, c_1643])).
% 5.68/2.08  tff(c_1036, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_10, c_151])).
% 5.68/2.08  tff(c_1651, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1036])).
% 5.68/2.08  tff(c_2292, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2285, c_1651])).
% 5.68/2.08  tff(c_2300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1504, c_2292])).
% 5.68/2.08  tff(c_2301, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_118])).
% 5.68/2.08  tff(c_2303, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_150])).
% 5.68/2.08  tff(c_2316, plain, (![A_217]: (k1_relat_1(A_217)=k1_xboole_0 | k2_relat_1(A_217)!=k1_xboole_0 | ~v1_relat_1(A_217))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.68/2.08  tff(c_2322, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_146, c_2316])).
% 5.68/2.08  tff(c_2329, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2303, c_2322])).
% 5.68/2.08  tff(c_2490, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2489, c_2329])).
% 5.68/2.08  tff(c_2520, plain, (![A_238, B_239, C_240]: (k1_relset_1(A_238, B_239, C_240)=k1_relat_1(C_240) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.68/2.08  tff(c_2537, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2520])).
% 5.68/2.08  tff(c_2797, plain, (![B_267, A_268, C_269]: (k1_xboole_0=B_267 | k1_relset_1(A_268, B_267, C_269)=A_268 | ~v1_funct_2(C_269, A_268, B_267) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_268, B_267))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.68/2.08  tff(c_2813, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_2797])).
% 5.68/2.08  tff(c_2824, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2537, c_2813])).
% 5.68/2.08  tff(c_2825, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2490, c_2824])).
% 5.68/2.08  tff(c_2833, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2825, c_2303])).
% 5.68/2.08  tff(c_2302, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_118])).
% 5.68/2.08  tff(c_2535, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2302, c_2520])).
% 5.68/2.08  tff(c_2884, plain, (![B_271, C_272, A_273]: (k1_xboole_0=B_271 | v1_funct_2(C_272, A_273, B_271) | k1_relset_1(A_273, B_271, C_272)!=A_273 | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_273, B_271))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.68/2.08  tff(c_2890, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2302, c_2884])).
% 5.68/2.08  tff(c_2900, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2535, c_2890])).
% 5.68/2.08  tff(c_2901, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2301, c_2833, c_2900])).
% 5.68/2.08  tff(c_2909, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_2901])).
% 5.68/2.08  tff(c_2912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_54, c_2489, c_2909])).
% 5.68/2.08  tff(c_2913, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_150])).
% 5.68/2.08  tff(c_2914, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_150])).
% 5.68/2.08  tff(c_3761, plain, (![A_336]: (m1_subset_1(A_336, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_336), k2_relat_1(A_336)))) | ~v1_funct_1(A_336) | ~v1_relat_1(A_336))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.68/2.08  tff(c_3791, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2914, c_3761])).
% 5.68/2.08  tff(c_3807, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_2913, c_3791])).
% 5.68/2.08  tff(c_3812, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_3807, c_26])).
% 5.68/2.08  tff(c_3821, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3812])).
% 5.68/2.08  tff(c_3830, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3821, c_69])).
% 5.68/2.08  tff(c_3845, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3830, c_2913])).
% 5.68/2.08  tff(c_3857, plain, (![A_337, B_338, C_339]: (k2_relset_1(A_337, B_338, C_339)=k2_relat_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.68/2.08  tff(c_3870, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_3857])).
% 5.68/2.08  tff(c_3875, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3870])).
% 5.68/2.08  tff(c_3904, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3845, c_3875])).
% 5.68/2.08  tff(c_3676, plain, (![C_326, A_327, B_328]: (v1_xboole_0(C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))) | ~v1_xboole_0(A_327))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.68/2.08  tff(c_3687, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_2302, c_3676])).
% 5.68/2.08  tff(c_3691, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3687])).
% 5.68/2.08  tff(c_3919, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3904, c_3691])).
% 5.68/2.08  tff(c_3929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3821, c_3919])).
% 5.68/2.08  tff(c_3931, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_3687])).
% 5.68/2.08  tff(c_3937, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3931, c_69])).
% 5.68/2.08  tff(c_3950, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3937, c_2913])).
% 5.68/2.08  tff(c_3949, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3937, c_2914])).
% 5.68/2.08  tff(c_4096, plain, (![A_344]: (m1_subset_1(A_344, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_344), k2_relat_1(A_344)))) | ~v1_funct_1(A_344) | ~v1_relat_1(A_344))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.68/2.08  tff(c_4117, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3949, c_4096])).
% 5.68/2.08  tff(c_4132, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_3950, c_4117])).
% 5.68/2.08  tff(c_4139, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4132, c_26])).
% 5.68/2.08  tff(c_4148, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3931, c_4139])).
% 5.68/2.08  tff(c_3938, plain, (![A_2]: (A_2='#skF_2' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_3931, c_6])).
% 5.68/2.08  tff(c_4158, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_4148, c_3938])).
% 5.68/2.08  tff(c_3930, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3687])).
% 5.68/2.08  tff(c_4000, plain, (![A_342]: (A_342='#skF_2' | ~v1_xboole_0(A_342))), inference(resolution, [status(thm)], [c_3931, c_6])).
% 5.68/2.08  tff(c_4007, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_3930, c_4000])).
% 5.68/2.08  tff(c_4032, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4007, c_2301])).
% 5.68/2.08  tff(c_4164, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4158, c_4158, c_4032])).
% 5.68/2.08  tff(c_3168, plain, (![A_297]: (m1_subset_1(A_297, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_297), k2_relat_1(A_297)))) | ~v1_funct_1(A_297) | ~v1_relat_1(A_297))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.68/2.08  tff(c_3192, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2914, c_3168])).
% 5.68/2.08  tff(c_3204, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_2913, c_3192])).
% 5.68/2.08  tff(c_3209, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_3204, c_26])).
% 5.68/2.08  tff(c_3218, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3209])).
% 5.68/2.08  tff(c_3252, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3218, c_69])).
% 5.68/2.08  tff(c_3265, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3252, c_2913])).
% 5.68/2.08  tff(c_2935, plain, (![A_274, A_275, B_276]: (v1_relat_1(A_274) | ~r1_tarski(A_274, k2_zfmisc_1(A_275, B_276)))), inference(resolution, [status(thm)], [c_10, c_137])).
% 5.68/2.08  tff(c_2950, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2935])).
% 5.68/2.08  tff(c_2954, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2950, c_14])).
% 5.68/2.08  tff(c_2955, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2954])).
% 5.68/2.08  tff(c_2956, plain, (![A_277]: (k1_relat_1(A_277)=k1_xboole_0 | k2_relat_1(A_277)!=k1_xboole_0 | ~v1_relat_1(A_277))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.68/2.08  tff(c_2969, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2950, c_2956])).
% 5.68/2.08  tff(c_2975, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2955, c_2969])).
% 5.68/2.08  tff(c_3260, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3252, c_3252, c_2975])).
% 5.68/2.08  tff(c_3324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3265, c_3260])).
% 5.68/2.08  tff(c_3326, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2954])).
% 5.68/2.08  tff(c_3946, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3937, c_3937, c_3326])).
% 5.68/2.08  tff(c_4167, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4158, c_4158, c_3946])).
% 5.68/2.08  tff(c_4031, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4007, c_2302])).
% 5.68/2.08  tff(c_4162, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4158, c_4158, c_4031])).
% 5.68/2.08  tff(c_28, plain, (![A_16, B_17, C_18]: (k1_relset_1(A_16, B_17, C_18)=k1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.68/2.08  tff(c_4377, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4162, c_28])).
% 5.68/2.08  tff(c_4391, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4167, c_4377])).
% 5.68/2.08  tff(c_4174, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4158, c_3937])).
% 5.68/2.08  tff(c_36, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.68/2.08  tff(c_4434, plain, (![C_357, B_358]: (v1_funct_2(C_357, '#skF_3', B_358) | k1_relset_1('#skF_3', B_358, C_357)!='#skF_3' | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_358))))), inference(demodulation, [status(thm), theory('equality')], [c_4174, c_4174, c_4174, c_4174, c_36])).
% 5.68/2.08  tff(c_4437, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_1') | k1_relset_1('#skF_3', '#skF_1', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_4162, c_4434])).
% 5.68/2.08  tff(c_4447, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4391, c_4437])).
% 5.68/2.08  tff(c_4449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4164, c_4447])).
% 5.68/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.08  
% 5.68/2.08  Inference rules
% 5.68/2.08  ----------------------
% 5.68/2.08  #Ref     : 0
% 5.68/2.08  #Sup     : 919
% 5.68/2.08  #Fact    : 0
% 5.68/2.08  #Define  : 0
% 5.68/2.08  #Split   : 37
% 5.68/2.08  #Chain   : 0
% 5.68/2.08  #Close   : 0
% 5.68/2.08  
% 5.68/2.08  Ordering : KBO
% 5.68/2.08  
% 5.68/2.08  Simplification rules
% 5.68/2.08  ----------------------
% 5.68/2.09  #Subsume      : 92
% 5.68/2.09  #Demod        : 1182
% 5.68/2.09  #Tautology    : 480
% 5.68/2.09  #SimpNegUnit  : 26
% 5.68/2.09  #BackRed      : 173
% 5.68/2.09  
% 5.68/2.09  #Partial instantiations: 0
% 5.68/2.09  #Strategies tried      : 1
% 5.68/2.09  
% 5.68/2.09  Timing (in seconds)
% 5.68/2.09  ----------------------
% 5.68/2.09  Preprocessing        : 0.33
% 5.68/2.09  Parsing              : 0.17
% 5.68/2.09  CNF conversion       : 0.02
% 5.68/2.09  Main loop            : 0.97
% 5.68/2.09  Inferencing          : 0.36
% 5.68/2.09  Reduction            : 0.32
% 5.68/2.09  Demodulation         : 0.22
% 5.68/2.09  BG Simplification    : 0.04
% 5.68/2.09  Subsumption          : 0.15
% 5.68/2.09  Abstraction          : 0.04
% 5.68/2.09  MUC search           : 0.00
% 5.68/2.09  Cooper               : 0.00
% 5.68/2.09  Total                : 1.36
% 5.68/2.09  Index Insertion      : 0.00
% 5.68/2.09  Index Deletion       : 0.00
% 5.68/2.09  Index Matching       : 0.00
% 5.68/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
