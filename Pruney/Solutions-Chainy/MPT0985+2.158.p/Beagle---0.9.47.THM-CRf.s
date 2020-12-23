%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:52 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  142 (1987 expanded)
%              Number of leaves         :   33 ( 682 expanded)
%              Depth                    :   15
%              Number of atoms          :  233 (5454 expanded)
%              Number of equality atoms :  103 (1587 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_113,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(c_48,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_75,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_78,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_81,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_78])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_83])).

tff(c_89,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_86])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_89])).

tff(c_92,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_115,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_95,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_95])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_98])).

tff(c_44,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_132,plain,(
    ! [A_38] :
      ( k4_relat_1(A_38) = k2_funct_1(A_38)
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_132])).

tff(c_138,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_50,c_135])).

tff(c_201,plain,(
    ! [A_50,B_51,C_52] :
      ( k3_relset_1(A_50,B_51,C_52) = k4_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_204,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_201])).

tff(c_206,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_204])).

tff(c_244,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k3_relset_1(A_57,B_58,C_59),k1_zfmisc_1(k2_zfmisc_1(B_58,A_57)))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_263,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_244])).

tff(c_272,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_263])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_272])).

tff(c_275,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_387,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_393,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_387])).

tff(c_397,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_393])).

tff(c_102,plain,(
    ! [A_36] :
      ( k1_relat_1(A_36) = k1_xboole_0
      | k2_relat_1(A_36) != k1_xboole_0
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_102])).

tff(c_287,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_400,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_287])).

tff(c_317,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_325,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_317])).

tff(c_566,plain,(
    ! [B_87,A_88,C_89] :
      ( k1_xboole_0 = B_87
      | k1_relset_1(A_88,B_87,C_89) = A_88
      | ~ v1_funct_2(C_89,A_88,B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_581,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_566])).

tff(c_591,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_325,c_581])).

tff(c_592,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_591])).

tff(c_289,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) = k1_xboole_0
      | k1_relat_1(A_60) != k1_xboole_0
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_295,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_289])).

tff(c_307,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_295])).

tff(c_596,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_307])).

tff(c_310,plain,(
    ! [A_61] :
      ( k4_relat_1(A_61) = k2_funct_1(A_61)
      | ~ v2_funct_1(A_61)
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_313,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_310])).

tff(c_316,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_50,c_313])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_329,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_8])).

tff(c_336,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_329])).

tff(c_276,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_324,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_276,c_317])).

tff(c_354,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_324])).

tff(c_398,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_354])).

tff(c_647,plain,(
    ! [B_90,C_91,A_92] :
      ( k1_xboole_0 = B_90
      | v1_funct_2(C_91,A_92,B_90)
      | k1_relset_1(A_92,B_90,C_91) != A_92
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_659,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_276,c_647])).

tff(c_672,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_659])).

tff(c_674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_596,c_672])).

tff(c_676,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_793,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_799,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_793])).

tff(c_803,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_676,c_799])).

tff(c_30,plain,(
    ! [C_24,A_22] :
      ( k1_xboole_0 = C_24
      | ~ v1_funct_2(C_24,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_932,plain,(
    ! [C_117,A_118] :
      ( C_117 = '#skF_2'
      | ~ v1_funct_2(C_117,A_118,'#skF_2')
      | A_118 = '#skF_2'
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,'#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_803,c_803,c_803,c_30])).

tff(c_935,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_932])).

tff(c_938,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_935])).

tff(c_939,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_938])).

tff(c_958,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_275])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_279,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_276,c_2])).

tff(c_282,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_279])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_relat_1(A_7) = k1_xboole_0
      | k2_relat_1(A_7) != k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_286,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_282,c_10])).

tff(c_704,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_685,plain,(
    ! [A_93] :
      ( k2_relat_1(A_93) = k1_xboole_0
      | k1_relat_1(A_93) != k1_xboole_0
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_698,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0
    | k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_282,c_685])).

tff(c_705,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_698])).

tff(c_706,plain,(
    ! [A_94] :
      ( k4_relat_1(A_94) = k2_funct_1(A_94)
      | ~ v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_709,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_706])).

tff(c_712,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_50,c_709])).

tff(c_716,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_8])).

tff(c_723,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_676,c_716])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_705,c_723])).

tff(c_726,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_774,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_777,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_276,c_774])).

tff(c_782,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_777])).

tff(c_804,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_782])).

tff(c_950,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_939,c_804])).

tff(c_957,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_276])).

tff(c_956,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_803])).

tff(c_32,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1225,plain,(
    ! [C_130,B_131] :
      ( v1_funct_2(C_130,'#skF_1',B_131)
      | k1_relset_1('#skF_1',B_131,C_130) != '#skF_1'
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_131))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_956,c_956,c_956,c_32])).

tff(c_1238,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_957,c_1225])).

tff(c_1247,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_1238])).

tff(c_1249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_958,c_1247])).

tff(c_1250,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_938])).

tff(c_1270,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_275])).

tff(c_1262,plain,(
    k1_relset_1('#skF_3','#skF_1',k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_1250,c_804])).

tff(c_1269,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_276])).

tff(c_1268,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_803])).

tff(c_1393,plain,(
    ! [C_135,B_136] :
      ( v1_funct_2(C_135,'#skF_3',B_136)
      | k1_relset_1('#skF_3',B_136,C_135) != '#skF_3'
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_136))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1268,c_1268,c_1268,c_1268,c_32])).

tff(c_1396,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1')
    | k1_relset_1('#skF_3','#skF_1',k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1269,c_1393])).

tff(c_1399,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_1396])).

tff(c_1401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1270,c_1399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:54:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.56  
% 3.47/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.56  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.47/1.56  
% 3.47/1.56  %Foreground sorts:
% 3.47/1.56  
% 3.47/1.56  
% 3.47/1.56  %Background operators:
% 3.47/1.56  
% 3.47/1.56  
% 3.47/1.56  %Foreground operators:
% 3.47/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.47/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.56  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.47/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.56  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.47/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.47/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.47/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.56  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.47/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.56  
% 3.47/1.59  tff(f_113, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.47/1.59  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.47/1.59  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.47/1.59  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.47/1.59  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.47/1.59  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 3.47/1.59  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 3.47/1.59  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.47/1.59  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.47/1.59  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.47/1.59  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.47/1.59  tff(f_40, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.47/1.59  tff(c_48, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.47/1.59  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.47/1.59  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.47/1.59  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.47/1.59  tff(c_16, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.47/1.59  tff(c_40, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.47/1.59  tff(c_75, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.47/1.59  tff(c_78, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_75])).
% 3.47/1.59  tff(c_81, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_78])).
% 3.47/1.59  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.47/1.59  tff(c_83, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.59  tff(c_86, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_83])).
% 3.47/1.59  tff(c_89, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_86])).
% 3.47/1.59  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_89])).
% 3.47/1.59  tff(c_92, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_40])).
% 3.47/1.59  tff(c_115, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_92])).
% 3.47/1.59  tff(c_95, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.59  tff(c_98, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_95])).
% 3.47/1.59  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_98])).
% 3.47/1.59  tff(c_44, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.47/1.59  tff(c_132, plain, (![A_38]: (k4_relat_1(A_38)=k2_funct_1(A_38) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.47/1.59  tff(c_135, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_132])).
% 3.47/1.59  tff(c_138, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_50, c_135])).
% 3.47/1.59  tff(c_201, plain, (![A_50, B_51, C_52]: (k3_relset_1(A_50, B_51, C_52)=k4_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.47/1.59  tff(c_204, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_201])).
% 3.47/1.59  tff(c_206, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_204])).
% 3.47/1.59  tff(c_244, plain, (![A_57, B_58, C_59]: (m1_subset_1(k3_relset_1(A_57, B_58, C_59), k1_zfmisc_1(k2_zfmisc_1(B_58, A_57))) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.47/1.59  tff(c_263, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_206, c_244])).
% 3.47/1.59  tff(c_272, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_263])).
% 3.47/1.59  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_272])).
% 3.47/1.59  tff(c_275, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_92])).
% 3.47/1.59  tff(c_387, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.47/1.59  tff(c_393, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_387])).
% 3.47/1.59  tff(c_397, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_393])).
% 3.47/1.59  tff(c_102, plain, (![A_36]: (k1_relat_1(A_36)=k1_xboole_0 | k2_relat_1(A_36)!=k1_xboole_0 | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.59  tff(c_112, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_102])).
% 3.47/1.59  tff(c_287, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_112])).
% 3.47/1.59  tff(c_400, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_397, c_287])).
% 3.47/1.59  tff(c_317, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.47/1.59  tff(c_325, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_317])).
% 3.47/1.59  tff(c_566, plain, (![B_87, A_88, C_89]: (k1_xboole_0=B_87 | k1_relset_1(A_88, B_87, C_89)=A_88 | ~v1_funct_2(C_89, A_88, B_87) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.47/1.59  tff(c_581, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_566])).
% 3.47/1.59  tff(c_591, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_325, c_581])).
% 3.47/1.59  tff(c_592, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_400, c_591])).
% 3.47/1.59  tff(c_289, plain, (![A_60]: (k2_relat_1(A_60)=k1_xboole_0 | k1_relat_1(A_60)!=k1_xboole_0 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.59  tff(c_295, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_289])).
% 3.47/1.59  tff(c_307, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_287, c_295])).
% 3.47/1.59  tff(c_596, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_592, c_307])).
% 3.47/1.59  tff(c_310, plain, (![A_61]: (k4_relat_1(A_61)=k2_funct_1(A_61) | ~v2_funct_1(A_61) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.47/1.59  tff(c_313, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_310])).
% 3.47/1.59  tff(c_316, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_50, c_313])).
% 3.47/1.59  tff(c_8, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.47/1.59  tff(c_329, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_316, c_8])).
% 3.47/1.59  tff(c_336, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_329])).
% 3.47/1.59  tff(c_276, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_92])).
% 3.47/1.59  tff(c_324, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_276, c_317])).
% 3.47/1.59  tff(c_354, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_324])).
% 3.47/1.59  tff(c_398, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_397, c_354])).
% 3.47/1.59  tff(c_647, plain, (![B_90, C_91, A_92]: (k1_xboole_0=B_90 | v1_funct_2(C_91, A_92, B_90) | k1_relset_1(A_92, B_90, C_91)!=A_92 | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_90))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.47/1.59  tff(c_659, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_276, c_647])).
% 3.47/1.59  tff(c_672, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_659])).
% 3.47/1.59  tff(c_674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_596, c_672])).
% 3.47/1.59  tff(c_676, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_112])).
% 3.47/1.59  tff(c_793, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.47/1.59  tff(c_799, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_793])).
% 3.47/1.59  tff(c_803, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_676, c_799])).
% 3.47/1.59  tff(c_30, plain, (![C_24, A_22]: (k1_xboole_0=C_24 | ~v1_funct_2(C_24, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.47/1.59  tff(c_932, plain, (![C_117, A_118]: (C_117='#skF_2' | ~v1_funct_2(C_117, A_118, '#skF_2') | A_118='#skF_2' | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_803, c_803, c_803, c_803, c_30])).
% 3.47/1.59  tff(c_935, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_46, c_932])).
% 3.47/1.59  tff(c_938, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_935])).
% 3.47/1.59  tff(c_939, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_938])).
% 3.47/1.59  tff(c_958, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_939, c_275])).
% 3.47/1.59  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.59  tff(c_279, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_276, c_2])).
% 3.47/1.59  tff(c_282, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_279])).
% 3.47/1.59  tff(c_10, plain, (![A_7]: (k1_relat_1(A_7)=k1_xboole_0 | k2_relat_1(A_7)!=k1_xboole_0 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.59  tff(c_286, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0 | k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_282, c_10])).
% 3.47/1.59  tff(c_704, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_286])).
% 3.47/1.59  tff(c_685, plain, (![A_93]: (k2_relat_1(A_93)=k1_xboole_0 | k1_relat_1(A_93)!=k1_xboole_0 | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.59  tff(c_698, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0 | k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_282, c_685])).
% 3.47/1.59  tff(c_705, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_704, c_698])).
% 3.47/1.59  tff(c_706, plain, (![A_94]: (k4_relat_1(A_94)=k2_funct_1(A_94) | ~v2_funct_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.47/1.59  tff(c_709, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_706])).
% 3.47/1.59  tff(c_712, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_50, c_709])).
% 3.47/1.59  tff(c_716, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_712, c_8])).
% 3.47/1.59  tff(c_723, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_101, c_676, c_716])).
% 3.47/1.59  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_705, c_723])).
% 3.47/1.59  tff(c_726, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_286])).
% 3.47/1.59  tff(c_774, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.47/1.59  tff(c_777, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_276, c_774])).
% 3.47/1.59  tff(c_782, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_726, c_777])).
% 3.47/1.59  tff(c_804, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_803, c_782])).
% 3.47/1.59  tff(c_950, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_939, c_939, c_804])).
% 3.47/1.59  tff(c_957, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_939, c_276])).
% 3.47/1.59  tff(c_956, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_939, c_803])).
% 3.47/1.59  tff(c_32, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.47/1.59  tff(c_1225, plain, (![C_130, B_131]: (v1_funct_2(C_130, '#skF_1', B_131) | k1_relset_1('#skF_1', B_131, C_130)!='#skF_1' | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_131))))), inference(demodulation, [status(thm), theory('equality')], [c_956, c_956, c_956, c_956, c_32])).
% 3.47/1.59  tff(c_1238, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))!='#skF_1'), inference(resolution, [status(thm)], [c_957, c_1225])).
% 3.47/1.59  tff(c_1247, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_950, c_1238])).
% 3.47/1.59  tff(c_1249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_958, c_1247])).
% 3.47/1.59  tff(c_1250, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_938])).
% 3.47/1.59  tff(c_1270, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_275])).
% 3.47/1.59  tff(c_1262, plain, (k1_relset_1('#skF_3', '#skF_1', k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_1250, c_804])).
% 3.47/1.59  tff(c_1269, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_276])).
% 3.47/1.59  tff(c_1268, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_803])).
% 3.47/1.59  tff(c_1393, plain, (![C_135, B_136]: (v1_funct_2(C_135, '#skF_3', B_136) | k1_relset_1('#skF_3', B_136, C_135)!='#skF_3' | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_136))))), inference(demodulation, [status(thm), theory('equality')], [c_1268, c_1268, c_1268, c_1268, c_32])).
% 3.47/1.59  tff(c_1396, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1') | k1_relset_1('#skF_3', '#skF_1', k2_funct_1('#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_1269, c_1393])).
% 3.47/1.59  tff(c_1399, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_1396])).
% 3.47/1.59  tff(c_1401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1270, c_1399])).
% 3.47/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.59  
% 3.47/1.59  Inference rules
% 3.47/1.59  ----------------------
% 3.47/1.59  #Ref     : 0
% 3.47/1.59  #Sup     : 327
% 3.47/1.59  #Fact    : 0
% 3.47/1.59  #Define  : 0
% 3.47/1.59  #Split   : 8
% 3.47/1.59  #Chain   : 0
% 3.47/1.59  #Close   : 0
% 3.47/1.59  
% 3.47/1.59  Ordering : KBO
% 3.47/1.59  
% 3.47/1.59  Simplification rules
% 3.47/1.59  ----------------------
% 3.47/1.59  #Subsume      : 18
% 3.47/1.59  #Demod        : 281
% 3.47/1.59  #Tautology    : 195
% 3.47/1.59  #SimpNegUnit  : 24
% 3.47/1.59  #BackRed      : 65
% 3.47/1.59  
% 3.47/1.59  #Partial instantiations: 0
% 3.47/1.59  #Strategies tried      : 1
% 3.47/1.59  
% 3.47/1.59  Timing (in seconds)
% 3.47/1.59  ----------------------
% 3.47/1.59  Preprocessing        : 0.31
% 3.47/1.59  Parsing              : 0.16
% 3.47/1.59  CNF conversion       : 0.02
% 3.47/1.59  Main loop            : 0.45
% 3.47/1.59  Inferencing          : 0.16
% 3.47/1.59  Reduction            : 0.15
% 3.47/1.59  Demodulation         : 0.11
% 3.47/1.59  BG Simplification    : 0.02
% 3.47/1.59  Subsumption          : 0.07
% 3.47/1.59  Abstraction          : 0.02
% 3.47/1.59  MUC search           : 0.00
% 3.47/1.59  Cooper               : 0.00
% 3.47/1.59  Total                : 0.81
% 3.47/1.59  Index Insertion      : 0.00
% 3.47/1.59  Index Deletion       : 0.00
% 3.47/1.59  Index Matching       : 0.00
% 3.47/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
