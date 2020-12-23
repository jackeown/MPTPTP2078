%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:51 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 817 expanded)
%              Number of leaves         :   36 ( 277 expanded)
%              Depth                    :   12
%              Number of atoms          :  315 (2229 expanded)
%              Number of equality atoms :  113 ( 562 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_149,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_184,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_187,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_184])).

tff(c_193,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_187])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_68,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_66,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1516,plain,(
    ! [A_202,B_203,C_204] :
      ( k2_relset_1(A_202,B_203,C_204) = k2_relat_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1522,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1516])).

tff(c_1529,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1522])).

tff(c_40,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_341,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_relset_1(A_74,B_75,C_76) = k2_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_344,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_341])).

tff(c_350,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_344])).

tff(c_22,plain,(
    ! [A_13] :
      ( k2_relat_1(A_13) != k1_xboole_0
      | k1_xboole_0 = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_211,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_193,c_22])).

tff(c_249,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_353,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_249])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_315,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_323,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_315])).

tff(c_548,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_554,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_548])).

tff(c_562,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_323,c_554])).

tff(c_563,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_562])).

tff(c_38,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_125,plain,(
    ! [A_39] :
      ( v1_funct_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_110,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_128,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_125,c_110])).

tff(c_131,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_128])).

tff(c_155,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_158,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_155])).

tff(c_164,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_158])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_164])).

tff(c_168,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_358,plain,(
    ! [B_77,A_78] :
      ( v1_funct_2(B_77,k1_relat_1(B_77),A_78)
      | ~ r1_tarski(k2_relat_1(B_77),A_78)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_829,plain,(
    ! [A_120,A_121] :
      ( v1_funct_2(k2_funct_1(A_120),k2_relat_1(A_120),A_121)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_120)),A_121)
      | ~ v1_funct_1(k2_funct_1(A_120))
      | ~ v1_relat_1(k2_funct_1(A_120))
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_358])).

tff(c_832,plain,(
    ! [A_121] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_121)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_121)
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_829])).

tff(c_840,plain,(
    ! [A_121] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_121)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_121)
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_74,c_68,c_168,c_832])).

tff(c_843,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_840])).

tff(c_846,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_843])).

tff(c_850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_74,c_846])).

tff(c_852,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_840])).

tff(c_390,plain,(
    ! [B_86,A_87] :
      ( m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_86),A_87)))
      | ~ r1_tarski(k2_relat_1(B_86),A_87)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_867,plain,(
    ! [A_122,A_123] :
      ( m1_subset_1(k2_funct_1(A_122),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_122),A_123)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_122)),A_123)
      | ~ v1_funct_1(k2_funct_1(A_122))
      | ~ v1_relat_1(k2_funct_1(A_122))
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_390])).

tff(c_894,plain,(
    ! [A_123] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_123)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_123)
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_867])).

tff(c_934,plain,(
    ! [A_125] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_125)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_74,c_68,c_852,c_168,c_894])).

tff(c_167,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_221,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_973,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_934,c_221])).

tff(c_979,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_973])).

tff(c_982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_74,c_68,c_6,c_563,c_979])).

tff(c_983,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_992,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_10])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_993,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_983,c_20])).

tff(c_170,plain,(
    ! [A_46] :
      ( k2_relat_1(A_46) != k1_xboole_0
      | k1_xboole_0 = A_46
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_180,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) != k1_xboole_0
      | k2_funct_1(A_17) = k1_xboole_0
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_30,c_170])).

tff(c_1131,plain,(
    ! [A_151] :
      ( k2_relat_1(k2_funct_1(A_151)) != '#skF_4'
      | k2_funct_1(A_151) = '#skF_4'
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_983,c_180])).

tff(c_1339,plain,(
    ! [A_179] :
      ( k1_relat_1(A_179) != '#skF_4'
      | k2_funct_1(A_179) = '#skF_4'
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179)
      | ~ v2_funct_1(A_179)
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1131])).

tff(c_1345,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1339])).

tff(c_1351,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_74,c_993,c_1345])).

tff(c_984,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1001,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_984])).

tff(c_1135,plain,(
    ! [A_152,B_153,C_154] :
      ( k2_relset_1(A_152,B_153,C_154) = k2_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1139,plain,(
    ! [A_152,B_153] : k2_relset_1(A_152,B_153,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_992,c_1135])).

tff(c_1141,plain,(
    ! [A_152,B_153] : k2_relset_1(A_152,B_153,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_1139])).

tff(c_1142,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_66])).

tff(c_1150,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_221])).

tff(c_1352,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1351,c_1150])).

tff(c_1356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_1352])).

tff(c_1357,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_1358,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_1486,plain,(
    ! [A_197,B_198,C_199] :
      ( k1_relset_1(A_197,B_198,C_199) = k1_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1497,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1358,c_1486])).

tff(c_1704,plain,(
    ! [B_224,C_225,A_226] :
      ( k1_xboole_0 = B_224
      | v1_funct_2(C_225,A_226,B_224)
      | k1_relset_1(A_226,B_224,C_225) != A_226
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1710,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1358,c_1704])).

tff(c_1720,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1497,c_1710])).

tff(c_1721,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1357,c_1720])).

tff(c_1727,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1721])).

tff(c_1730,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1727])).

tff(c_1733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_74,c_68,c_1529,c_1730])).

tff(c_1734,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1721])).

tff(c_1401,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_1532,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1529,c_1401])).

tff(c_1744,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_1532])).

tff(c_1498,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1486])).

tff(c_56,plain,(
    ! [B_26,A_25,C_27] :
      ( k1_xboole_0 = B_26
      | k1_relset_1(A_25,B_26,C_27) = A_25
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1831,plain,(
    ! [B_227,A_228,C_229] :
      ( B_227 = '#skF_2'
      | k1_relset_1(A_228,B_227,C_229) = A_228
      | ~ v1_funct_2(C_229,A_228,B_227)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_228,B_227))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_56])).

tff(c_1840,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1831])).

tff(c_1845,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1498,c_1840])).

tff(c_1846,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1744,c_1845])).

tff(c_24,plain,(
    ! [A_13] :
      ( k1_relat_1(A_13) != k1_xboole_0
      | k1_xboole_0 = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_212,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_193,c_24])).

tff(c_1386,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_1752,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_1386])).

tff(c_1873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_1752])).

tff(c_1874,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1876,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1874,c_1386])).

tff(c_1885,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1874,c_1874,c_20])).

tff(c_1898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1876,c_1885])).

tff(c_1899,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1917,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_8])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1916,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1899,c_18])).

tff(c_1900,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_1923,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1900])).

tff(c_2178,plain,(
    ! [B_271,A_272] :
      ( v1_funct_2(B_271,k1_relat_1(B_271),A_272)
      | ~ r1_tarski(k2_relat_1(B_271),A_272)
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2184,plain,(
    ! [A_272] :
      ( v1_funct_2('#skF_4','#skF_4',A_272)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_272)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1923,c_2178])).

tff(c_2186,plain,(
    ! [A_272] : v1_funct_2('#skF_4','#skF_4',A_272) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_74,c_1917,c_1916,c_2184])).

tff(c_1914,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_10])).

tff(c_2143,plain,(
    ! [A_261,B_262,C_263] :
      ( k2_relset_1(A_261,B_262,C_263) = k2_relat_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2147,plain,(
    ! [A_261,B_262] : k2_relset_1(A_261,B_262,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1914,c_2143])).

tff(c_2149,plain,(
    ! [A_261,B_262] : k2_relset_1(A_261,B_262,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_2147])).

tff(c_2150,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2149,c_66])).

tff(c_2038,plain,(
    ! [A_250] :
      ( k1_relat_1(k2_funct_1(A_250)) = k2_relat_1(A_250)
      | ~ v2_funct_1(A_250)
      | ~ v1_funct_1(A_250)
      | ~ v1_relat_1(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14,plain,(
    ! [B_10,A_8] :
      ( v1_relat_1(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1903,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1358,c_14])).

tff(c_1906,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1903])).

tff(c_1971,plain,(
    ! [A_241] :
      ( k1_relat_1(A_241) != '#skF_4'
      | A_241 = '#skF_4'
      | ~ v1_relat_1(A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1899,c_24])).

tff(c_1987,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1906,c_1971])).

tff(c_2019,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1987])).

tff(c_2044,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2038,c_2019])).

tff(c_2051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_74,c_68,c_1916,c_2044])).

tff(c_2052,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1987])).

tff(c_2068,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_1357])).

tff(c_2158,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2068])).

tff(c_2189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_2158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:53:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.72  
% 4.30/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.73  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.30/1.73  
% 4.30/1.73  %Foreground sorts:
% 4.30/1.73  
% 4.30/1.73  
% 4.30/1.73  %Background operators:
% 4.30/1.73  
% 4.30/1.73  
% 4.30/1.73  %Foreground operators:
% 4.30/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.30/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.30/1.73  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.30/1.73  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.30/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.30/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.30/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.30/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.30/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.30/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.30/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.30/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.30/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.30/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.30/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.30/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.30/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.30/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.30/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.30/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.30/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.30/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.30/1.73  
% 4.30/1.75  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.30/1.75  tff(f_149, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.30/1.75  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.30/1.75  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.30/1.75  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.30/1.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.30/1.75  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.30/1.75  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.30/1.75  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.30/1.75  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.30/1.75  tff(f_132, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.30/1.75  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.30/1.75  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.30/1.75  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.30/1.75  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.30/1.75  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.30/1.75  tff(c_184, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.30/1.75  tff(c_187, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_70, c_184])).
% 4.30/1.75  tff(c_193, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_187])).
% 4.30/1.75  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.30/1.75  tff(c_68, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.30/1.75  tff(c_66, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.30/1.75  tff(c_1516, plain, (![A_202, B_203, C_204]: (k2_relset_1(A_202, B_203, C_204)=k2_relat_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.30/1.75  tff(c_1522, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_1516])).
% 4.30/1.75  tff(c_1529, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1522])).
% 4.30/1.75  tff(c_40, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.30/1.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.75  tff(c_341, plain, (![A_74, B_75, C_76]: (k2_relset_1(A_74, B_75, C_76)=k2_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.30/1.75  tff(c_344, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_341])).
% 4.30/1.75  tff(c_350, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_344])).
% 4.30/1.75  tff(c_22, plain, (![A_13]: (k2_relat_1(A_13)!=k1_xboole_0 | k1_xboole_0=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.75  tff(c_211, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_193, c_22])).
% 4.30/1.75  tff(c_249, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_211])).
% 4.30/1.75  tff(c_353, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_249])).
% 4.30/1.75  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.30/1.75  tff(c_315, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.30/1.75  tff(c_323, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_315])).
% 4.30/1.75  tff(c_548, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.30/1.75  tff(c_554, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_548])).
% 4.30/1.75  tff(c_562, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_323, c_554])).
% 4.30/1.75  tff(c_563, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_353, c_562])).
% 4.30/1.75  tff(c_38, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.30/1.75  tff(c_30, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.30/1.75  tff(c_125, plain, (![A_39]: (v1_funct_1(k2_funct_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.30/1.75  tff(c_64, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.30/1.75  tff(c_110, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_64])).
% 4.30/1.75  tff(c_128, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_125, c_110])).
% 4.30/1.75  tff(c_131, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_128])).
% 4.30/1.75  tff(c_155, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.30/1.75  tff(c_158, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_70, c_155])).
% 4.30/1.75  tff(c_164, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_158])).
% 4.30/1.75  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_164])).
% 4.30/1.75  tff(c_168, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_64])).
% 4.30/1.75  tff(c_358, plain, (![B_77, A_78]: (v1_funct_2(B_77, k1_relat_1(B_77), A_78) | ~r1_tarski(k2_relat_1(B_77), A_78) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.30/1.75  tff(c_829, plain, (![A_120, A_121]: (v1_funct_2(k2_funct_1(A_120), k2_relat_1(A_120), A_121) | ~r1_tarski(k2_relat_1(k2_funct_1(A_120)), A_121) | ~v1_funct_1(k2_funct_1(A_120)) | ~v1_relat_1(k2_funct_1(A_120)) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_40, c_358])).
% 4.30/1.75  tff(c_832, plain, (![A_121]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_121) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_121) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_350, c_829])).
% 4.30/1.75  tff(c_840, plain, (![A_121]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_121) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_121) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_74, c_68, c_168, c_832])).
% 4.30/1.75  tff(c_843, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_840])).
% 4.30/1.75  tff(c_846, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_843])).
% 4.30/1.75  tff(c_850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_74, c_846])).
% 4.30/1.75  tff(c_852, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_840])).
% 4.30/1.75  tff(c_390, plain, (![B_86, A_87]: (m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_86), A_87))) | ~r1_tarski(k2_relat_1(B_86), A_87) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.30/1.75  tff(c_867, plain, (![A_122, A_123]: (m1_subset_1(k2_funct_1(A_122), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_122), A_123))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_122)), A_123) | ~v1_funct_1(k2_funct_1(A_122)) | ~v1_relat_1(k2_funct_1(A_122)) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_40, c_390])).
% 4.30/1.75  tff(c_894, plain, (![A_123]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_123))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_123) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_350, c_867])).
% 4.30/1.75  tff(c_934, plain, (![A_125]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_125))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_125))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_74, c_68, c_852, c_168, c_894])).
% 4.30/1.75  tff(c_167, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_64])).
% 4.30/1.75  tff(c_221, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_167])).
% 4.30/1.75  tff(c_973, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_934, c_221])).
% 4.30/1.75  tff(c_979, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_973])).
% 4.30/1.75  tff(c_982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_74, c_68, c_6, c_563, c_979])).
% 4.30/1.75  tff(c_983, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_211])).
% 4.30/1.75  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.30/1.75  tff(c_992, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_983, c_10])).
% 4.30/1.75  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.75  tff(c_993, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_983, c_983, c_20])).
% 4.30/1.75  tff(c_170, plain, (![A_46]: (k2_relat_1(A_46)!=k1_xboole_0 | k1_xboole_0=A_46 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.75  tff(c_180, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))!=k1_xboole_0 | k2_funct_1(A_17)=k1_xboole_0 | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_30, c_170])).
% 4.30/1.75  tff(c_1131, plain, (![A_151]: (k2_relat_1(k2_funct_1(A_151))!='#skF_4' | k2_funct_1(A_151)='#skF_4' | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_983, c_983, c_180])).
% 4.30/1.75  tff(c_1339, plain, (![A_179]: (k1_relat_1(A_179)!='#skF_4' | k2_funct_1(A_179)='#skF_4' | ~v1_funct_1(A_179) | ~v1_relat_1(A_179) | ~v2_funct_1(A_179) | ~v1_funct_1(A_179) | ~v1_relat_1(A_179))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1131])).
% 4.30/1.75  tff(c_1345, plain, (k1_relat_1('#skF_4')!='#skF_4' | k2_funct_1('#skF_4')='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1339])).
% 4.30/1.75  tff(c_1351, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_74, c_993, c_1345])).
% 4.30/1.75  tff(c_984, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_211])).
% 4.30/1.75  tff(c_1001, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_983, c_984])).
% 4.30/1.75  tff(c_1135, plain, (![A_152, B_153, C_154]: (k2_relset_1(A_152, B_153, C_154)=k2_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.30/1.75  tff(c_1139, plain, (![A_152, B_153]: (k2_relset_1(A_152, B_153, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_992, c_1135])).
% 4.30/1.75  tff(c_1141, plain, (![A_152, B_153]: (k2_relset_1(A_152, B_153, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_1139])).
% 4.30/1.75  tff(c_1142, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1141, c_66])).
% 4.30/1.75  tff(c_1150, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_221])).
% 4.30/1.75  tff(c_1352, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1351, c_1150])).
% 4.30/1.75  tff(c_1356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_992, c_1352])).
% 4.30/1.75  tff(c_1357, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_167])).
% 4.30/1.75  tff(c_1358, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_167])).
% 4.30/1.75  tff(c_1486, plain, (![A_197, B_198, C_199]: (k1_relset_1(A_197, B_198, C_199)=k1_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.30/1.75  tff(c_1497, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1358, c_1486])).
% 4.30/1.75  tff(c_1704, plain, (![B_224, C_225, A_226]: (k1_xboole_0=B_224 | v1_funct_2(C_225, A_226, B_224) | k1_relset_1(A_226, B_224, C_225)!=A_226 | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_224))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.30/1.75  tff(c_1710, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_1358, c_1704])).
% 4.30/1.75  tff(c_1720, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1497, c_1710])).
% 4.30/1.75  tff(c_1721, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1357, c_1720])).
% 4.30/1.75  tff(c_1727, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_1721])).
% 4.30/1.75  tff(c_1730, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_1727])).
% 4.30/1.75  tff(c_1733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_74, c_68, c_1529, c_1730])).
% 4.30/1.75  tff(c_1734, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1721])).
% 4.30/1.75  tff(c_1401, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_211])).
% 4.30/1.75  tff(c_1532, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1529, c_1401])).
% 4.30/1.75  tff(c_1744, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_1532])).
% 4.30/1.75  tff(c_1498, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_1486])).
% 4.30/1.75  tff(c_56, plain, (![B_26, A_25, C_27]: (k1_xboole_0=B_26 | k1_relset_1(A_25, B_26, C_27)=A_25 | ~v1_funct_2(C_27, A_25, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.30/1.75  tff(c_1831, plain, (![B_227, A_228, C_229]: (B_227='#skF_2' | k1_relset_1(A_228, B_227, C_229)=A_228 | ~v1_funct_2(C_229, A_228, B_227) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_228, B_227))))), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_56])).
% 4.30/1.75  tff(c_1840, plain, ('#skF_2'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_1831])).
% 4.30/1.75  tff(c_1845, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1498, c_1840])).
% 4.30/1.75  tff(c_1846, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1744, c_1845])).
% 4.30/1.75  tff(c_24, plain, (![A_13]: (k1_relat_1(A_13)!=k1_xboole_0 | k1_xboole_0=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.75  tff(c_212, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_193, c_24])).
% 4.30/1.75  tff(c_1386, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_212])).
% 4.30/1.75  tff(c_1752, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_1386])).
% 4.30/1.75  tff(c_1873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1846, c_1752])).
% 4.30/1.75  tff(c_1874, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_211])).
% 4.30/1.75  tff(c_1876, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1874, c_1386])).
% 4.30/1.75  tff(c_1885, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1874, c_1874, c_20])).
% 4.30/1.75  tff(c_1898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1876, c_1885])).
% 4.30/1.75  tff(c_1899, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_212])).
% 4.30/1.75  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.30/1.75  tff(c_1917, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_8])).
% 4.30/1.75  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.75  tff(c_1916, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1899, c_18])).
% 4.30/1.75  tff(c_1900, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_212])).
% 4.30/1.75  tff(c_1923, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1900])).
% 4.30/1.75  tff(c_2178, plain, (![B_271, A_272]: (v1_funct_2(B_271, k1_relat_1(B_271), A_272) | ~r1_tarski(k2_relat_1(B_271), A_272) | ~v1_funct_1(B_271) | ~v1_relat_1(B_271))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.30/1.75  tff(c_2184, plain, (![A_272]: (v1_funct_2('#skF_4', '#skF_4', A_272) | ~r1_tarski(k2_relat_1('#skF_4'), A_272) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1923, c_2178])).
% 4.30/1.75  tff(c_2186, plain, (![A_272]: (v1_funct_2('#skF_4', '#skF_4', A_272))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_74, c_1917, c_1916, c_2184])).
% 4.30/1.75  tff(c_1914, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_10])).
% 4.30/1.75  tff(c_2143, plain, (![A_261, B_262, C_263]: (k2_relset_1(A_261, B_262, C_263)=k2_relat_1(C_263) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.30/1.75  tff(c_2147, plain, (![A_261, B_262]: (k2_relset_1(A_261, B_262, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1914, c_2143])).
% 4.30/1.75  tff(c_2149, plain, (![A_261, B_262]: (k2_relset_1(A_261, B_262, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1916, c_2147])).
% 4.30/1.75  tff(c_2150, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2149, c_66])).
% 4.30/1.75  tff(c_2038, plain, (![A_250]: (k1_relat_1(k2_funct_1(A_250))=k2_relat_1(A_250) | ~v2_funct_1(A_250) | ~v1_funct_1(A_250) | ~v1_relat_1(A_250))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.30/1.75  tff(c_14, plain, (![B_10, A_8]: (v1_relat_1(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.30/1.75  tff(c_1903, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_1358, c_14])).
% 4.30/1.75  tff(c_1906, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1903])).
% 4.30/1.75  tff(c_1971, plain, (![A_241]: (k1_relat_1(A_241)!='#skF_4' | A_241='#skF_4' | ~v1_relat_1(A_241))), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1899, c_24])).
% 4.30/1.75  tff(c_1987, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1906, c_1971])).
% 4.30/1.75  tff(c_2019, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_1987])).
% 4.30/1.75  tff(c_2044, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2038, c_2019])).
% 4.30/1.75  tff(c_2051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_74, c_68, c_1916, c_2044])).
% 4.30/1.75  tff(c_2052, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1987])).
% 4.30/1.75  tff(c_2068, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2052, c_1357])).
% 4.30/1.75  tff(c_2158, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2068])).
% 4.30/1.75  tff(c_2189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2186, c_2158])).
% 4.30/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.75  
% 4.30/1.75  Inference rules
% 4.30/1.75  ----------------------
% 4.30/1.75  #Ref     : 0
% 4.30/1.75  #Sup     : 418
% 4.30/1.75  #Fact    : 0
% 4.30/1.75  #Define  : 0
% 4.30/1.75  #Split   : 21
% 4.30/1.75  #Chain   : 0
% 4.30/1.75  #Close   : 0
% 4.30/1.75  
% 4.30/1.75  Ordering : KBO
% 4.30/1.75  
% 4.30/1.75  Simplification rules
% 4.30/1.75  ----------------------
% 4.30/1.75  #Subsume      : 56
% 4.30/1.75  #Demod        : 644
% 4.30/1.75  #Tautology    : 227
% 4.30/1.75  #SimpNegUnit  : 16
% 4.30/1.75  #BackRed      : 87
% 4.30/1.75  
% 4.30/1.75  #Partial instantiations: 0
% 4.30/1.75  #Strategies tried      : 1
% 4.30/1.75  
% 4.30/1.75  Timing (in seconds)
% 4.30/1.75  ----------------------
% 4.30/1.76  Preprocessing        : 0.35
% 4.30/1.76  Parsing              : 0.18
% 4.30/1.76  CNF conversion       : 0.02
% 4.30/1.76  Main loop            : 0.62
% 4.30/1.76  Inferencing          : 0.22
% 4.30/1.76  Reduction            : 0.21
% 4.30/1.76  Demodulation         : 0.15
% 4.30/1.76  BG Simplification    : 0.03
% 4.30/1.76  Subsumption          : 0.11
% 4.30/1.76  Abstraction          : 0.03
% 4.30/1.76  MUC search           : 0.00
% 4.30/1.76  Cooper               : 0.00
% 4.30/1.76  Total                : 1.03
% 4.30/1.76  Index Insertion      : 0.00
% 4.30/1.76  Index Deletion       : 0.00
% 4.30/1.76  Index Matching       : 0.00
% 4.30/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
