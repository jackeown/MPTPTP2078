%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:42 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 612 expanded)
%              Number of leaves         :   26 ( 218 expanded)
%              Depth                    :   13
%              Number of atoms          :  166 (1710 expanded)
%              Number of equality atoms :   47 ( 414 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
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

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2093,plain,(
    ! [C_206,A_207,B_208] :
      ( m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ r1_tarski(k2_relat_1(C_206),B_208)
      | ~ r1_tarski(k1_relat_1(C_206),A_207)
      | ~ v1_relat_1(C_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_9,B_11] :
      ( r1_tarski(k2_relat_1(A_9),k2_relat_1(B_11))
      | ~ r1_tarski(A_9,B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_356,plain,(
    ! [C_61,A_62,B_63] :
      ( m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ r1_tarski(k2_relat_1(C_61),B_63)
      | ~ r1_tarski(k1_relat_1(C_61),A_62)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_968,plain,(
    ! [A_130,B_131,C_132] :
      ( k1_relset_1(A_130,B_131,C_132) = k1_relat_1(C_132)
      | ~ r1_tarski(k2_relat_1(C_132),B_131)
      | ~ r1_tarski(k1_relat_1(C_132),A_130)
      | ~ v1_relat_1(C_132) ) ),
    inference(resolution,[status(thm)],[c_356,c_32])).

tff(c_1135,plain,(
    ! [A_145,B_146,A_147] :
      ( k1_relset_1(A_145,k2_relat_1(B_146),A_147) = k1_relat_1(A_147)
      | ~ r1_tarski(k1_relat_1(A_147),A_145)
      | ~ r1_tarski(A_147,B_146)
      | ~ v1_relat_1(B_146)
      | ~ v1_relat_1(A_147) ) ),
    inference(resolution,[status(thm)],[c_24,c_968])).

tff(c_1157,plain,(
    ! [A_147,B_146] :
      ( k1_relset_1(k1_relat_1(A_147),k2_relat_1(B_146),A_147) = k1_relat_1(A_147)
      | ~ r1_tarski(A_147,B_146)
      | ~ v1_relat_1(B_146)
      | ~ v1_relat_1(A_147) ) ),
    inference(resolution,[status(thm)],[c_8,c_1135])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_633,plain,(
    ! [C_101,A_102,B_103] :
      ( r1_tarski(C_101,k2_zfmisc_1(A_102,B_103))
      | ~ r1_tarski(k2_relat_1(C_101),B_103)
      | ~ r1_tarski(k1_relat_1(C_101),A_102)
      | ~ v1_relat_1(C_101) ) ),
    inference(resolution,[status(thm)],[c_356,c_18])).

tff(c_648,plain,(
    ! [C_101,A_102] :
      ( r1_tarski(C_101,k2_zfmisc_1(A_102,k2_relat_1(C_101)))
      | ~ r1_tarski(k1_relat_1(C_101),A_102)
      | ~ v1_relat_1(C_101) ) ),
    inference(resolution,[status(thm)],[c_8,c_633])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_475,plain,(
    ! [B_80,C_81,A_82] :
      ( k1_xboole_0 = B_80
      | v1_funct_2(C_81,A_82,B_80)
      | k1_relset_1(A_82,B_80,C_81) != A_82
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_828,plain,(
    ! [B_116,A_117,A_118] :
      ( k1_xboole_0 = B_116
      | v1_funct_2(A_117,A_118,B_116)
      | k1_relset_1(A_118,B_116,A_117) != A_118
      | ~ r1_tarski(A_117,k2_zfmisc_1(A_118,B_116)) ) ),
    inference(resolution,[status(thm)],[c_20,c_475])).

tff(c_1265,plain,(
    ! [C_155,A_156] :
      ( k2_relat_1(C_155) = k1_xboole_0
      | v1_funct_2(C_155,A_156,k2_relat_1(C_155))
      | k1_relset_1(A_156,k2_relat_1(C_155),C_155) != A_156
      | ~ r1_tarski(k1_relat_1(C_155),A_156)
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_648,c_828])).

tff(c_50,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_92,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_1284,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1265,c_92])).

tff(c_1299,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8,c_1284])).

tff(c_1302,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1299])).

tff(c_1305,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_1302])).

tff(c_1315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8,c_1305])).

tff(c_1316,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1299])).

tff(c_649,plain,(
    ! [C_104,A_105] :
      ( r1_tarski(C_104,k2_zfmisc_1(A_105,k2_relat_1(C_104)))
      | ~ r1_tarski(k1_relat_1(C_104),A_105)
      | ~ v1_relat_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_8,c_633])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_667,plain,(
    ! [A_105,C_104] :
      ( k2_zfmisc_1(A_105,k2_relat_1(C_104)) = C_104
      | ~ r1_tarski(k2_zfmisc_1(A_105,k2_relat_1(C_104)),C_104)
      | ~ r1_tarski(k1_relat_1(C_104),A_105)
      | ~ v1_relat_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_649,c_4])).

tff(c_1331,plain,(
    ! [A_105] :
      ( k2_zfmisc_1(A_105,k2_relat_1('#skF_1')) = '#skF_1'
      | ~ r1_tarski(k2_zfmisc_1(A_105,k1_xboole_0),'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_105)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1316,c_667])).

tff(c_1386,plain,(
    ! [A_105] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10,c_14,c_14,c_1316,c_1331])).

tff(c_1421,plain,(
    ! [A_157] : ~ r1_tarski(k1_relat_1('#skF_1'),A_157) ),
    inference(splitLeft,[status(thm)],[c_1386])).

tff(c_1450,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_1421])).

tff(c_1451,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1386])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_175,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_388,plain,(
    ! [A_66,B_67,A_68] :
      ( k1_relset_1(A_66,B_67,A_68) = k1_relat_1(A_68)
      | ~ r1_tarski(A_68,k2_zfmisc_1(A_66,B_67)) ) ),
    inference(resolution,[status(thm)],[c_20,c_175])).

tff(c_402,plain,(
    ! [A_66,B_67] : k1_relset_1(A_66,B_67,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_388])).

tff(c_405,plain,(
    ! [A_66,B_67] : k1_relset_1(A_66,B_67,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_402])).

tff(c_36,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_57,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_138,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_155,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_138])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_155])).

tff(c_161,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_438,plain,(
    ! [C_74,B_75] :
      ( v1_funct_2(C_74,k1_xboole_0,B_75)
      | k1_relset_1(k1_xboole_0,B_75,C_74) != k1_xboole_0
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_40])).

tff(c_440,plain,(
    ! [B_75] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_75)
      | k1_relset_1(k1_xboole_0,B_75,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_161,c_438])).

tff(c_446,plain,(
    ! [B_75] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_440])).

tff(c_1478,plain,(
    ! [B_75] : v1_funct_2('#skF_1','#skF_1',B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1451,c_446])).

tff(c_1500,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1451,c_30])).

tff(c_1318,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_92])).

tff(c_1452,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1318])).

tff(c_1596,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1500,c_1452])).

tff(c_1801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_1596])).

tff(c_1802,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2099,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2093,c_1802])).

tff(c_2113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8,c_8,c_2099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:47:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.73  
% 4.10/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.73  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 4.10/1.73  
% 4.10/1.73  %Foreground sorts:
% 4.10/1.73  
% 4.10/1.73  
% 4.10/1.73  %Background operators:
% 4.10/1.73  
% 4.10/1.73  
% 4.10/1.73  %Foreground operators:
% 4.10/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.10/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.10/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.10/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.10/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.10/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.10/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.10/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.10/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.10/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.10/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.10/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.73  
% 4.10/1.75  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.10/1.75  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.10/1.75  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.10/1.75  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.10/1.75  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.10/1.75  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 4.10/1.75  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.10/1.75  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.10/1.75  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.10/1.75  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.10/1.75  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.10/1.75  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.10/1.75  tff(c_2093, plain, (![C_206, A_207, B_208]: (m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~r1_tarski(k2_relat_1(C_206), B_208) | ~r1_tarski(k1_relat_1(C_206), A_207) | ~v1_relat_1(C_206))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.75  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.10/1.75  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.10/1.75  tff(c_24, plain, (![A_9, B_11]: (r1_tarski(k2_relat_1(A_9), k2_relat_1(B_11)) | ~r1_tarski(A_9, B_11) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.10/1.75  tff(c_356, plain, (![C_61, A_62, B_63]: (m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~r1_tarski(k2_relat_1(C_61), B_63) | ~r1_tarski(k1_relat_1(C_61), A_62) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.75  tff(c_32, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.10/1.75  tff(c_968, plain, (![A_130, B_131, C_132]: (k1_relset_1(A_130, B_131, C_132)=k1_relat_1(C_132) | ~r1_tarski(k2_relat_1(C_132), B_131) | ~r1_tarski(k1_relat_1(C_132), A_130) | ~v1_relat_1(C_132))), inference(resolution, [status(thm)], [c_356, c_32])).
% 4.10/1.75  tff(c_1135, plain, (![A_145, B_146, A_147]: (k1_relset_1(A_145, k2_relat_1(B_146), A_147)=k1_relat_1(A_147) | ~r1_tarski(k1_relat_1(A_147), A_145) | ~r1_tarski(A_147, B_146) | ~v1_relat_1(B_146) | ~v1_relat_1(A_147))), inference(resolution, [status(thm)], [c_24, c_968])).
% 4.10/1.75  tff(c_1157, plain, (![A_147, B_146]: (k1_relset_1(k1_relat_1(A_147), k2_relat_1(B_146), A_147)=k1_relat_1(A_147) | ~r1_tarski(A_147, B_146) | ~v1_relat_1(B_146) | ~v1_relat_1(A_147))), inference(resolution, [status(thm)], [c_8, c_1135])).
% 4.10/1.75  tff(c_18, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.10/1.75  tff(c_633, plain, (![C_101, A_102, B_103]: (r1_tarski(C_101, k2_zfmisc_1(A_102, B_103)) | ~r1_tarski(k2_relat_1(C_101), B_103) | ~r1_tarski(k1_relat_1(C_101), A_102) | ~v1_relat_1(C_101))), inference(resolution, [status(thm)], [c_356, c_18])).
% 4.10/1.75  tff(c_648, plain, (![C_101, A_102]: (r1_tarski(C_101, k2_zfmisc_1(A_102, k2_relat_1(C_101))) | ~r1_tarski(k1_relat_1(C_101), A_102) | ~v1_relat_1(C_101))), inference(resolution, [status(thm)], [c_8, c_633])).
% 4.10/1.75  tff(c_20, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.10/1.75  tff(c_475, plain, (![B_80, C_81, A_82]: (k1_xboole_0=B_80 | v1_funct_2(C_81, A_82, B_80) | k1_relset_1(A_82, B_80, C_81)!=A_82 | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_80))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.10/1.75  tff(c_828, plain, (![B_116, A_117, A_118]: (k1_xboole_0=B_116 | v1_funct_2(A_117, A_118, B_116) | k1_relset_1(A_118, B_116, A_117)!=A_118 | ~r1_tarski(A_117, k2_zfmisc_1(A_118, B_116)))), inference(resolution, [status(thm)], [c_20, c_475])).
% 4.10/1.75  tff(c_1265, plain, (![C_155, A_156]: (k2_relat_1(C_155)=k1_xboole_0 | v1_funct_2(C_155, A_156, k2_relat_1(C_155)) | k1_relset_1(A_156, k2_relat_1(C_155), C_155)!=A_156 | ~r1_tarski(k1_relat_1(C_155), A_156) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_648, c_828])).
% 4.10/1.75  tff(c_50, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.10/1.75  tff(c_48, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.10/1.75  tff(c_54, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 4.10/1.75  tff(c_92, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_54])).
% 4.10/1.75  tff(c_1284, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1265, c_92])).
% 4.10/1.75  tff(c_1299, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8, c_1284])).
% 4.10/1.75  tff(c_1302, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1299])).
% 4.10/1.75  tff(c_1305, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1157, c_1302])).
% 4.10/1.75  tff(c_1315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_8, c_1305])).
% 4.10/1.75  tff(c_1316, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1299])).
% 4.10/1.75  tff(c_649, plain, (![C_104, A_105]: (r1_tarski(C_104, k2_zfmisc_1(A_105, k2_relat_1(C_104))) | ~r1_tarski(k1_relat_1(C_104), A_105) | ~v1_relat_1(C_104))), inference(resolution, [status(thm)], [c_8, c_633])).
% 4.10/1.75  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.10/1.75  tff(c_667, plain, (![A_105, C_104]: (k2_zfmisc_1(A_105, k2_relat_1(C_104))=C_104 | ~r1_tarski(k2_zfmisc_1(A_105, k2_relat_1(C_104)), C_104) | ~r1_tarski(k1_relat_1(C_104), A_105) | ~v1_relat_1(C_104))), inference(resolution, [status(thm)], [c_649, c_4])).
% 4.10/1.75  tff(c_1331, plain, (![A_105]: (k2_zfmisc_1(A_105, k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(A_105, k1_xboole_0), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_105) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1316, c_667])).
% 4.10/1.75  tff(c_1386, plain, (![A_105]: (k1_xboole_0='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), A_105))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10, c_14, c_14, c_1316, c_1331])).
% 4.10/1.75  tff(c_1421, plain, (![A_157]: (~r1_tarski(k1_relat_1('#skF_1'), A_157))), inference(splitLeft, [status(thm)], [c_1386])).
% 4.10/1.75  tff(c_1450, plain, $false, inference(resolution, [status(thm)], [c_8, c_1421])).
% 4.10/1.75  tff(c_1451, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1386])).
% 4.10/1.75  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.10/1.75  tff(c_175, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.10/1.75  tff(c_388, plain, (![A_66, B_67, A_68]: (k1_relset_1(A_66, B_67, A_68)=k1_relat_1(A_68) | ~r1_tarski(A_68, k2_zfmisc_1(A_66, B_67)))), inference(resolution, [status(thm)], [c_20, c_175])).
% 4.10/1.75  tff(c_402, plain, (![A_66, B_67]: (k1_relset_1(A_66, B_67, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_388])).
% 4.10/1.75  tff(c_405, plain, (![A_66, B_67]: (k1_relset_1(A_66, B_67, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_402])).
% 4.10/1.75  tff(c_36, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.10/1.75  tff(c_57, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 4.10/1.75  tff(c_138, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_57])).
% 4.10/1.75  tff(c_155, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_138])).
% 4.10/1.75  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_155])).
% 4.10/1.75  tff(c_161, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_57])).
% 4.10/1.75  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.10/1.75  tff(c_40, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.10/1.75  tff(c_438, plain, (![C_74, B_75]: (v1_funct_2(C_74, k1_xboole_0, B_75) | k1_relset_1(k1_xboole_0, B_75, C_74)!=k1_xboole_0 | ~m1_subset_1(C_74, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_40])).
% 4.10/1.75  tff(c_440, plain, (![B_75]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_75) | k1_relset_1(k1_xboole_0, B_75, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_161, c_438])).
% 4.10/1.75  tff(c_446, plain, (![B_75]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_75))), inference(demodulation, [status(thm), theory('equality')], [c_405, c_440])).
% 4.10/1.75  tff(c_1478, plain, (![B_75]: (v1_funct_2('#skF_1', '#skF_1', B_75))), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1451, c_446])).
% 4.10/1.75  tff(c_1500, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1451, c_30])).
% 4.10/1.75  tff(c_1318, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1316, c_92])).
% 4.10/1.75  tff(c_1452, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1318])).
% 4.10/1.75  tff(c_1596, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1500, c_1452])).
% 4.10/1.75  tff(c_1801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1478, c_1596])).
% 4.10/1.75  tff(c_1802, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_54])).
% 4.10/1.75  tff(c_2099, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2093, c_1802])).
% 4.10/1.75  tff(c_2113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_8, c_8, c_2099])).
% 4.10/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.75  
% 4.10/1.75  Inference rules
% 4.10/1.75  ----------------------
% 4.10/1.75  #Ref     : 0
% 4.10/1.75  #Sup     : 417
% 4.10/1.75  #Fact    : 0
% 4.10/1.75  #Define  : 0
% 4.10/1.75  #Split   : 5
% 4.10/1.75  #Chain   : 0
% 4.10/1.75  #Close   : 0
% 4.10/1.75  
% 4.10/1.75  Ordering : KBO
% 4.10/1.75  
% 4.10/1.75  Simplification rules
% 4.10/1.75  ----------------------
% 4.10/1.75  #Subsume      : 42
% 4.10/1.75  #Demod        : 623
% 4.10/1.75  #Tautology    : 214
% 4.10/1.75  #SimpNegUnit  : 0
% 4.10/1.75  #BackRed      : 53
% 4.10/1.75  
% 4.10/1.75  #Partial instantiations: 0
% 4.10/1.75  #Strategies tried      : 1
% 4.10/1.75  
% 4.10/1.75  Timing (in seconds)
% 4.10/1.75  ----------------------
% 4.10/1.75  Preprocessing        : 0.33
% 4.10/1.75  Parsing              : 0.18
% 4.10/1.75  CNF conversion       : 0.02
% 4.10/1.75  Main loop            : 0.63
% 4.10/1.75  Inferencing          : 0.22
% 4.10/1.75  Reduction            : 0.19
% 4.10/1.75  Demodulation         : 0.14
% 4.10/1.75  BG Simplification    : 0.03
% 4.10/1.75  Subsumption          : 0.14
% 4.10/1.75  Abstraction          : 0.04
% 4.10/1.75  MUC search           : 0.00
% 4.10/1.75  Cooper               : 0.00
% 4.10/1.75  Total                : 1.00
% 4.10/1.75  Index Insertion      : 0.00
% 4.10/1.75  Index Deletion       : 0.00
% 4.10/1.75  Index Matching       : 0.00
% 4.10/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
