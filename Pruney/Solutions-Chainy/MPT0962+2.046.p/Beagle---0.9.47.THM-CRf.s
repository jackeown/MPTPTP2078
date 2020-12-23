%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:58 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 304 expanded)
%              Number of leaves         :   34 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  199 ( 693 expanded)
%              Number of equality atoms :   53 ( 131 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_14,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_1268,plain,(
    ! [A_202,B_203] :
      ( r1_tarski(A_202,B_203)
      | ~ m1_subset_1(A_202,k1_zfmisc_1(B_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1272,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_53,c_1268])).

tff(c_46,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1429,plain,(
    ! [C_244,A_245,B_246] :
      ( m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ r1_tarski(k2_relat_1(C_244),B_246)
      | ~ r1_tarski(k1_relat_1(C_244),A_245)
      | ~ v1_relat_1(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    ! [C_42,B_43,A_44] :
      ( ~ v1_xboole_0(C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,(
    ! [B_45,A_46,A_47] :
      ( ~ v1_xboole_0(B_45)
      | ~ r2_hidden(A_46,A_47)
      | ~ r1_tarski(A_47,B_45) ) ),
    inference(resolution,[status(thm)],[c_20,c_114])).

tff(c_125,plain,(
    ! [B_48,A_49] :
      ( ~ v1_xboole_0(B_48)
      | ~ r1_tarski(A_49,B_48)
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_133,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_125])).

tff(c_139,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44])).

tff(c_72,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_79,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_87,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_53,c_79])).

tff(c_218,plain,(
    ! [C_72,A_73,B_74] :
      ( m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ r1_tarski(k2_relat_1(C_72),B_74)
      | ~ r1_tarski(k1_relat_1(C_72),A_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_268,plain,(
    ! [C_78,A_79,B_80] :
      ( r1_tarski(C_78,k2_zfmisc_1(A_79,B_80))
      | ~ r1_tarski(k2_relat_1(C_78),B_80)
      | ~ r1_tarski(k1_relat_1(C_78),A_79)
      | ~ v1_relat_1(C_78) ) ),
    inference(resolution,[status(thm)],[c_218,c_18])).

tff(c_273,plain,(
    ! [A_79] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_79,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_79)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_268])).

tff(c_278,plain,(
    ! [A_81] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_81,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_273])).

tff(c_283,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_87,c_278])).

tff(c_141,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_150,plain,(
    ! [A_52,B_53,A_11] :
      ( k1_relset_1(A_52,B_53,A_11) = k1_relat_1(A_11)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_52,B_53)) ) ),
    inference(resolution,[status(thm)],[c_20,c_141])).

tff(c_290,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_283,c_150])).

tff(c_292,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_xboole_0 = B_82
      | v1_funct_2(C_83,A_84,B_82)
      | k1_relset_1(A_84,B_82,C_83) != A_84
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_396,plain,(
    ! [B_97,A_98,A_99] :
      ( k1_xboole_0 = B_97
      | v1_funct_2(A_98,A_99,B_97)
      | k1_relset_1(A_99,B_97,A_98) != A_99
      | ~ r1_tarski(A_98,k2_zfmisc_1(A_99,B_97)) ) ),
    inference(resolution,[status(thm)],[c_20,c_292])).

tff(c_402,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_283,c_396])).

tff(c_410,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_402])).

tff(c_411,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_410])).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [B_39,A_40] :
      ( ~ r1_xboole_0(B_39,A_40)
      | ~ r1_tarski(B_39,A_40)
      | v1_xboole_0(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_98,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_95])).

tff(c_101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_98])).

tff(c_431,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_101])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_431])).

tff(c_441,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_445,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_441,c_6])).

tff(c_89,plain,(
    ! [A_38] :
      ( k2_relat_1(A_38) = k1_xboole_0
      | k1_relat_1(A_38) != k1_xboole_0
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_93,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_89])).

tff(c_94,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_102,plain,(
    ! [A_41] :
      ( k1_relat_1(A_41) = k1_xboole_0
      | k2_relat_1(A_41) != k1_xboole_0
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_105,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_102])).

tff(c_108,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_105])).

tff(c_447,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_108])).

tff(c_440,plain,(
    v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_466,plain,(
    ! [A_100] :
      ( A_100 = '#skF_2'
      | ~ v1_xboole_0(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_6])).

tff(c_469,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_440,c_466])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_469])).

tff(c_477,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_479,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_46])).

tff(c_478,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_630,plain,(
    ! [C_137,A_138,B_139] :
      ( m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ r1_tarski(k2_relat_1(C_137),B_139)
      | ~ r1_tarski(k1_relat_1(C_137),A_138)
      | ~ v1_relat_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_690,plain,(
    ! [C_145,A_146,B_147] :
      ( r1_tarski(C_145,k2_zfmisc_1(A_146,B_147))
      | ~ r1_tarski(k2_relat_1(C_145),B_147)
      | ~ r1_tarski(k1_relat_1(C_145),A_146)
      | ~ v1_relat_1(C_145) ) ),
    inference(resolution,[status(thm)],[c_630,c_18])).

tff(c_692,plain,(
    ! [A_146,B_147] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_146,B_147))
      | ~ r1_tarski(k1_xboole_0,B_147)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_146)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_690])).

tff(c_699,plain,(
    ! [A_148,B_149] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_148,B_149))
      | ~ r1_tarski(k1_xboole_0,B_149)
      | ~ r1_tarski(k1_xboole_0,A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_478,c_692])).

tff(c_534,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_543,plain,(
    ! [A_113,B_114,A_11] :
      ( k1_relset_1(A_113,B_114,A_11) = k1_relat_1(A_11)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_113,B_114)) ) ),
    inference(resolution,[status(thm)],[c_20,c_534])).

tff(c_714,plain,(
    ! [A_148,B_149] :
      ( k1_relset_1(A_148,B_149,'#skF_3') = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_xboole_0,B_149)
      | ~ r1_tarski(k1_xboole_0,A_148) ) ),
    inference(resolution,[status(thm)],[c_699,c_543])).

tff(c_1109,plain,(
    ! [A_188,B_189] :
      ( k1_relset_1(A_188,B_189,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_189)
      | ~ r1_tarski(k1_xboole_0,A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_714])).

tff(c_1117,plain,(
    ! [A_190] :
      ( k1_relset_1(A_190,'#skF_2','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_190) ) ),
    inference(resolution,[status(thm)],[c_479,c_1109])).

tff(c_1126,plain,(
    k1_relset_1(k1_xboole_0,'#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_1117])).

tff(c_580,plain,(
    ! [C_127,B_128] :
      ( v1_funct_2(C_127,k1_xboole_0,B_128)
      | k1_relset_1(k1_xboole_0,B_128,C_127) != k1_xboole_0
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_589,plain,(
    ! [A_11,B_128] :
      ( v1_funct_2(A_11,k1_xboole_0,B_128)
      | k1_relset_1(k1_xboole_0,B_128,A_11) != k1_xboole_0
      | ~ r1_tarski(A_11,k2_zfmisc_1(k1_xboole_0,B_128)) ) ),
    inference(resolution,[status(thm)],[c_20,c_580])).

tff(c_707,plain,(
    ! [B_149] :
      ( v1_funct_2('#skF_3',k1_xboole_0,B_149)
      | k1_relset_1(k1_xboole_0,B_149,'#skF_3') != k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_149)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_699,c_589])).

tff(c_1245,plain,(
    ! [B_200] :
      ( v1_funct_2('#skF_3',k1_xboole_0,B_200)
      | k1_relset_1(k1_xboole_0,B_200,'#skF_3') != k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_707])).

tff(c_496,plain,(
    ~ v1_funct_2('#skF_3',k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_72])).

tff(c_1252,plain,
    ( k1_relset_1(k1_xboole_0,'#skF_2','#skF_3') != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_1245,c_496])).

tff(c_1260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_1126,c_1252])).

tff(c_1261,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1453,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1429,c_1261])).

tff(c_1466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1272,c_46,c_1453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.53  
% 3.45/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.53  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.45/1.53  
% 3.45/1.53  %Foreground sorts:
% 3.45/1.53  
% 3.45/1.53  
% 3.45/1.53  %Background operators:
% 3.45/1.53  
% 3.45/1.53  
% 3.45/1.53  %Foreground operators:
% 3.45/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.45/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.45/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.45/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.45/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.45/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.45/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.45/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.45/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.45/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.53  
% 3.50/1.55  tff(f_119, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.50/1.55  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.50/1.55  tff(f_59, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.50/1.55  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.50/1.55  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.50/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.50/1.55  tff(f_70, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.50/1.55  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.50/1.55  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.50/1.55  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.50/1.55  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.50/1.55  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.50/1.55  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.50/1.55  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.55  tff(c_14, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.50/1.55  tff(c_16, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.50/1.55  tff(c_53, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.50/1.55  tff(c_1268, plain, (![A_202, B_203]: (r1_tarski(A_202, B_203) | ~m1_subset_1(A_202, k1_zfmisc_1(B_203)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.50/1.55  tff(c_1272, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(resolution, [status(thm)], [c_53, c_1268])).
% 3.50/1.55  tff(c_46, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.55  tff(c_1429, plain, (![C_244, A_245, B_246]: (m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~r1_tarski(k2_relat_1(C_244), B_246) | ~r1_tarski(k1_relat_1(C_244), A_245) | ~v1_relat_1(C_244))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.50/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.55  tff(c_20, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.50/1.55  tff(c_114, plain, (![C_42, B_43, A_44]: (~v1_xboole_0(C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.50/1.55  tff(c_121, plain, (![B_45, A_46, A_47]: (~v1_xboole_0(B_45) | ~r2_hidden(A_46, A_47) | ~r1_tarski(A_47, B_45))), inference(resolution, [status(thm)], [c_20, c_114])).
% 3.50/1.55  tff(c_125, plain, (![B_48, A_49]: (~v1_xboole_0(B_48) | ~r1_tarski(A_49, B_48) | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_4, c_121])).
% 3.50/1.55  tff(c_133, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_125])).
% 3.50/1.55  tff(c_139, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_133])).
% 3.50/1.55  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.55  tff(c_44, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.55  tff(c_52, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44])).
% 3.50/1.55  tff(c_72, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 3.50/1.55  tff(c_79, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.50/1.55  tff(c_87, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(resolution, [status(thm)], [c_53, c_79])).
% 3.50/1.55  tff(c_218, plain, (![C_72, A_73, B_74]: (m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~r1_tarski(k2_relat_1(C_72), B_74) | ~r1_tarski(k1_relat_1(C_72), A_73) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.50/1.55  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.50/1.55  tff(c_268, plain, (![C_78, A_79, B_80]: (r1_tarski(C_78, k2_zfmisc_1(A_79, B_80)) | ~r1_tarski(k2_relat_1(C_78), B_80) | ~r1_tarski(k1_relat_1(C_78), A_79) | ~v1_relat_1(C_78))), inference(resolution, [status(thm)], [c_218, c_18])).
% 3.50/1.55  tff(c_273, plain, (![A_79]: (r1_tarski('#skF_3', k2_zfmisc_1(A_79, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_79) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_268])).
% 3.50/1.55  tff(c_278, plain, (![A_81]: (r1_tarski('#skF_3', k2_zfmisc_1(A_81, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_81))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_273])).
% 3.50/1.55  tff(c_283, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_87, c_278])).
% 3.50/1.55  tff(c_141, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.50/1.55  tff(c_150, plain, (![A_52, B_53, A_11]: (k1_relset_1(A_52, B_53, A_11)=k1_relat_1(A_11) | ~r1_tarski(A_11, k2_zfmisc_1(A_52, B_53)))), inference(resolution, [status(thm)], [c_20, c_141])).
% 3.50/1.55  tff(c_290, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_283, c_150])).
% 3.50/1.55  tff(c_292, plain, (![B_82, C_83, A_84]: (k1_xboole_0=B_82 | v1_funct_2(C_83, A_84, B_82) | k1_relset_1(A_84, B_82, C_83)!=A_84 | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_82))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.50/1.55  tff(c_396, plain, (![B_97, A_98, A_99]: (k1_xboole_0=B_97 | v1_funct_2(A_98, A_99, B_97) | k1_relset_1(A_99, B_97, A_98)!=A_99 | ~r1_tarski(A_98, k2_zfmisc_1(A_99, B_97)))), inference(resolution, [status(thm)], [c_20, c_292])).
% 3.50/1.55  tff(c_402, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_283, c_396])).
% 3.50/1.55  tff(c_410, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_402])).
% 3.50/1.55  tff(c_411, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_72, c_410])).
% 3.50/1.55  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.50/1.55  tff(c_95, plain, (![B_39, A_40]: (~r1_xboole_0(B_39, A_40) | ~r1_tarski(B_39, A_40) | v1_xboole_0(B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.50/1.55  tff(c_98, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_95])).
% 3.50/1.55  tff(c_101, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_98])).
% 3.50/1.55  tff(c_431, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_101])).
% 3.50/1.55  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_431])).
% 3.50/1.55  tff(c_441, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_133])).
% 3.50/1.55  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.50/1.55  tff(c_445, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_441, c_6])).
% 3.50/1.55  tff(c_89, plain, (![A_38]: (k2_relat_1(A_38)=k1_xboole_0 | k1_relat_1(A_38)!=k1_xboole_0 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.50/1.55  tff(c_93, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_89])).
% 3.50/1.55  tff(c_94, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_93])).
% 3.50/1.55  tff(c_102, plain, (![A_41]: (k1_relat_1(A_41)=k1_xboole_0 | k2_relat_1(A_41)!=k1_xboole_0 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.50/1.55  tff(c_105, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_102])).
% 3.50/1.55  tff(c_108, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_94, c_105])).
% 3.50/1.55  tff(c_447, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_108])).
% 3.50/1.55  tff(c_440, plain, (v1_xboole_0(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_133])).
% 3.50/1.55  tff(c_466, plain, (![A_100]: (A_100='#skF_2' | ~v1_xboole_0(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_6])).
% 3.50/1.55  tff(c_469, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_440, c_466])).
% 3.50/1.55  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_447, c_469])).
% 3.50/1.55  tff(c_477, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_93])).
% 3.50/1.55  tff(c_479, plain, (r1_tarski(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_46])).
% 3.50/1.55  tff(c_478, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_93])).
% 3.50/1.55  tff(c_630, plain, (![C_137, A_138, B_139]: (m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~r1_tarski(k2_relat_1(C_137), B_139) | ~r1_tarski(k1_relat_1(C_137), A_138) | ~v1_relat_1(C_137))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.50/1.55  tff(c_690, plain, (![C_145, A_146, B_147]: (r1_tarski(C_145, k2_zfmisc_1(A_146, B_147)) | ~r1_tarski(k2_relat_1(C_145), B_147) | ~r1_tarski(k1_relat_1(C_145), A_146) | ~v1_relat_1(C_145))), inference(resolution, [status(thm)], [c_630, c_18])).
% 3.50/1.55  tff(c_692, plain, (![A_146, B_147]: (r1_tarski('#skF_3', k2_zfmisc_1(A_146, B_147)) | ~r1_tarski(k1_xboole_0, B_147) | ~r1_tarski(k1_relat_1('#skF_3'), A_146) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_690])).
% 3.50/1.55  tff(c_699, plain, (![A_148, B_149]: (r1_tarski('#skF_3', k2_zfmisc_1(A_148, B_149)) | ~r1_tarski(k1_xboole_0, B_149) | ~r1_tarski(k1_xboole_0, A_148))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_478, c_692])).
% 3.50/1.55  tff(c_534, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.50/1.55  tff(c_543, plain, (![A_113, B_114, A_11]: (k1_relset_1(A_113, B_114, A_11)=k1_relat_1(A_11) | ~r1_tarski(A_11, k2_zfmisc_1(A_113, B_114)))), inference(resolution, [status(thm)], [c_20, c_534])).
% 3.50/1.55  tff(c_714, plain, (![A_148, B_149]: (k1_relset_1(A_148, B_149, '#skF_3')=k1_relat_1('#skF_3') | ~r1_tarski(k1_xboole_0, B_149) | ~r1_tarski(k1_xboole_0, A_148))), inference(resolution, [status(thm)], [c_699, c_543])).
% 3.50/1.55  tff(c_1109, plain, (![A_188, B_189]: (k1_relset_1(A_188, B_189, '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_189) | ~r1_tarski(k1_xboole_0, A_188))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_714])).
% 3.50/1.55  tff(c_1117, plain, (![A_190]: (k1_relset_1(A_190, '#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_190))), inference(resolution, [status(thm)], [c_479, c_1109])).
% 3.50/1.55  tff(c_1126, plain, (k1_relset_1(k1_xboole_0, '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_1117])).
% 3.50/1.55  tff(c_580, plain, (![C_127, B_128]: (v1_funct_2(C_127, k1_xboole_0, B_128) | k1_relset_1(k1_xboole_0, B_128, C_127)!=k1_xboole_0 | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_128))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.50/1.55  tff(c_589, plain, (![A_11, B_128]: (v1_funct_2(A_11, k1_xboole_0, B_128) | k1_relset_1(k1_xboole_0, B_128, A_11)!=k1_xboole_0 | ~r1_tarski(A_11, k2_zfmisc_1(k1_xboole_0, B_128)))), inference(resolution, [status(thm)], [c_20, c_580])).
% 3.50/1.55  tff(c_707, plain, (![B_149]: (v1_funct_2('#skF_3', k1_xboole_0, B_149) | k1_relset_1(k1_xboole_0, B_149, '#skF_3')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_149) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_699, c_589])).
% 3.50/1.55  tff(c_1245, plain, (![B_200]: (v1_funct_2('#skF_3', k1_xboole_0, B_200) | k1_relset_1(k1_xboole_0, B_200, '#skF_3')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_200))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_707])).
% 3.50/1.55  tff(c_496, plain, (~v1_funct_2('#skF_3', k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_478, c_72])).
% 3.50/1.55  tff(c_1252, plain, (k1_relset_1(k1_xboole_0, '#skF_2', '#skF_3')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_1245, c_496])).
% 3.50/1.55  tff(c_1260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_479, c_1126, c_1252])).
% 3.50/1.55  tff(c_1261, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_52])).
% 3.50/1.55  tff(c_1453, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1429, c_1261])).
% 3.50/1.55  tff(c_1466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1272, c_46, c_1453])).
% 3.50/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.55  
% 3.50/1.55  Inference rules
% 3.50/1.55  ----------------------
% 3.50/1.55  #Ref     : 0
% 3.50/1.55  #Sup     : 268
% 3.50/1.55  #Fact    : 0
% 3.50/1.55  #Define  : 0
% 3.50/1.55  #Split   : 10
% 3.50/1.55  #Chain   : 0
% 3.50/1.55  #Close   : 0
% 3.50/1.55  
% 3.50/1.55  Ordering : KBO
% 3.50/1.55  
% 3.50/1.55  Simplification rules
% 3.50/1.55  ----------------------
% 3.50/1.55  #Subsume      : 25
% 3.50/1.55  #Demod        : 266
% 3.50/1.55  #Tautology    : 97
% 3.50/1.55  #SimpNegUnit  : 6
% 3.50/1.55  #BackRed      : 59
% 3.50/1.55  
% 3.50/1.55  #Partial instantiations: 0
% 3.50/1.55  #Strategies tried      : 1
% 3.50/1.55  
% 3.50/1.55  Timing (in seconds)
% 3.50/1.55  ----------------------
% 3.50/1.56  Preprocessing        : 0.32
% 3.50/1.56  Parsing              : 0.17
% 3.50/1.56  CNF conversion       : 0.02
% 3.50/1.56  Main loop            : 0.46
% 3.50/1.56  Inferencing          : 0.17
% 3.50/1.56  Reduction            : 0.14
% 3.50/1.56  Demodulation         : 0.10
% 3.50/1.56  BG Simplification    : 0.02
% 3.50/1.56  Subsumption          : 0.08
% 3.50/1.56  Abstraction          : 0.03
% 3.50/1.56  MUC search           : 0.00
% 3.50/1.56  Cooper               : 0.00
% 3.50/1.56  Total                : 0.82
% 3.50/1.56  Index Insertion      : 0.00
% 3.50/1.56  Index Deletion       : 0.00
% 3.50/1.56  Index Matching       : 0.00
% 3.50/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
