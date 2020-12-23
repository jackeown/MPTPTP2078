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
% DateTime   : Thu Dec  3 10:17:10 EST 2020

% Result     : Theorem 9.60s
% Output     : CNFRefutation 9.92s
% Verified   : 
% Statistics : Number of formulae       :  208 (2311 expanded)
%              Number of leaves         :   41 ( 744 expanded)
%              Depth                    :   15
%              Number of atoms          :  338 (4921 expanded)
%              Number of equality atoms :  141 (1188 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8365,plain,(
    ! [A_1540,B_1541] :
      ( v1_xboole_0(k1_funct_2(A_1540,B_1541))
      | ~ v1_xboole_0(B_1541)
      | v1_xboole_0(A_1540) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_68,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_129,plain,(
    ! [B_41,A_42] :
      ( ~ r2_hidden(B_41,A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_129])).

tff(c_8372,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8365,c_133])).

tff(c_8374,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8372])).

tff(c_66,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_145,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_184,plain,(
    ! [A_56,B_57] :
      ( v1_xboole_0(k1_funct_2(A_56,B_57))
      | ~ v1_xboole_0(B_57)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_191,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_184,c_133])).

tff(c_193,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_866,plain,(
    ! [C_87,A_88,B_89] :
      ( m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ r2_hidden(C_87,k1_funct_2(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1268,plain,(
    ! [C_128,A_129,B_130] :
      ( r1_tarski(C_128,k2_zfmisc_1(A_129,B_130))
      | ~ r2_hidden(C_128,k1_funct_2(A_129,B_130)) ) ),
    inference(resolution,[status(thm)],[c_866,c_24])).

tff(c_1313,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_1268])).

tff(c_28,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k2_relat_1(k2_zfmisc_1(A_16,B_17)) = B_17
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_877,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k2_relat_1(A_90),k2_relat_1(B_91))
      | ~ r1_tarski(A_90,B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_886,plain,(
    ! [A_90,B_17,A_16] :
      ( r1_tarski(k2_relat_1(A_90),B_17)
      | ~ r1_tarski(A_90,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_90)
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_877])).

tff(c_3656,plain,(
    ! [A_1405,B_1406,A_1407] :
      ( r1_tarski(k2_relat_1(A_1405),B_1406)
      | ~ r1_tarski(A_1405,k2_zfmisc_1(A_1407,B_1406))
      | ~ v1_relat_1(A_1405)
      | k1_xboole_0 = B_1406
      | k1_xboole_0 = A_1407 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_886])).

tff(c_3664,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1313,c_3656])).

tff(c_3680,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3664])).

tff(c_3686,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3680])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_117,plain,(
    ! [A_38,B_39] : v1_relat_1(k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_119,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_117])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_892,plain,(
    ! [A_90] :
      ( r1_tarski(k2_relat_1(A_90),k1_xboole_0)
      | ~ r1_tarski(A_90,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_877])).

tff(c_944,plain,(
    ! [A_96] :
      ( r1_tarski(k2_relat_1(A_96),k1_xboole_0)
      | ~ r1_tarski(A_96,k1_xboole_0)
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_892])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_947,plain,(
    ! [A_96] :
      ( k4_xboole_0(k2_relat_1(A_96),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_96,k1_xboole_0)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_944,c_12])).

tff(c_960,plain,(
    ! [A_97] :
      ( k2_relat_1(A_97) = k1_xboole_0
      | ~ r1_tarski(A_97,k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_947])).

tff(c_967,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) = k1_xboole_0
      | ~ v1_relat_1(A_6)
      | k4_xboole_0(A_6,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_960])).

tff(c_979,plain,(
    ! [A_98] :
      ( k2_relat_1(A_98) = k1_xboole_0
      | ~ v1_relat_1(A_98)
      | k1_xboole_0 != A_98 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_967])).

tff(c_992,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_979])).

tff(c_993,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_992])).

tff(c_3749,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3686,c_993])).

tff(c_3782,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3686,c_16])).

tff(c_22,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3781,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_2',B_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3686,c_3686,c_22])).

tff(c_1317,plain,(
    k4_xboole_0('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1313,c_12])).

tff(c_3736,plain,(
    k4_xboole_0('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3686,c_1317])).

tff(c_4026,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3782,c_3781,c_3736])).

tff(c_4027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3749,c_4026])).

tff(c_4029,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3680])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k1_relat_1(k2_zfmisc_1(A_16,B_17)) = A_16
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1322,plain,(
    ! [A_131,B_132] :
      ( r1_tarski(k1_relat_1(A_131),k1_relat_1(B_132))
      | ~ r1_tarski(A_131,B_132)
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1331,plain,(
    ! [A_131,A_16,B_17] :
      ( r1_tarski(k1_relat_1(A_131),A_16)
      | ~ r1_tarski(A_131,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_131)
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1322])).

tff(c_4203,plain,(
    ! [A_1425,A_1426,B_1427] :
      ( r1_tarski(k1_relat_1(A_1425),A_1426)
      | ~ r1_tarski(A_1425,k2_zfmisc_1(A_1426,B_1427))
      | ~ v1_relat_1(A_1425)
      | k1_xboole_0 = B_1427
      | k1_xboole_0 = A_1426 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1331])).

tff(c_4211,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1313,c_4203])).

tff(c_4227,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4211])).

tff(c_4228,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4029,c_4227])).

tff(c_4234,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4228])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4338,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4234,c_6])).

tff(c_4340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_4338])).

tff(c_4342,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4228])).

tff(c_336,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_funct_2(C_69,A_70,B_71)
      | ~ r2_hidden(C_69,k1_funct_2(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_354,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_336])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_994,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1501,plain,(
    ! [A_142,B_143,A_144] :
      ( k1_relset_1(A_142,B_143,A_144) = k1_relat_1(A_144)
      | ~ r1_tarski(A_144,k2_zfmisc_1(A_142,B_143)) ) ),
    inference(resolution,[status(thm)],[c_26,c_994])).

tff(c_1523,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1313,c_1501])).

tff(c_58,plain,(
    ! [C_31,A_29,B_30] :
      ( m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ r2_hidden(C_31,k1_funct_2(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2167,plain,(
    ! [B_166,A_167,C_168] :
      ( k1_xboole_0 = B_166
      | k1_relset_1(A_167,B_166,C_168) = A_167
      | ~ v1_funct_2(C_168,A_167,B_166)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7389,plain,(
    ! [B_1476,A_1477,C_1478] :
      ( k1_xboole_0 = B_1476
      | k1_relset_1(A_1477,B_1476,C_1478) = A_1477
      | ~ v1_funct_2(C_1478,A_1477,B_1476)
      | ~ r2_hidden(C_1478,k1_funct_2(A_1477,B_1476)) ) ),
    inference(resolution,[status(thm)],[c_58,c_2167])).

tff(c_7468,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_7389])).

tff(c_7485,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_1523,c_7468])).

tff(c_7487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_4342,c_7485])).

tff(c_7489,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7497,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7489,c_8])).

tff(c_7488,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_7493,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7488,c_8])).

tff(c_7515,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7497,c_7493])).

tff(c_7505,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7493,c_16])).

tff(c_7559,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_3') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7515,c_7505])).

tff(c_7524,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7515,c_68])).

tff(c_7504,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_2',B_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7493,c_7493,c_22])).

tff(c_7614,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_3',B_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7515,c_7515,c_7504])).

tff(c_8165,plain,(
    ! [C_1519,A_1520,B_1521] :
      ( m1_subset_1(C_1519,k1_zfmisc_1(k2_zfmisc_1(A_1520,B_1521)))
      | ~ r2_hidden(C_1519,k1_funct_2(A_1520,B_1521)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8176,plain,(
    ! [C_1522,B_1523] :
      ( m1_subset_1(C_1522,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_1522,k1_funct_2('#skF_3',B_1523)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7614,c_8165])).

tff(c_8205,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7524,c_8176])).

tff(c_8210,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8205,c_24])).

tff(c_7500,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = '#skF_2'
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7493,c_12])).

tff(c_7648,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = '#skF_3'
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7515,c_7500])).

tff(c_8229,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8210,c_7648])).

tff(c_8231,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7559,c_8229])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7508,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7493,c_7493,c_40])).

tff(c_7532,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7515,c_7515,c_7508])).

tff(c_8264,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8231,c_8231,c_7532])).

tff(c_7522,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7515,c_145])).

tff(c_8261,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8231,c_7522])).

tff(c_8305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8264,c_8261])).

tff(c_8306,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8566,plain,(
    ! [C_1563,A_1564,B_1565] :
      ( m1_subset_1(C_1563,k1_zfmisc_1(k2_zfmisc_1(A_1564,B_1565)))
      | ~ r2_hidden(C_1563,k1_funct_2(A_1564,B_1565)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_14655,plain,(
    ! [C_3145,A_3146,B_3147] :
      ( r1_tarski(C_3145,k2_zfmisc_1(A_3146,B_3147))
      | ~ r2_hidden(C_3145,k1_funct_2(A_3146,B_3147)) ) ),
    inference(resolution,[status(thm)],[c_8566,c_24])).

tff(c_14676,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_14655])).

tff(c_14681,plain,(
    ! [A_3148,B_3149] :
      ( r1_tarski(k2_relat_1(A_3148),k2_relat_1(B_3149))
      | ~ r1_tarski(A_3148,B_3149)
      | ~ v1_relat_1(B_3149)
      | ~ v1_relat_1(A_3148) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14690,plain,(
    ! [A_3148,B_17,A_16] :
      ( r1_tarski(k2_relat_1(A_3148),B_17)
      | ~ r1_tarski(A_3148,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_3148)
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_14681])).

tff(c_17957,plain,(
    ! [A_4640,B_4641,A_4642] :
      ( r1_tarski(k2_relat_1(A_4640),B_4641)
      | ~ r1_tarski(A_4640,k2_zfmisc_1(A_4642,B_4641))
      | ~ v1_relat_1(A_4640)
      | k1_xboole_0 = B_4641
      | k1_xboole_0 = A_4642 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14690])).

tff(c_17965,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14676,c_17957])).

tff(c_17981,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_17965])).

tff(c_17982,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_8306,c_17981])).

tff(c_17988,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_17982])).

tff(c_8307,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8611,plain,(
    ! [A_1572,B_1573] :
      ( r1_tarski(k1_relat_1(A_1572),k1_relat_1(B_1573))
      | ~ r1_tarski(A_1572,B_1573)
      | ~ v1_relat_1(B_1573)
      | ~ v1_relat_1(A_1572) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8623,plain,(
    ! [B_1573] :
      ( r1_tarski('#skF_2',k1_relat_1(B_1573))
      | ~ r1_tarski('#skF_4',B_1573)
      | ~ v1_relat_1(B_1573)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8307,c_8611])).

tff(c_8646,plain,(
    ! [B_1574] :
      ( r1_tarski('#skF_2',k1_relat_1(B_1574))
      | ~ r1_tarski('#skF_4',B_1574)
      | ~ v1_relat_1(B_1574) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8623])).

tff(c_8658,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_8646])).

tff(c_8665,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_8658])).

tff(c_14499,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8665])).

tff(c_18070,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17988,c_14499])).

tff(c_18099,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_2',B_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17988,c_17988,c_22])).

tff(c_18264,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18099,c_14676])).

tff(c_18266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18070,c_18264])).

tff(c_18267,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17982])).

tff(c_18384,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18267,c_6])).

tff(c_18386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8374,c_18384])).

tff(c_18387,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8665])).

tff(c_18391,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18387,c_12])).

tff(c_18393,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18391])).

tff(c_18450,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18393,c_16])).

tff(c_18388,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8665])).

tff(c_18460,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18393,c_18388])).

tff(c_18722,plain,(
    ! [A_4675,B_4676] :
      ( k4_xboole_0(A_4675,B_4676) = '#skF_2'
      | ~ r1_tarski(A_4675,B_4676) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18393,c_12])).

tff(c_18731,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18460,c_18722])).

tff(c_18745,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18450,c_18731])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18451,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18393,c_14])).

tff(c_18770,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18745,c_18451])).

tff(c_18452,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18393,c_18393,c_38])).

tff(c_18772,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18745,c_18745,c_18452])).

tff(c_18822,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18772,c_8306])).

tff(c_18840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18770,c_18822])).

tff(c_18842,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_8372])).

tff(c_18872,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18842,c_8])).

tff(c_18841,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_8372])).

tff(c_18846,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18841,c_8])).

tff(c_18893,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18872,c_18846])).

tff(c_18883,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18846,c_16])).

tff(c_19004,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_3') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18893,c_18883])).

tff(c_18902,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18893,c_68])).

tff(c_18881,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18846,c_18846,c_20])).

tff(c_18980,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18893,c_18893,c_18881])).

tff(c_19219,plain,(
    ! [C_4712,A_4713,B_4714] :
      ( m1_subset_1(C_4712,k1_zfmisc_1(k2_zfmisc_1(A_4713,B_4714)))
      | ~ r2_hidden(C_4712,k1_funct_2(A_4713,B_4714)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_19230,plain,(
    ! [C_4715,A_4716] :
      ( m1_subset_1(C_4715,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_4715,k1_funct_2(A_4716,'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18980,c_19219])).

tff(c_19242,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18902,c_19230])).

tff(c_19247,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_19242,c_24])).

tff(c_18878,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = '#skF_2'
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18846,c_12])).

tff(c_19050,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = '#skF_3'
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18893,c_18878])).

tff(c_19250,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_19247,c_19050])).

tff(c_19252,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19004,c_19250])).

tff(c_8345,plain,(
    ! [A_1536,B_1537] :
      ( r1_tarski(A_1536,B_1537)
      | k4_xboole_0(A_1536,B_1537) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8352,plain,(
    k4_xboole_0(k2_relat_1('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8345,c_8306])).

tff(c_18875,plain,(
    k4_xboole_0(k2_relat_1('#skF_4'),'#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18846,c_8352])).

tff(c_18898,plain,(
    k4_xboole_0(k2_relat_1('#skF_4'),'#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18893,c_18875])).

tff(c_19032,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19004,c_18898])).

tff(c_19276,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19252,c_19032])).

tff(c_18885,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18846,c_18846,c_38])).

tff(c_18911,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18893,c_18893,c_18885])).

tff(c_19287,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19252,c_19252,c_18911])).

tff(c_19324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19276,c_19287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.60/3.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.60/3.53  
% 9.60/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.60/3.53  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 9.60/3.53  
% 9.60/3.53  %Foreground sorts:
% 9.60/3.53  
% 9.60/3.53  
% 9.60/3.53  %Background operators:
% 9.60/3.53  
% 9.60/3.53  
% 9.60/3.53  %Foreground operators:
% 9.60/3.53  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 9.60/3.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.60/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.60/3.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.60/3.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.60/3.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.60/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.60/3.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.60/3.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.60/3.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.60/3.53  tff('#skF_2', type, '#skF_2': $i).
% 9.60/3.53  tff('#skF_3', type, '#skF_3': $i).
% 9.60/3.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.60/3.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.60/3.53  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 9.60/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.60/3.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.60/3.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.60/3.53  tff('#skF_4', type, '#skF_4': $i).
% 9.60/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.60/3.53  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 9.60/3.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.60/3.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.60/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.60/3.53  
% 9.92/3.56  tff(f_44, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.92/3.56  tff(f_111, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 9.92/3.56  tff(f_132, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 9.92/3.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.92/3.56  tff(f_119, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 9.92/3.56  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.92/3.56  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.92/3.56  tff(f_68, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 9.92/3.56  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 9.92/3.56  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.92/3.56  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.92/3.56  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 9.92/3.56  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.92/3.56  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.92/3.56  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.92/3.56  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.92/3.56  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.92/3.56  tff(c_16, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.92/3.56  tff(c_8365, plain, (![A_1540, B_1541]: (v1_xboole_0(k1_funct_2(A_1540, B_1541)) | ~v1_xboole_0(B_1541) | v1_xboole_0(A_1540))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.92/3.56  tff(c_68, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.92/3.56  tff(c_129, plain, (![B_41, A_42]: (~r2_hidden(B_41, A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.92/3.56  tff(c_133, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_129])).
% 9.92/3.56  tff(c_8372, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8365, c_133])).
% 9.92/3.56  tff(c_8374, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_8372])).
% 9.92/3.56  tff(c_66, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.92/3.56  tff(c_145, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_66])).
% 9.92/3.56  tff(c_184, plain, (![A_56, B_57]: (v1_xboole_0(k1_funct_2(A_56, B_57)) | ~v1_xboole_0(B_57) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.92/3.56  tff(c_191, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_184, c_133])).
% 9.92/3.56  tff(c_193, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_191])).
% 9.92/3.56  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.92/3.56  tff(c_866, plain, (![C_87, A_88, B_89]: (m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~r2_hidden(C_87, k1_funct_2(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.92/3.56  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.92/3.56  tff(c_1268, plain, (![C_128, A_129, B_130]: (r1_tarski(C_128, k2_zfmisc_1(A_129, B_130)) | ~r2_hidden(C_128, k1_funct_2(A_129, B_130)))), inference(resolution, [status(thm)], [c_866, c_24])).
% 9.92/3.56  tff(c_1313, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_1268])).
% 9.92/3.56  tff(c_28, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.92/3.56  tff(c_30, plain, (![A_16, B_17]: (k2_relat_1(k2_zfmisc_1(A_16, B_17))=B_17 | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.92/3.56  tff(c_877, plain, (![A_90, B_91]: (r1_tarski(k2_relat_1(A_90), k2_relat_1(B_91)) | ~r1_tarski(A_90, B_91) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.92/3.56  tff(c_886, plain, (![A_90, B_17, A_16]: (r1_tarski(k2_relat_1(A_90), B_17) | ~r1_tarski(A_90, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_90) | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_30, c_877])).
% 9.92/3.56  tff(c_3656, plain, (![A_1405, B_1406, A_1407]: (r1_tarski(k2_relat_1(A_1405), B_1406) | ~r1_tarski(A_1405, k2_zfmisc_1(A_1407, B_1406)) | ~v1_relat_1(A_1405) | k1_xboole_0=B_1406 | k1_xboole_0=A_1407)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_886])).
% 9.92/3.56  tff(c_3664, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1313, c_3656])).
% 9.92/3.56  tff(c_3680, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3664])).
% 9.92/3.56  tff(c_3686, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3680])).
% 9.92/3.56  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.92/3.56  tff(c_20, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.92/3.56  tff(c_117, plain, (![A_38, B_39]: (v1_relat_1(k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.92/3.56  tff(c_119, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_117])).
% 9.92/3.56  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.92/3.56  tff(c_892, plain, (![A_90]: (r1_tarski(k2_relat_1(A_90), k1_xboole_0) | ~r1_tarski(A_90, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_38, c_877])).
% 9.92/3.56  tff(c_944, plain, (![A_96]: (r1_tarski(k2_relat_1(A_96), k1_xboole_0) | ~r1_tarski(A_96, k1_xboole_0) | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_892])).
% 9.92/3.56  tff(c_12, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.92/3.56  tff(c_947, plain, (![A_96]: (k4_xboole_0(k2_relat_1(A_96), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_96, k1_xboole_0) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_944, c_12])).
% 9.92/3.56  tff(c_960, plain, (![A_97]: (k2_relat_1(A_97)=k1_xboole_0 | ~r1_tarski(A_97, k1_xboole_0) | ~v1_relat_1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_947])).
% 9.92/3.56  tff(c_967, plain, (![A_6]: (k2_relat_1(A_6)=k1_xboole_0 | ~v1_relat_1(A_6) | k4_xboole_0(A_6, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_960])).
% 9.92/3.56  tff(c_979, plain, (![A_98]: (k2_relat_1(A_98)=k1_xboole_0 | ~v1_relat_1(A_98) | k1_xboole_0!=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_967])).
% 9.92/3.56  tff(c_992, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_72, c_979])).
% 9.92/3.56  tff(c_993, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_992])).
% 9.92/3.56  tff(c_3749, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3686, c_993])).
% 9.92/3.56  tff(c_3782, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_3686, c_16])).
% 9.92/3.56  tff(c_22, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.92/3.56  tff(c_3781, plain, (![B_11]: (k2_zfmisc_1('#skF_2', B_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3686, c_3686, c_22])).
% 9.92/3.56  tff(c_1317, plain, (k4_xboole_0('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1313, c_12])).
% 9.92/3.56  tff(c_3736, plain, (k4_xboole_0('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3686, c_1317])).
% 9.92/3.56  tff(c_4026, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3782, c_3781, c_3736])).
% 9.92/3.56  tff(c_4027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3749, c_4026])).
% 9.92/3.56  tff(c_4029, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_3680])).
% 9.92/3.56  tff(c_32, plain, (![A_16, B_17]: (k1_relat_1(k2_zfmisc_1(A_16, B_17))=A_16 | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.92/3.56  tff(c_1322, plain, (![A_131, B_132]: (r1_tarski(k1_relat_1(A_131), k1_relat_1(B_132)) | ~r1_tarski(A_131, B_132) | ~v1_relat_1(B_132) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.92/3.56  tff(c_1331, plain, (![A_131, A_16, B_17]: (r1_tarski(k1_relat_1(A_131), A_16) | ~r1_tarski(A_131, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_131) | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_32, c_1322])).
% 9.92/3.56  tff(c_4203, plain, (![A_1425, A_1426, B_1427]: (r1_tarski(k1_relat_1(A_1425), A_1426) | ~r1_tarski(A_1425, k2_zfmisc_1(A_1426, B_1427)) | ~v1_relat_1(A_1425) | k1_xboole_0=B_1427 | k1_xboole_0=A_1426)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1331])).
% 9.92/3.56  tff(c_4211, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1313, c_4203])).
% 9.92/3.56  tff(c_4227, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4211])).
% 9.92/3.56  tff(c_4228, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4029, c_4227])).
% 9.92/3.56  tff(c_4234, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4228])).
% 9.92/3.56  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.92/3.56  tff(c_4338, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4234, c_6])).
% 9.92/3.56  tff(c_4340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_4338])).
% 9.92/3.56  tff(c_4342, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4228])).
% 9.92/3.56  tff(c_336, plain, (![C_69, A_70, B_71]: (v1_funct_2(C_69, A_70, B_71) | ~r2_hidden(C_69, k1_funct_2(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.92/3.56  tff(c_354, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_336])).
% 9.92/3.56  tff(c_26, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.92/3.56  tff(c_994, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.92/3.56  tff(c_1501, plain, (![A_142, B_143, A_144]: (k1_relset_1(A_142, B_143, A_144)=k1_relat_1(A_144) | ~r1_tarski(A_144, k2_zfmisc_1(A_142, B_143)))), inference(resolution, [status(thm)], [c_26, c_994])).
% 9.92/3.56  tff(c_1523, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1313, c_1501])).
% 9.92/3.56  tff(c_58, plain, (![C_31, A_29, B_30]: (m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~r2_hidden(C_31, k1_funct_2(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.92/3.56  tff(c_2167, plain, (![B_166, A_167, C_168]: (k1_xboole_0=B_166 | k1_relset_1(A_167, B_166, C_168)=A_167 | ~v1_funct_2(C_168, A_167, B_166) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.92/3.56  tff(c_7389, plain, (![B_1476, A_1477, C_1478]: (k1_xboole_0=B_1476 | k1_relset_1(A_1477, B_1476, C_1478)=A_1477 | ~v1_funct_2(C_1478, A_1477, B_1476) | ~r2_hidden(C_1478, k1_funct_2(A_1477, B_1476)))), inference(resolution, [status(thm)], [c_58, c_2167])).
% 9.92/3.56  tff(c_7468, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_7389])).
% 9.92/3.56  tff(c_7485, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_1523, c_7468])).
% 9.92/3.56  tff(c_7487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_4342, c_7485])).
% 9.92/3.56  tff(c_7489, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_191])).
% 9.92/3.56  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.92/3.56  tff(c_7497, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_7489, c_8])).
% 9.92/3.56  tff(c_7488, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_191])).
% 9.92/3.56  tff(c_7493, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_7488, c_8])).
% 9.92/3.56  tff(c_7515, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7497, c_7493])).
% 9.92/3.56  tff(c_7505, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_7493, c_16])).
% 9.92/3.56  tff(c_7559, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_3')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_7515, c_7505])).
% 9.92/3.56  tff(c_7524, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7515, c_68])).
% 9.92/3.56  tff(c_7504, plain, (![B_11]: (k2_zfmisc_1('#skF_2', B_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7493, c_7493, c_22])).
% 9.92/3.56  tff(c_7614, plain, (![B_11]: (k2_zfmisc_1('#skF_3', B_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7515, c_7515, c_7504])).
% 9.92/3.56  tff(c_8165, plain, (![C_1519, A_1520, B_1521]: (m1_subset_1(C_1519, k1_zfmisc_1(k2_zfmisc_1(A_1520, B_1521))) | ~r2_hidden(C_1519, k1_funct_2(A_1520, B_1521)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.92/3.56  tff(c_8176, plain, (![C_1522, B_1523]: (m1_subset_1(C_1522, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_1522, k1_funct_2('#skF_3', B_1523)))), inference(superposition, [status(thm), theory('equality')], [c_7614, c_8165])).
% 9.92/3.56  tff(c_8205, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_7524, c_8176])).
% 9.92/3.56  tff(c_8210, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8205, c_24])).
% 9.92/3.56  tff(c_7500, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)='#skF_2' | ~r1_tarski(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_7493, c_12])).
% 9.92/3.56  tff(c_7648, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)='#skF_3' | ~r1_tarski(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_7515, c_7500])).
% 9.92/3.56  tff(c_8229, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_8210, c_7648])).
% 9.92/3.56  tff(c_8231, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7559, c_8229])).
% 9.92/3.56  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.92/3.56  tff(c_7508, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7493, c_7493, c_40])).
% 9.92/3.56  tff(c_7532, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7515, c_7515, c_7508])).
% 9.92/3.56  tff(c_8264, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8231, c_8231, c_7532])).
% 9.92/3.56  tff(c_7522, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7515, c_145])).
% 9.92/3.56  tff(c_8261, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8231, c_7522])).
% 9.92/3.56  tff(c_8305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8264, c_8261])).
% 9.92/3.56  tff(c_8306, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 9.92/3.56  tff(c_8566, plain, (![C_1563, A_1564, B_1565]: (m1_subset_1(C_1563, k1_zfmisc_1(k2_zfmisc_1(A_1564, B_1565))) | ~r2_hidden(C_1563, k1_funct_2(A_1564, B_1565)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.92/3.56  tff(c_14655, plain, (![C_3145, A_3146, B_3147]: (r1_tarski(C_3145, k2_zfmisc_1(A_3146, B_3147)) | ~r2_hidden(C_3145, k1_funct_2(A_3146, B_3147)))), inference(resolution, [status(thm)], [c_8566, c_24])).
% 9.92/3.56  tff(c_14676, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_14655])).
% 9.92/3.56  tff(c_14681, plain, (![A_3148, B_3149]: (r1_tarski(k2_relat_1(A_3148), k2_relat_1(B_3149)) | ~r1_tarski(A_3148, B_3149) | ~v1_relat_1(B_3149) | ~v1_relat_1(A_3148))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.92/3.56  tff(c_14690, plain, (![A_3148, B_17, A_16]: (r1_tarski(k2_relat_1(A_3148), B_17) | ~r1_tarski(A_3148, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_3148) | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_30, c_14681])).
% 9.92/3.56  tff(c_17957, plain, (![A_4640, B_4641, A_4642]: (r1_tarski(k2_relat_1(A_4640), B_4641) | ~r1_tarski(A_4640, k2_zfmisc_1(A_4642, B_4641)) | ~v1_relat_1(A_4640) | k1_xboole_0=B_4641 | k1_xboole_0=A_4642)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14690])).
% 9.92/3.56  tff(c_17965, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_14676, c_17957])).
% 9.92/3.56  tff(c_17981, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_17965])).
% 9.92/3.56  tff(c_17982, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_8306, c_17981])).
% 9.92/3.56  tff(c_17988, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_17982])).
% 9.92/3.56  tff(c_8307, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 9.92/3.56  tff(c_8611, plain, (![A_1572, B_1573]: (r1_tarski(k1_relat_1(A_1572), k1_relat_1(B_1573)) | ~r1_tarski(A_1572, B_1573) | ~v1_relat_1(B_1573) | ~v1_relat_1(A_1572))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.92/3.56  tff(c_8623, plain, (![B_1573]: (r1_tarski('#skF_2', k1_relat_1(B_1573)) | ~r1_tarski('#skF_4', B_1573) | ~v1_relat_1(B_1573) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8307, c_8611])).
% 9.92/3.56  tff(c_8646, plain, (![B_1574]: (r1_tarski('#skF_2', k1_relat_1(B_1574)) | ~r1_tarski('#skF_4', B_1574) | ~v1_relat_1(B_1574))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8623])).
% 9.92/3.56  tff(c_8658, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_8646])).
% 9.92/3.56  tff(c_8665, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_8658])).
% 9.92/3.56  tff(c_14499, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8665])).
% 9.92/3.56  tff(c_18070, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17988, c_14499])).
% 9.92/3.56  tff(c_18099, plain, (![B_11]: (k2_zfmisc_1('#skF_2', B_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17988, c_17988, c_22])).
% 9.92/3.56  tff(c_18264, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18099, c_14676])).
% 9.92/3.56  tff(c_18266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18070, c_18264])).
% 9.92/3.56  tff(c_18267, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_17982])).
% 9.92/3.56  tff(c_18384, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18267, c_6])).
% 9.92/3.56  tff(c_18386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8374, c_18384])).
% 9.92/3.56  tff(c_18387, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8665])).
% 9.92/3.56  tff(c_18391, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_18387, c_12])).
% 9.92/3.56  tff(c_18393, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18391])).
% 9.92/3.56  tff(c_18450, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_18393, c_16])).
% 9.92/3.56  tff(c_18388, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8665])).
% 9.92/3.56  tff(c_18460, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18393, c_18388])).
% 9.92/3.56  tff(c_18722, plain, (![A_4675, B_4676]: (k4_xboole_0(A_4675, B_4676)='#skF_2' | ~r1_tarski(A_4675, B_4676))), inference(demodulation, [status(thm), theory('equality')], [c_18393, c_12])).
% 9.92/3.56  tff(c_18731, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_18460, c_18722])).
% 9.92/3.56  tff(c_18745, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18450, c_18731])).
% 9.92/3.56  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.92/3.56  tff(c_18451, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_18393, c_14])).
% 9.92/3.56  tff(c_18770, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_18745, c_18451])).
% 9.92/3.56  tff(c_18452, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18393, c_18393, c_38])).
% 9.92/3.56  tff(c_18772, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18745, c_18745, c_18452])).
% 9.92/3.56  tff(c_18822, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18772, c_8306])).
% 9.92/3.56  tff(c_18840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18770, c_18822])).
% 9.92/3.56  tff(c_18842, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_8372])).
% 9.92/3.56  tff(c_18872, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_18842, c_8])).
% 9.92/3.56  tff(c_18841, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_8372])).
% 9.92/3.56  tff(c_18846, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_18841, c_8])).
% 9.92/3.56  tff(c_18893, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18872, c_18846])).
% 9.92/3.56  tff(c_18883, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_18846, c_16])).
% 9.92/3.56  tff(c_19004, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_3')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_18893, c_18883])).
% 9.92/3.56  tff(c_18902, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18893, c_68])).
% 9.92/3.56  tff(c_18881, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18846, c_18846, c_20])).
% 9.92/3.56  tff(c_18980, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18893, c_18893, c_18881])).
% 9.92/3.56  tff(c_19219, plain, (![C_4712, A_4713, B_4714]: (m1_subset_1(C_4712, k1_zfmisc_1(k2_zfmisc_1(A_4713, B_4714))) | ~r2_hidden(C_4712, k1_funct_2(A_4713, B_4714)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.92/3.56  tff(c_19230, plain, (![C_4715, A_4716]: (m1_subset_1(C_4715, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_4715, k1_funct_2(A_4716, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18980, c_19219])).
% 9.92/3.56  tff(c_19242, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_18902, c_19230])).
% 9.92/3.56  tff(c_19247, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_19242, c_24])).
% 9.92/3.56  tff(c_18878, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)='#skF_2' | ~r1_tarski(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_18846, c_12])).
% 9.92/3.56  tff(c_19050, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)='#skF_3' | ~r1_tarski(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_18893, c_18878])).
% 9.92/3.56  tff(c_19250, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_19247, c_19050])).
% 9.92/3.56  tff(c_19252, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19004, c_19250])).
% 9.92/3.56  tff(c_8345, plain, (![A_1536, B_1537]: (r1_tarski(A_1536, B_1537) | k4_xboole_0(A_1536, B_1537)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.92/3.56  tff(c_8352, plain, (k4_xboole_0(k2_relat_1('#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8345, c_8306])).
% 9.92/3.56  tff(c_18875, plain, (k4_xboole_0(k2_relat_1('#skF_4'), '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18846, c_8352])).
% 9.92/3.56  tff(c_18898, plain, (k4_xboole_0(k2_relat_1('#skF_4'), '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18893, c_18875])).
% 9.92/3.56  tff(c_19032, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19004, c_18898])).
% 9.92/3.56  tff(c_19276, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19252, c_19032])).
% 9.92/3.56  tff(c_18885, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18846, c_18846, c_38])).
% 9.92/3.56  tff(c_18911, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18893, c_18893, c_18885])).
% 9.92/3.56  tff(c_19287, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19252, c_19252, c_18911])).
% 9.92/3.56  tff(c_19324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19276, c_19287])).
% 9.92/3.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.56  
% 9.92/3.56  Inference rules
% 9.92/3.56  ----------------------
% 9.92/3.56  #Ref     : 0
% 9.92/3.56  #Sup     : 4188
% 9.92/3.56  #Fact    : 12
% 9.92/3.56  #Define  : 0
% 9.92/3.56  #Split   : 33
% 9.92/3.56  #Chain   : 0
% 9.92/3.56  #Close   : 0
% 9.92/3.56  
% 9.92/3.56  Ordering : KBO
% 9.92/3.56  
% 9.92/3.56  Simplification rules
% 9.92/3.56  ----------------------
% 9.92/3.56  #Subsume      : 967
% 9.92/3.56  #Demod        : 4451
% 9.92/3.56  #Tautology    : 2108
% 9.92/3.56  #SimpNegUnit  : 165
% 9.92/3.56  #BackRed      : 997
% 9.92/3.56  
% 9.92/3.56  #Partial instantiations: 603
% 9.92/3.56  #Strategies tried      : 1
% 9.92/3.56  
% 9.92/3.56  Timing (in seconds)
% 9.92/3.56  ----------------------
% 9.92/3.56  Preprocessing        : 0.34
% 9.92/3.56  Parsing              : 0.19
% 9.92/3.56  CNF conversion       : 0.02
% 9.92/3.56  Main loop            : 2.36
% 9.92/3.56  Inferencing          : 0.77
% 9.92/3.56  Reduction            : 0.74
% 9.92/3.56  Demodulation         : 0.52
% 9.92/3.56  BG Simplification    : 0.08
% 9.92/3.56  Subsumption          : 0.60
% 9.92/3.56  Abstraction          : 0.09
% 9.92/3.56  MUC search           : 0.00
% 9.92/3.56  Cooper               : 0.00
% 9.92/3.56  Total                : 2.76
% 9.92/3.56  Index Insertion      : 0.00
% 9.92/3.56  Index Deletion       : 0.00
% 9.92/3.56  Index Matching       : 0.00
% 9.92/3.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
