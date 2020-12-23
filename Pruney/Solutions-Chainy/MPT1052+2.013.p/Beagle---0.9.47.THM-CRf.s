%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:10 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  209 (2189 expanded)
%              Number of leaves         :   39 ( 706 expanded)
%              Depth                    :   14
%              Number of atoms          :  339 (4750 expanded)
%              Number of equality atoms :  134 (1117 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4646,plain,(
    ! [A_1337,B_1338] :
      ( v1_xboole_0(k1_funct_2(A_1337,B_1338))
      | ~ v1_xboole_0(B_1338)
      | v1_xboole_0(A_1337) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_68,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_122,plain,(
    ! [B_40,A_41] :
      ( ~ r2_hidden(B_40,A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_122])).

tff(c_4653,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4646,c_126])).

tff(c_4655,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4653])).

tff(c_66,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_149,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_184,plain,(
    ! [A_55,B_56] :
      ( v1_xboole_0(k1_funct_2(A_55,B_56))
      | ~ v1_xboole_0(B_56)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_191,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_184,c_126])).

tff(c_203,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_855,plain,(
    ! [C_84,A_85,B_86] :
      ( m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ r2_hidden(C_84,k1_funct_2(A_85,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1001,plain,(
    ! [C_97,A_98,B_99] :
      ( r1_tarski(C_97,k2_zfmisc_1(A_98,B_99))
      | ~ r2_hidden(C_97,k1_funct_2(A_98,B_99)) ) ),
    inference(resolution,[status(thm)],[c_855,c_24])).

tff(c_1046,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_1001])).

tff(c_28,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( k1_relat_1(k2_zfmisc_1(A_15,B_16)) = A_15
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_901,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k1_relat_1(A_90),k1_relat_1(B_91))
      | ~ r1_tarski(A_90,B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_909,plain,(
    ! [A_90,A_15,B_16] :
      ( r1_tarski(k1_relat_1(A_90),A_15)
      | ~ r1_tarski(A_90,k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(A_90)
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_901])).

tff(c_2966,plain,(
    ! [A_1259,A_1260,B_1261] :
      ( r1_tarski(k1_relat_1(A_1259),A_1260)
      | ~ r1_tarski(A_1259,k2_zfmisc_1(A_1260,B_1261))
      | ~ v1_relat_1(A_1259)
      | k1_xboole_0 = B_1261
      | k1_xboole_0 = A_1260 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_909])).

tff(c_2974,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1046,c_2966])).

tff(c_2990,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2974])).

tff(c_2998,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2990])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3078,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2998,c_16])).

tff(c_22,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3077,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_2',B_10) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2998,c_2998,c_22])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1065,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1046,c_10])).

tff(c_1066,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1065])).

tff(c_3265,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_1066])).

tff(c_3269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3078,c_3265])).

tff(c_3271,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2990])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( k2_relat_1(k2_zfmisc_1(A_15,B_16)) = B_16
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1395,plain,(
    ! [A_127,B_128] :
      ( r1_tarski(k2_relat_1(A_127),k2_relat_1(B_128))
      | ~ r1_tarski(A_127,B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1403,plain,(
    ! [A_127,B_16,A_15] :
      ( r1_tarski(k2_relat_1(A_127),B_16)
      | ~ r1_tarski(A_127,k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(A_127)
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1395])).

tff(c_3273,plain,(
    ! [A_1270,B_1271,A_1272] :
      ( r1_tarski(k2_relat_1(A_1270),B_1271)
      | ~ r1_tarski(A_1270,k2_zfmisc_1(A_1272,B_1271))
      | ~ v1_relat_1(A_1270)
      | k1_xboole_0 = B_1271
      | k1_xboole_0 = A_1272 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1403])).

tff(c_3281,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1046,c_3273])).

tff(c_3297,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3281])).

tff(c_3298,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3271,c_3297])).

tff(c_3311,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3298])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3396,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3311,c_6])).

tff(c_3398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_3396])).

tff(c_3400,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3298])).

tff(c_193,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_funct_2(C_57,A_58,B_59)
      | ~ r2_hidden(C_57,k1_funct_2(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_202,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_193])).

tff(c_58,plain,(
    ! [C_30,A_28,B_29] :
      ( m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ r2_hidden(C_30,k1_funct_2(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1222,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1494,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ r2_hidden(C_136,k1_funct_2(A_134,B_135)) ) ),
    inference(resolution,[status(thm)],[c_58,c_1222])).

tff(c_1533,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1494])).

tff(c_2328,plain,(
    ! [B_1216,A_1217,C_1218] :
      ( k1_xboole_0 = B_1216
      | k1_relset_1(A_1217,B_1216,C_1218) = A_1217
      | ~ v1_funct_2(C_1218,A_1217,B_1216)
      | ~ m1_subset_1(C_1218,k1_zfmisc_1(k2_zfmisc_1(A_1217,B_1216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3801,plain,(
    ! [B_1293,A_1294,C_1295] :
      ( k1_xboole_0 = B_1293
      | k1_relset_1(A_1294,B_1293,C_1295) = A_1294
      | ~ v1_funct_2(C_1295,A_1294,B_1293)
      | ~ r2_hidden(C_1295,k1_funct_2(A_1294,B_1293)) ) ),
    inference(resolution,[status(thm)],[c_58,c_2328])).

tff(c_3844,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3801])).

tff(c_3854,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_1533,c_3844])).

tff(c_3856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_3400,c_3854])).

tff(c_3858,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3866,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3858,c_8])).

tff(c_3857,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_3862,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3857,c_8])).

tff(c_3882,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3866,c_3862])).

tff(c_3892,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3882,c_68])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3870,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3862,c_20])).

tff(c_3961,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3882,c_3882,c_3870])).

tff(c_4504,plain,(
    ! [C_1327,A_1328,B_1329] :
      ( m1_subset_1(C_1327,k1_zfmisc_1(k2_zfmisc_1(A_1328,B_1329)))
      | ~ r2_hidden(C_1327,k1_funct_2(A_1328,B_1329)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4515,plain,(
    ! [C_1330,A_1331] :
      ( m1_subset_1(C_1330,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_1330,k1_funct_2(A_1331,'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3961,c_4504])).

tff(c_4541,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3892,c_4515])).

tff(c_4546,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4541,c_24])).

tff(c_161,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_170,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_161])).

tff(c_3867,plain,(
    ! [A_8] :
      ( A_8 = '#skF_2'
      | ~ r1_tarski(A_8,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3862,c_170])).

tff(c_4020,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3882,c_3882,c_3867])).

tff(c_4552,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4546,c_4020])).

tff(c_3890,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3882,c_149])).

tff(c_4583,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4552,c_3890])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3875,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3862,c_40])).

tff(c_3903,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3882,c_3882,c_3875])).

tff(c_4586,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4552,c_4552,c_3903])).

tff(c_4628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4583,c_4586])).

tff(c_4629,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4854,plain,(
    ! [C_1362,A_1363,B_1364] :
      ( m1_subset_1(C_1362,k1_zfmisc_1(k2_zfmisc_1(A_1363,B_1364)))
      | ~ r2_hidden(C_1362,k1_funct_2(A_1363,B_1364)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5072,plain,(
    ! [C_1382,A_1383,B_1384] :
      ( r1_tarski(C_1382,k2_zfmisc_1(A_1383,B_1384))
      | ~ r2_hidden(C_1382,k1_funct_2(A_1383,B_1384)) ) ),
    inference(resolution,[status(thm)],[c_4854,c_24])).

tff(c_5093,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_5072])).

tff(c_5326,plain,(
    ! [A_1404,B_1405] :
      ( r1_tarski(k2_relat_1(A_1404),k2_relat_1(B_1405))
      | ~ r1_tarski(A_1404,B_1405)
      | ~ v1_relat_1(B_1405)
      | ~ v1_relat_1(A_1404) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5334,plain,(
    ! [A_1404,B_16,A_15] :
      ( r1_tarski(k2_relat_1(A_1404),B_16)
      | ~ r1_tarski(A_1404,k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(A_1404)
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5326])).

tff(c_7693,plain,(
    ! [A_2602,B_2603,A_2604] :
      ( r1_tarski(k2_relat_1(A_2602),B_2603)
      | ~ r1_tarski(A_2602,k2_zfmisc_1(A_2604,B_2603))
      | ~ v1_relat_1(A_2602)
      | k1_xboole_0 = B_2603
      | k1_xboole_0 = A_2604 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5334])).

tff(c_7704,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5093,c_7693])).

tff(c_7721,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7704])).

tff(c_7722,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4629,c_7721])).

tff(c_7730,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7722])).

tff(c_7814,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7730,c_16])).

tff(c_7813,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_2',B_10) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7730,c_7730,c_22])).

tff(c_5096,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5093,c_10])).

tff(c_5097,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5096])).

tff(c_7931,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7813,c_5097])).

tff(c_7935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7814,c_7931])).

tff(c_7936,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7722])).

tff(c_8024,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7936,c_6])).

tff(c_8026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4655,c_8024])).

tff(c_8027,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5096])).

tff(c_8043,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_8027,c_30])).

tff(c_8056,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8043])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8046,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8027,c_18])).

tff(c_8055,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8046])).

tff(c_8074,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8056,c_8055])).

tff(c_8223,plain,(
    ! [B_2617] : k2_zfmisc_1('#skF_2',B_2617) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8056,c_8056,c_22])).

tff(c_8230,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8223,c_8027])).

tff(c_8249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8074,c_8230])).

tff(c_8250,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8043])).

tff(c_8252,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8250])).

tff(c_8253,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8252,c_4629])).

tff(c_8256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8253])).

tff(c_8257,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8250])).

tff(c_8309,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8257,c_6])).

tff(c_8311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4655,c_8309])).

tff(c_8313,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8046])).

tff(c_95,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_95])).

tff(c_4630,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4919,plain,(
    ! [A_1372,B_1373] :
      ( r1_tarski(k1_relat_1(A_1372),k1_relat_1(B_1373))
      | ~ r1_tarski(A_1372,B_1373)
      | ~ v1_relat_1(B_1373)
      | ~ v1_relat_1(A_1372) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4930,plain,(
    ! [B_1373] :
      ( r1_tarski('#skF_2',k1_relat_1(B_1373))
      | ~ r1_tarski('#skF_4',B_1373)
      | ~ v1_relat_1(B_1373)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4630,c_4919])).

tff(c_4953,plain,(
    ! [B_1374] :
      ( r1_tarski('#skF_2',k1_relat_1(B_1374))
      | ~ r1_tarski('#skF_4',B_1374)
      | ~ v1_relat_1(B_1374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4930])).

tff(c_4964,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4953])).

tff(c_4971,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_4964])).

tff(c_4972,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4971])).

tff(c_8316,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8313,c_4972])).

tff(c_8348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8316])).

tff(c_8349,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4971])).

tff(c_4656,plain,(
    ! [B_1339,A_1340] :
      ( B_1339 = A_1340
      | ~ r1_tarski(B_1339,A_1340)
      | ~ r1_tarski(A_1340,B_1339) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4665,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_4656])).

tff(c_8356,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8349,c_4665])).

tff(c_8350,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4971])).

tff(c_8415,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8356,c_8350])).

tff(c_8557,plain,(
    ! [A_2630] :
      ( A_2630 = '#skF_2'
      | ~ r1_tarski(A_2630,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8356,c_8356,c_4665])).

tff(c_8574,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8415,c_8557])).

tff(c_8405,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8356,c_16])).

tff(c_8587,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8574,c_8405])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8406,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8356,c_8356,c_38])).

tff(c_8589,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8574,c_8574,c_8406])).

tff(c_8637,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8589,c_4629])).

tff(c_8661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8587,c_8637])).

tff(c_8663,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4653])).

tff(c_8671,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8663,c_8])).

tff(c_8662,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4653])).

tff(c_8667,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8662,c_8])).

tff(c_8686,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8671,c_8667])).

tff(c_8695,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8686,c_68])).

tff(c_8676,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_2',B_10) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8667,c_8667,c_22])).

tff(c_8753,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8686,c_8686,c_8676])).

tff(c_9311,plain,(
    ! [C_2668,A_2669,B_2670] :
      ( m1_subset_1(C_2668,k1_zfmisc_1(k2_zfmisc_1(A_2669,B_2670)))
      | ~ r2_hidden(C_2668,k1_funct_2(A_2669,B_2670)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9322,plain,(
    ! [C_2671,B_2672] :
      ( m1_subset_1(C_2671,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_2671,k1_funct_2('#skF_3',B_2672)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8753,c_9311])).

tff(c_9351,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8695,c_9322])).

tff(c_9356,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_9351,c_24])).

tff(c_8677,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8667,c_16])).

tff(c_8732,plain,(
    ! [A_2636] : r1_tarski('#skF_3',A_2636) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8686,c_8677])).

tff(c_8735,plain,(
    ! [A_2636] :
      ( A_2636 = '#skF_3'
      | ~ r1_tarski(A_2636,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8732,c_10])).

tff(c_9382,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9356,c_8735])).

tff(c_8678,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8667,c_8667,c_38])).

tff(c_8717,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8686,c_8686,c_8678])).

tff(c_9415,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9382,c_9382,c_8717])).

tff(c_9422,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9382,c_4629])).

tff(c_9447,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9415,c_9422])).

tff(c_9450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_9447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.54/2.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/2.54  
% 7.54/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/2.54  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 7.54/2.54  
% 7.54/2.54  %Foreground sorts:
% 7.54/2.54  
% 7.54/2.54  
% 7.54/2.54  %Background operators:
% 7.54/2.54  
% 7.54/2.54  
% 7.54/2.54  %Foreground operators:
% 7.54/2.54  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 7.54/2.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.54/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.54/2.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.54/2.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.54/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.54/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.54/2.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.54/2.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.54/2.54  tff('#skF_2', type, '#skF_2': $i).
% 7.54/2.54  tff('#skF_3', type, '#skF_3': $i).
% 7.54/2.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.54/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.54/2.54  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 7.54/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.54/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.54/2.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.54/2.54  tff('#skF_4', type, '#skF_4': $i).
% 7.54/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.54/2.54  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 7.54/2.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.54/2.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.54/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.54/2.54  
% 7.54/2.56  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.54/2.56  tff(f_111, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 7.54/2.56  tff(f_132, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 7.54/2.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.54/2.56  tff(f_119, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 7.54/2.56  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.54/2.56  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.54/2.56  tff(f_68, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 7.54/2.56  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 7.54/2.56  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.54/2.56  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.54/2.56  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.54/2.56  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.54/2.56  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.54/2.56  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.54/2.56  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.54/2.56  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.54/2.57  tff(c_4646, plain, (![A_1337, B_1338]: (v1_xboole_0(k1_funct_2(A_1337, B_1338)) | ~v1_xboole_0(B_1338) | v1_xboole_0(A_1337))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.54/2.57  tff(c_68, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.54/2.57  tff(c_122, plain, (![B_40, A_41]: (~r2_hidden(B_40, A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.54/2.57  tff(c_126, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_122])).
% 7.54/2.57  tff(c_4653, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4646, c_126])).
% 7.54/2.57  tff(c_4655, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_4653])).
% 7.54/2.57  tff(c_66, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.54/2.57  tff(c_149, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_66])).
% 7.54/2.57  tff(c_184, plain, (![A_55, B_56]: (v1_xboole_0(k1_funct_2(A_55, B_56)) | ~v1_xboole_0(B_56) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.54/2.57  tff(c_191, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_184, c_126])).
% 7.54/2.57  tff(c_203, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_191])).
% 7.54/2.57  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.54/2.57  tff(c_855, plain, (![C_84, A_85, B_86]: (m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~r2_hidden(C_84, k1_funct_2(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.54/2.57  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.54/2.57  tff(c_1001, plain, (![C_97, A_98, B_99]: (r1_tarski(C_97, k2_zfmisc_1(A_98, B_99)) | ~r2_hidden(C_97, k1_funct_2(A_98, B_99)))), inference(resolution, [status(thm)], [c_855, c_24])).
% 7.54/2.57  tff(c_1046, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_1001])).
% 7.54/2.57  tff(c_28, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.54/2.57  tff(c_32, plain, (![A_15, B_16]: (k1_relat_1(k2_zfmisc_1(A_15, B_16))=A_15 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.54/2.57  tff(c_901, plain, (![A_90, B_91]: (r1_tarski(k1_relat_1(A_90), k1_relat_1(B_91)) | ~r1_tarski(A_90, B_91) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.54/2.57  tff(c_909, plain, (![A_90, A_15, B_16]: (r1_tarski(k1_relat_1(A_90), A_15) | ~r1_tarski(A_90, k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(A_90) | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(superposition, [status(thm), theory('equality')], [c_32, c_901])).
% 7.54/2.57  tff(c_2966, plain, (![A_1259, A_1260, B_1261]: (r1_tarski(k1_relat_1(A_1259), A_1260) | ~r1_tarski(A_1259, k2_zfmisc_1(A_1260, B_1261)) | ~v1_relat_1(A_1259) | k1_xboole_0=B_1261 | k1_xboole_0=A_1260)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_909])).
% 7.54/2.57  tff(c_2974, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1046, c_2966])).
% 7.54/2.57  tff(c_2990, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2974])).
% 7.54/2.57  tff(c_2998, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2990])).
% 7.54/2.57  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.54/2.57  tff(c_3078, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2998, c_16])).
% 7.54/2.57  tff(c_22, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.54/2.57  tff(c_3077, plain, (![B_10]: (k2_zfmisc_1('#skF_2', B_10)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2998, c_2998, c_22])).
% 7.54/2.57  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.54/2.57  tff(c_1065, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_1046, c_10])).
% 7.54/2.57  tff(c_1066, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1065])).
% 7.54/2.57  tff(c_3265, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3077, c_1066])).
% 7.54/2.57  tff(c_3269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3078, c_3265])).
% 7.54/2.57  tff(c_3271, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2990])).
% 7.54/2.57  tff(c_30, plain, (![A_15, B_16]: (k2_relat_1(k2_zfmisc_1(A_15, B_16))=B_16 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.83/2.57  tff(c_1395, plain, (![A_127, B_128]: (r1_tarski(k2_relat_1(A_127), k2_relat_1(B_128)) | ~r1_tarski(A_127, B_128) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.83/2.57  tff(c_1403, plain, (![A_127, B_16, A_15]: (r1_tarski(k2_relat_1(A_127), B_16) | ~r1_tarski(A_127, k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(A_127) | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(superposition, [status(thm), theory('equality')], [c_30, c_1395])).
% 7.83/2.57  tff(c_3273, plain, (![A_1270, B_1271, A_1272]: (r1_tarski(k2_relat_1(A_1270), B_1271) | ~r1_tarski(A_1270, k2_zfmisc_1(A_1272, B_1271)) | ~v1_relat_1(A_1270) | k1_xboole_0=B_1271 | k1_xboole_0=A_1272)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1403])).
% 7.83/2.57  tff(c_3281, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1046, c_3273])).
% 7.83/2.57  tff(c_3297, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3281])).
% 7.83/2.57  tff(c_3298, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3271, c_3297])).
% 7.83/2.57  tff(c_3311, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3298])).
% 7.83/2.57  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.83/2.57  tff(c_3396, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3311, c_6])).
% 7.83/2.57  tff(c_3398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_203, c_3396])).
% 7.83/2.57  tff(c_3400, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3298])).
% 7.83/2.57  tff(c_193, plain, (![C_57, A_58, B_59]: (v1_funct_2(C_57, A_58, B_59) | ~r2_hidden(C_57, k1_funct_2(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.57  tff(c_202, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_193])).
% 7.83/2.57  tff(c_58, plain, (![C_30, A_28, B_29]: (m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~r2_hidden(C_30, k1_funct_2(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.57  tff(c_1222, plain, (![A_109, B_110, C_111]: (k1_relset_1(A_109, B_110, C_111)=k1_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.83/2.57  tff(c_1494, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~r2_hidden(C_136, k1_funct_2(A_134, B_135)))), inference(resolution, [status(thm)], [c_58, c_1222])).
% 7.83/2.57  tff(c_1533, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1494])).
% 7.83/2.57  tff(c_2328, plain, (![B_1216, A_1217, C_1218]: (k1_xboole_0=B_1216 | k1_relset_1(A_1217, B_1216, C_1218)=A_1217 | ~v1_funct_2(C_1218, A_1217, B_1216) | ~m1_subset_1(C_1218, k1_zfmisc_1(k2_zfmisc_1(A_1217, B_1216))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.83/2.57  tff(c_3801, plain, (![B_1293, A_1294, C_1295]: (k1_xboole_0=B_1293 | k1_relset_1(A_1294, B_1293, C_1295)=A_1294 | ~v1_funct_2(C_1295, A_1294, B_1293) | ~r2_hidden(C_1295, k1_funct_2(A_1294, B_1293)))), inference(resolution, [status(thm)], [c_58, c_2328])).
% 7.83/2.57  tff(c_3844, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_3801])).
% 7.83/2.57  tff(c_3854, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_1533, c_3844])).
% 7.83/2.57  tff(c_3856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_3400, c_3854])).
% 7.83/2.57  tff(c_3858, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_191])).
% 7.83/2.57  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.83/2.57  tff(c_3866, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3858, c_8])).
% 7.83/2.57  tff(c_3857, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_191])).
% 7.83/2.57  tff(c_3862, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3857, c_8])).
% 7.83/2.57  tff(c_3882, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3866, c_3862])).
% 7.83/2.57  tff(c_3892, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3882, c_68])).
% 7.83/2.57  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.83/2.57  tff(c_3870, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3862, c_20])).
% 7.83/2.57  tff(c_3961, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3882, c_3882, c_3870])).
% 7.83/2.57  tff(c_4504, plain, (![C_1327, A_1328, B_1329]: (m1_subset_1(C_1327, k1_zfmisc_1(k2_zfmisc_1(A_1328, B_1329))) | ~r2_hidden(C_1327, k1_funct_2(A_1328, B_1329)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.57  tff(c_4515, plain, (![C_1330, A_1331]: (m1_subset_1(C_1330, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_1330, k1_funct_2(A_1331, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3961, c_4504])).
% 7.83/2.57  tff(c_4541, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_3892, c_4515])).
% 7.83/2.57  tff(c_4546, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4541, c_24])).
% 7.83/2.57  tff(c_161, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.83/2.57  tff(c_170, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_161])).
% 7.83/2.57  tff(c_3867, plain, (![A_8]: (A_8='#skF_2' | ~r1_tarski(A_8, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3862, c_170])).
% 7.83/2.57  tff(c_4020, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3882, c_3882, c_3867])).
% 7.83/2.57  tff(c_4552, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4546, c_4020])).
% 7.83/2.57  tff(c_3890, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3882, c_149])).
% 7.83/2.57  tff(c_4583, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4552, c_3890])).
% 7.83/2.57  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.83/2.57  tff(c_3875, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3862, c_40])).
% 7.83/2.57  tff(c_3903, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3882, c_3882, c_3875])).
% 7.83/2.57  tff(c_4586, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4552, c_4552, c_3903])).
% 7.83/2.57  tff(c_4628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4583, c_4586])).
% 7.83/2.57  tff(c_4629, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 7.83/2.57  tff(c_4854, plain, (![C_1362, A_1363, B_1364]: (m1_subset_1(C_1362, k1_zfmisc_1(k2_zfmisc_1(A_1363, B_1364))) | ~r2_hidden(C_1362, k1_funct_2(A_1363, B_1364)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.57  tff(c_5072, plain, (![C_1382, A_1383, B_1384]: (r1_tarski(C_1382, k2_zfmisc_1(A_1383, B_1384)) | ~r2_hidden(C_1382, k1_funct_2(A_1383, B_1384)))), inference(resolution, [status(thm)], [c_4854, c_24])).
% 7.83/2.57  tff(c_5093, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_5072])).
% 7.83/2.57  tff(c_5326, plain, (![A_1404, B_1405]: (r1_tarski(k2_relat_1(A_1404), k2_relat_1(B_1405)) | ~r1_tarski(A_1404, B_1405) | ~v1_relat_1(B_1405) | ~v1_relat_1(A_1404))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.83/2.57  tff(c_5334, plain, (![A_1404, B_16, A_15]: (r1_tarski(k2_relat_1(A_1404), B_16) | ~r1_tarski(A_1404, k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(A_1404) | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(superposition, [status(thm), theory('equality')], [c_30, c_5326])).
% 7.83/2.57  tff(c_7693, plain, (![A_2602, B_2603, A_2604]: (r1_tarski(k2_relat_1(A_2602), B_2603) | ~r1_tarski(A_2602, k2_zfmisc_1(A_2604, B_2603)) | ~v1_relat_1(A_2602) | k1_xboole_0=B_2603 | k1_xboole_0=A_2604)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5334])).
% 7.83/2.57  tff(c_7704, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_5093, c_7693])).
% 7.83/2.57  tff(c_7721, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7704])).
% 7.83/2.57  tff(c_7722, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4629, c_7721])).
% 7.83/2.57  tff(c_7730, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_7722])).
% 7.83/2.57  tff(c_7814, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_7730, c_16])).
% 7.83/2.57  tff(c_7813, plain, (![B_10]: (k2_zfmisc_1('#skF_2', B_10)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7730, c_7730, c_22])).
% 7.83/2.57  tff(c_5096, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_5093, c_10])).
% 7.83/2.57  tff(c_5097, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5096])).
% 7.83/2.57  tff(c_7931, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7813, c_5097])).
% 7.83/2.57  tff(c_7935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7814, c_7931])).
% 7.83/2.57  tff(c_7936, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_7722])).
% 7.83/2.57  tff(c_8024, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7936, c_6])).
% 7.83/2.57  tff(c_8026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4655, c_8024])).
% 7.83/2.57  tff(c_8027, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_5096])).
% 7.83/2.57  tff(c_8043, plain, (k2_relat_1('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_8027, c_30])).
% 7.83/2.57  tff(c_8056, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_8043])).
% 7.83/2.57  tff(c_18, plain, (![B_10, A_9]: (k1_xboole_0=B_10 | k1_xboole_0=A_9 | k2_zfmisc_1(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.83/2.57  tff(c_8046, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8027, c_18])).
% 7.83/2.57  tff(c_8055, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_8046])).
% 7.83/2.57  tff(c_8074, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8056, c_8055])).
% 7.83/2.57  tff(c_8223, plain, (![B_2617]: (k2_zfmisc_1('#skF_2', B_2617)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8056, c_8056, c_22])).
% 7.83/2.57  tff(c_8230, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8223, c_8027])).
% 7.83/2.57  tff(c_8249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8074, c_8230])).
% 7.83/2.57  tff(c_8250, plain, (k1_xboole_0='#skF_3' | k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_8043])).
% 7.83/2.57  tff(c_8252, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_8250])).
% 7.83/2.57  tff(c_8253, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8252, c_4629])).
% 7.83/2.57  tff(c_8256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_8253])).
% 7.83/2.57  tff(c_8257, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_8250])).
% 7.83/2.57  tff(c_8309, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8257, c_6])).
% 7.83/2.57  tff(c_8311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4655, c_8309])).
% 7.83/2.57  tff(c_8313, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8046])).
% 7.83/2.57  tff(c_95, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.83/2.57  tff(c_97, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_95])).
% 7.83/2.57  tff(c_4630, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 7.83/2.57  tff(c_4919, plain, (![A_1372, B_1373]: (r1_tarski(k1_relat_1(A_1372), k1_relat_1(B_1373)) | ~r1_tarski(A_1372, B_1373) | ~v1_relat_1(B_1373) | ~v1_relat_1(A_1372))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.83/2.57  tff(c_4930, plain, (![B_1373]: (r1_tarski('#skF_2', k1_relat_1(B_1373)) | ~r1_tarski('#skF_4', B_1373) | ~v1_relat_1(B_1373) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4630, c_4919])).
% 7.83/2.57  tff(c_4953, plain, (![B_1374]: (r1_tarski('#skF_2', k1_relat_1(B_1374)) | ~r1_tarski('#skF_4', B_1374) | ~v1_relat_1(B_1374))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4930])).
% 7.83/2.57  tff(c_4964, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_4953])).
% 7.83/2.57  tff(c_4971, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_4964])).
% 7.83/2.57  tff(c_4972, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4971])).
% 7.83/2.57  tff(c_8316, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8313, c_4972])).
% 7.83/2.57  tff(c_8348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_8316])).
% 7.83/2.57  tff(c_8349, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4971])).
% 7.83/2.57  tff(c_4656, plain, (![B_1339, A_1340]: (B_1339=A_1340 | ~r1_tarski(B_1339, A_1340) | ~r1_tarski(A_1340, B_1339))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.83/2.57  tff(c_4665, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_4656])).
% 7.83/2.57  tff(c_8356, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8349, c_4665])).
% 7.83/2.57  tff(c_8350, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4971])).
% 7.83/2.57  tff(c_8415, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8356, c_8350])).
% 7.83/2.57  tff(c_8557, plain, (![A_2630]: (A_2630='#skF_2' | ~r1_tarski(A_2630, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8356, c_8356, c_4665])).
% 7.83/2.57  tff(c_8574, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_8415, c_8557])).
% 7.83/2.57  tff(c_8405, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_8356, c_16])).
% 7.83/2.57  tff(c_8587, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_8574, c_8405])).
% 7.83/2.57  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.83/2.57  tff(c_8406, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8356, c_8356, c_38])).
% 7.83/2.57  tff(c_8589, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8574, c_8574, c_8406])).
% 7.83/2.57  tff(c_8637, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8589, c_4629])).
% 7.83/2.57  tff(c_8661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8587, c_8637])).
% 7.83/2.57  tff(c_8663, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_4653])).
% 7.83/2.57  tff(c_8671, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8663, c_8])).
% 7.83/2.57  tff(c_8662, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_4653])).
% 7.83/2.57  tff(c_8667, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8662, c_8])).
% 7.83/2.57  tff(c_8686, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8671, c_8667])).
% 7.83/2.57  tff(c_8695, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8686, c_68])).
% 7.83/2.57  tff(c_8676, plain, (![B_10]: (k2_zfmisc_1('#skF_2', B_10)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8667, c_8667, c_22])).
% 7.83/2.57  tff(c_8753, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8686, c_8686, c_8676])).
% 7.83/2.57  tff(c_9311, plain, (![C_2668, A_2669, B_2670]: (m1_subset_1(C_2668, k1_zfmisc_1(k2_zfmisc_1(A_2669, B_2670))) | ~r2_hidden(C_2668, k1_funct_2(A_2669, B_2670)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.57  tff(c_9322, plain, (![C_2671, B_2672]: (m1_subset_1(C_2671, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_2671, k1_funct_2('#skF_3', B_2672)))), inference(superposition, [status(thm), theory('equality')], [c_8753, c_9311])).
% 7.83/2.57  tff(c_9351, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_8695, c_9322])).
% 7.83/2.57  tff(c_9356, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_9351, c_24])).
% 7.83/2.57  tff(c_8677, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_8667, c_16])).
% 7.83/2.57  tff(c_8732, plain, (![A_2636]: (r1_tarski('#skF_3', A_2636))), inference(demodulation, [status(thm), theory('equality')], [c_8686, c_8677])).
% 7.83/2.57  tff(c_8735, plain, (![A_2636]: (A_2636='#skF_3' | ~r1_tarski(A_2636, '#skF_3'))), inference(resolution, [status(thm)], [c_8732, c_10])).
% 7.83/2.57  tff(c_9382, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_9356, c_8735])).
% 7.83/2.57  tff(c_8678, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8667, c_8667, c_38])).
% 7.83/2.57  tff(c_8717, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8686, c_8686, c_8678])).
% 7.83/2.57  tff(c_9415, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9382, c_9382, c_8717])).
% 7.83/2.57  tff(c_9422, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9382, c_4629])).
% 7.83/2.57  tff(c_9447, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9415, c_9422])).
% 7.83/2.57  tff(c_9450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_9447])).
% 7.83/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.57  
% 7.83/2.57  Inference rules
% 7.83/2.57  ----------------------
% 7.83/2.57  #Ref     : 0
% 7.83/2.57  #Sup     : 2078
% 7.83/2.57  #Fact    : 8
% 7.83/2.57  #Define  : 0
% 7.83/2.57  #Split   : 28
% 7.83/2.57  #Chain   : 0
% 7.83/2.57  #Close   : 0
% 7.83/2.57  
% 7.83/2.57  Ordering : KBO
% 7.83/2.57  
% 7.83/2.57  Simplification rules
% 7.83/2.57  ----------------------
% 7.83/2.57  #Subsume      : 410
% 7.83/2.57  #Demod        : 2405
% 7.83/2.57  #Tautology    : 976
% 7.83/2.57  #SimpNegUnit  : 58
% 7.83/2.57  #BackRed      : 611
% 7.83/2.57  
% 7.83/2.57  #Partial instantiations: 375
% 7.83/2.57  #Strategies tried      : 1
% 7.83/2.57  
% 7.83/2.57  Timing (in seconds)
% 7.83/2.57  ----------------------
% 7.83/2.57  Preprocessing        : 0.33
% 7.83/2.57  Parsing              : 0.17
% 7.83/2.57  CNF conversion       : 0.02
% 7.83/2.57  Main loop            : 1.44
% 7.83/2.57  Inferencing          : 0.50
% 7.83/2.57  Reduction            : 0.46
% 7.83/2.57  Demodulation         : 0.32
% 7.83/2.57  BG Simplification    : 0.06
% 7.83/2.57  Subsumption          : 0.31
% 7.83/2.57  Abstraction          : 0.07
% 7.83/2.57  MUC search           : 0.00
% 7.83/2.57  Cooper               : 0.00
% 7.83/2.57  Total                : 1.83
% 7.83/2.57  Index Insertion      : 0.00
% 7.83/2.57  Index Deletion       : 0.00
% 7.83/2.57  Index Matching       : 0.00
% 7.83/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
